module Elfe.Verifier where

import Control.Applicative
import Control.Exception
import Control.Monad

import Elfe.Language
import Elfe.Prover

verify :: [Statement] -> IO [StatementStatus]
verify problem = verSeq problem (Context [] Empty)

verSeq :: [Statement] -> Context -> IO [StatementStatus]
verSeq [] _ = return []
verSeq (st:sts) (Context hs p) = do
  status <- verStat st (Context hs p)
  remaining <- verSeq sts (Context (hs ++ [st]) p)
  return $ status : remaining

verifySplit :: [Statement] -> Context -> IO [StatementStatus]
verifySplit [] _ = return []
verifySplit (c:cs) context = do
  status <- verStat c context
  remaining <- verifySplit cs context
  return $ status : remaining

verStat :: Statement -> Context -> IO StatementStatus
verStat (Statement id f Assumed pos) _context =
    return $ StatementStatus id f (Correct NotProven) [] pos
verStat (Statement id f ByContext pos) context = do
    status <- checkStat (Statement id f ByContext pos) context Nothing
    return $ StatementStatus id f status [] pos
verStat (Statement id f (BySubcontext ids) pos) context = do
    let analysis = analyzeByRules ids f context
    status <- checkStat (Statement id f ByContext pos) (restrictContext context ids) (Just analysis)
    return $ StatementStatus id f status [] pos
verStat (Statement id f (BySequence sequ) pos) context = do
    sequStatus <- verSeq sequ (Context [] context)
    return $ StatementStatus id f (foldStatus sequStatus) sequStatus pos
verStat (Statement id f (BySplit split) pos) context = do
    splitStatus <- verifySplit split context
    return $ StatementStatus id f (foldStatus splitStatus) splitStatus pos

-- | An optional pre-computed ProofAnalysis can be supplied (used when the
--   caller already knows the intended rule names before restricting context).
--   When Nothing, the analysis is derived from the context as given.
checkStat :: Statement -> Context -> Maybe ProofAnalysis -> IO ProofStatus
checkStat (Statement sid formula _ _) context maybeAnalysis = do
    let analysis = case maybeAnalysis of
                       Just a  -> a
                       Nothing -> analyzeProofAttempt formula context
    result <- prove (show context ++ "fof(" ++ sid ++ ", conjecture, (" ++ show formula ++ ")).\n")
    case result of
        Incorrect proverInfo ->
            return $ IncorrectWithExplanation proverInfo
                   $ generateErrorExplanation sid formula context analysis
        Unknown ->
            return $ IncorrectWithExplanation (ProverName "ATP" "timeout")
                   $ generateTimeoutExplanation sid formula context analysis
        Correct _ -> return result

-- ---------------------------------------------------------------------------
-- Proof analysis
-- ---------------------------------------------------------------------------

data ProofAnalysis = ProofAnalysis
  { analysisTarget    :: Formula
  , availableFormulas :: [Formula]
  , inferencePattern  :: Maybe InferencePattern
  , requiredFormulas  :: [Formula]
  , missingFormulas   :: [Formula]
  , intendedRule      :: Maybe String   -- rule name from "by <rule>" annotation
  } deriving (Show, Eq)

-- | Infer analysis purely from what is in context, without knowing which rule
--   was intended.  intendedRule is Nothing.
analyzeProofAttempt :: Formula -> Context -> ProofAnalysis
analyzeProofAttempt formula context =
    let available = extractFormulasFromContext context
        pat       = matchInferencePattern formula available
        required  = getRequiredPremises pat
        missing   = findMissingPremises required available
    in ProofAnalysis
        { analysisTarget    = formula
        , availableFormulas = available
        , inferencePattern  = pat
        , requiredFormulas  = required
        , missingFormulas   = missing
        , intendedRule      = Nothing
        }

-- | Analyse a proof attempt when the intended rule names are known (from the
--   "by <rule>" annotation preserved in BySubcontext).  Uses the full context
--   so missing premises are reported accurately even though the ATP only sees
--   the restricted context.
analyzeByRules :: [String] -> Formula -> Context -> ProofAnalysis
analyzeByRules []    formula context = analyzeProofAttempt formula context
analyzeByRules (r:_) formula context =
    let available             = extractFormulasFromContext context
        (pat, required, missing) = ruleAnalysis r formula available
    in ProofAnalysis
        { analysisTarget    = formula
        , availableFormulas = available
        , inferencePattern  = pat
        , requiredFormulas  = required
        , missingFormulas   = missing
        , intendedRule      = Just r
        }

-- | Map a single rule name + target formula to (pattern, required, missing).
ruleAnalysis :: String -> Formula -> [Formula]
            -> (Maybe InferencePattern, [Formula], [Formula])
ruleAnalysis rule formula available =
    case (rule, formula) of
        -- Transitivity: R(x,z) — find what half IS present, report the other half missing
        ("transitivity", Atom rel [Var x, Var z]) ->
            let fromX  = [t2 | Atom r [t1, t2] <- available, r == rel, t1 == Var x]
                toZ    = [t1 | Atom r [t1, t2] <- available, r == rel, t2 == Var z]
                -- Prefer a pivot that satisfies both halves; fall back to partial
                pivot  = case filter (`elem` toZ) fromX of
                            (y:_) -> y
                            []    -> case fromX of
                                        (y:_) -> y   -- have R(x,y), missing R(y,z)
                                        []    -> case toZ of
                                                    (y:_) -> y   -- have R(y,z), missing R(x,y)
                                                    []    -> Var "y"  -- have nothing
                pat     = Just (TransitivityPattern rel (Var x) pivot (Var z))
                required = [Atom rel [Var x, pivot], Atom rel [pivot, Var z]]
                missing  = findMissingPremises required available
            in (pat, required, missing)

        -- Symmetry: R(x,z) — need R(z,x)
        ("symmetry", Atom rel [Var x, Var z]) ->
            let pat      = Just (SymmetryPattern rel (Var x) (Var z))
                required = [Atom rel [Var z, Var x]]
                missing  = findMissingPremises required available
            in (pat, required, missing)

        -- Reflexivity: R(x,x) — no extra premises needed
        ("reflexivity", Atom rel [Var x1, Var x2]) | x1 == x2 ->
            (Just (ReflexivityPattern (Var x1)), [], [])

        -- Unknown or inapplicable rule: fall back to pattern inference
        _ ->
            let pat      = matchInferencePattern formula available
                required = getRequiredPremises pat
                missing  = findMissingPremises required available
            in (pat, required, missing)

-- ---------------------------------------------------------------------------
-- Pattern matching helpers
-- ---------------------------------------------------------------------------

extractFormulasFromContext :: Context -> [Formula]
extractFormulasFromContext Empty = []
extractFormulasFromContext (Context stmts parent) =
    map formula stmts ++ extractFormulasFromContext parent

-- | Match the formula against known inference patterns.
--   Reflexivity is checked first because its guard (x1 == x2) would otherwise
--   be shadowed by the general two-variable branch below it.
--   Modus ponens and conjunction elimination are tried last as catch-alls.
matchInferencePattern :: Formula -> [Formula] -> Maybe InferencePattern
matchInferencePattern target available =
    case target of
        Atom rel [Var x1, Var x2] | x1 == x2 ->
            Just (ReflexivityPattern (Var x1))
        Atom rel [Var x, Var z] ->
            case findTransitivityMiddle rel (Var x) (Var z) available of
                Just mid -> Just (TransitivityPattern rel (Var x) mid (Var z))
                Nothing  ->
                    if Atom rel [Var z, Var x] `elem` available
                    then Just (SymmetryPattern rel (Var x) (Var z))
                    else tryLogicalPatterns target available
        _ -> tryLogicalPatterns target available

-- | Try modus ponens (P→Q, P in context ⊢ Q) then conjunction elimination
--   (P∧Q in context ⊢ P or Q).  These apply to any formula shape.
tryLogicalPatterns :: Formula -> [Formula] -> Maybe InferencePattern
tryLogicalPatterns target available =
    case findModusPonens target available of
        Just pat -> Just pat
        Nothing  -> findConjunctionElim target available

-- | Find P→Q in context where Q matches target and P is also present.
findModusPonens :: Formula -> [Formula] -> Maybe InferencePattern
findModusPonens target available =
    let impls = [Impl p q | Impl p q <- available, q == target]
    in case impls of
        (impl@(Impl p _):_) | p `elem` available -> Just (ModusPonensPattern impl p)
        _                                              -> Nothing

-- | Find P∧Q in context where either P or Q matches target.
findConjunctionElim :: Formula -> [Formula] -> Maybe InferencePattern
findConjunctionElim target available =
    let conjs = [conj | conj@(And l r) <- available, l == target || r == target]
    in case conjs of
        (conj:_) -> Just (ConjunctionPattern conj)
        []       -> Nothing

-- | Scan available formulas to find a middle term y s.t. R(x,y) and R(y,z).
findTransitivityMiddle :: String -> Term -> Term -> [Formula] -> Maybe Term
findTransitivityMiddle rel x z available =
    let fromX = [t2 | Atom r [t1, t2] <- available, r == rel, t1 == x]
        toZ   = [t1 | Atom r [t1, t2] <- available, r == rel, t2 == z]
        hits  = filter (`elem` toZ) fromX
    in case hits of
        (mid:_) -> Just mid
        []      -> Nothing

getRequiredPremises :: Maybe InferencePattern -> [Formula]
getRequiredPremises Nothing    = []
getRequiredPremises (Just pat) = case pat of
    TransitivityPattern rel x y z -> [Atom rel [x, y], Atom rel [y, z]]
    SymmetryPattern rel x z       -> [Atom rel [z, x]]
    ReflexivityPattern _          -> []
    ModusPonensPattern impl prem  -> [impl, prem]
    ConjunctionPattern conj       -> [conj]
    _                             -> []

findMissingPremises :: [Formula] -> [Formula] -> [Formula]
findMissingPremises required available = filter (`notElem` available) required

-- ---------------------------------------------------------------------------
-- Explanation generation
-- ---------------------------------------------------------------------------

generateErrorExplanation :: String -> Formula -> Context -> ProofAnalysis -> ErrorExplanation
generateErrorExplanation stepId target context analysis =
    let missing  = missingFormulas analysis
        ruleStr  = case intendedRule analysis of
                       Just r  -> r
                       Nothing -> case inferencePattern analysis of
                                      Just pat -> show pat
                                      Nothing  -> "unknown inference"
        errType  = if null missing then UnknownError else MissingPremiseError missing
    in ErrorExplanation
        { failedStep        = parseStepId stepId
        , attemptedRule     = ruleStr
        , targetFormula     = target
        , requiredPremises  = requiredFormulas analysis
        , availablePremises = availableFormulas analysis
        , missingPremises   = missing
        , contextInfo       = context
        , errorType         = errType
        }

generateTimeoutExplanation :: String -> Formula -> Context -> ProofAnalysis -> ErrorExplanation
generateTimeoutExplanation stepId target context analysis =
    let ruleStr = case intendedRule analysis of
                      Just r  -> r
                      Nothing -> "unknown"
    in ErrorExplanation
        { failedStep        = parseStepId stepId
        , attemptedRule     = ruleStr
        , targetFormula     = target
        , requiredPremises  = requiredFormulas analysis
        , availablePremises = availableFormulas analysis
        , missingPremises   = missingFormulas analysis
        , contextInfo       = context
        , errorType         = ATPTimeoutError
        }

parseStepId :: String -> Int
parseStepId sid = case reads (drop (length idPrefix) sid) of
    [(n, "")] -> n
    _         -> 0

-- ---------------------------------------------------------------------------
-- ProofTrace construction
-- ---------------------------------------------------------------------------

-- | Build a flat ProofTrace from the status tree produced by verSeq.
buildTrace :: [StatementStatus] -> ProofTrace
buildTrace statuses = ProofTrace
    { traceSteps  = zipWith statementToStep [1..] (flattenStatuses statuses)
    , finalResult = foldStatus statuses
    }

-- | Depth-first flattening: parent before children.
flattenStatuses :: [StatementStatus] -> [StatementStatus]
flattenStatuses = go []
  where
    go acc []     = reverse acc
    go acc (s:ss) = go (s : acc) (children s ++ ss)

statementToStep :: Int -> StatementStatus -> TraceStep
statementToStep n (StatementStatus _ f st cs _) = TraceStep
    { stepNumber  = n
    , stepFormula = f
    , stepRule    = ruleFromStatus st
    , stepPremises = case st of
                         IncorrectWithExplanation _ expl -> availablePremises expl
                         _                               -> []
    , stepSuccess  = isCorrect st
    , stepError    = case st of
                         IncorrectWithExplanation _ expl -> Just expl
                         _                               -> Nothing
    }

ruleFromStatus :: ProofStatus -> String
ruleFromStatus (Correct (ProverName name _))     = name
ruleFromStatus (Correct NotProven)               = "assumed"
ruleFromStatus (IncorrectWithExplanation _ expl) = attemptedRule expl
ruleFromStatus (Incorrect _)                     = "failed"
ruleFromStatus Unknown                           = "unknown"

-- ---------------------------------------------------------------------------
-- Status helpers
-- ---------------------------------------------------------------------------

foldStatus :: [StatementStatus] -> ProofStatus
foldStatus [] = Correct NotProven
foldStatus ((StatementStatus _ _ s _ _):sts)
    | isCorrect s = foldStatus sts
    | otherwise   = s

isCorrect :: ProofStatus -> Bool
isCorrect (Correct _) = True
isCorrect _           = False
