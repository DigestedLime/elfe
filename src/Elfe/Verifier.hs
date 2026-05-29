module Elfe.Verifier where

import Control.Applicative                                   
import Control.Exception
import Control.Monad                                   

import Debug.Trace

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
verStat (Statement id f Assumed pos) context = do
    traceM ("Assume " ++ id ++ ": " ++ show f)
    return $ StatementStatus id f (Correct (NotProven)) [] pos
verStat (Statement id f ByContext pos) context = do
    traceM ("Prove  " ++ id ++ ": " ++ show f)
    status <- checkStat (Statement id f ByContext pos) context
    return $ StatementStatus id f status [] pos
verStat (Statement id f (BySubcontext ids) pos) context = do
    traceM ("Prove  " ++ id ++ ": " ++ show f ++ " by " ++ concat ids)
    status <- checkStat (Statement id f ByContext pos) $ restrictContext context ids
    return $ StatementStatus id f status [] pos
verStat (Statement id f (BySequence sequ) pos) context = do
    traceM ("Check  " ++ id ++ ": " ++ show f)
    sequStatus <- verSeq sequ (Context [] context) 
    return $ StatementStatus id f (foldStatus sequStatus) sequStatus pos
verStat (Statement id f (BySplit split) pos) context = do
    traceM ("Split  " ++ id ++ ": " ++ show f) 
    splitStatus <- verifySplit split context 
    return $ StatementStatus id f (foldStatus splitStatus) splitStatus pos

checkStat :: Statement -> Context -> IO ProofStatus
checkStat statement@(Statement id formula p _) context = do
    -- Try to analyze the proof attempt before calling ATP
    let analysis = analyzeProofAttempt formula context
    traceM ("Analyzing proof attempt for " ++ id ++ ": " ++ show formula)
    
    -- Call ATP as before
    result <- prove (show context ++ "fof(" ++ id ++ ", conjecture, (" ++ show formula ++ ")).\n")
    
    -- If ATP failed, enhance with our analysis
    case result of
        Incorrect proverInfo -> do
            traceM ("ATP failed for " ++ id ++ ", generating error explanation")
            let explanation = generateErrorExplanation id formula context analysis
            traceM ("Error explanation:\n" ++ formatErrorExplanation explanation)
            return $ IncorrectWithExplanation proverInfo explanation
        Unknown -> do
            traceM ("ATP timeout for " ++ id ++ ", generating error explanation")
            let explanation = generateTimeoutExplanation id formula context analysis
            traceM ("Error explanation:\n" ++ formatErrorExplanation explanation)
            return $ IncorrectWithExplanation (ProverName "ATP" "timeout") explanation
        Correct proverInfo -> do
            traceM ("ATP succeeded for " ++ id)
            return result

-- Analyze what the proof is attempting and what premises might be needed
analyzeProofAttempt :: Formula -> Context -> ProofAnalysis
analyzeProofAttempt formula context = 
    let availableFormulas = extractFormulasFromContext context
        targetPattern = matchInferencePattern formula availableFormulas
        requiredFormulas = getRequiredPremises targetPattern
        missingFormulas = findMissingPremises requiredFormulas availableFormulas
    in ProofAnalysis {
        analysisTarget = formula,
        availableFormulas = availableFormulas,
        inferencePattern = targetPattern,
        requiredFormulas = requiredFormulas,
        missingFormulas = missingFormulas
    }

data ProofAnalysis = ProofAnalysis
  { analysisTarget :: Formula
  , availableFormulas :: [Formula]
  , inferencePattern :: Maybe InferencePattern
  , requiredFormulas :: [Formula]
  , missingFormulas :: [Formula]
  } deriving (Show, Eq)

-- Formula Eq is defined as always-True, so structural checks must use show.
formulaElem :: Formula -> [Formula] -> Bool
formulaElem f = any (\g -> show f == show g)

-- Extract formulas from context for analysis
extractFormulasFromContext :: Context -> [Formula]
extractFormulasFromContext Empty = []
extractFormulasFromContext (Context statements parent) =
    map formula statements ++ extractFormulasFromContext parent

-- Match the formula against known inference patterns.
-- Reflexivity is checked first because its guard (x1 == x2) would otherwise
-- be shadowed by the catch-all two-variable branch below it.
matchInferencePattern :: Formula -> [Formula] -> Maybe InferencePattern
matchInferencePattern target available =
    case target of
        -- Reflexivity: R(x,x) — equal variable on both sides
        Atom rel [Var x1, Var x2] | x1 == x2 ->
            Just (ReflexivityPattern (Var x1))
        -- Two distinct-variable atom: try transitivity first, then symmetry
        Atom rel [Var x, Var z] ->
            case findTransitivityMiddle rel (Var x) (Var z) available of
                Just mid -> Just (TransitivityPattern rel (Var x) mid (Var z))
                Nothing  ->
                    if formulaElem (Atom rel [Var z, Var x]) available
                    then Just (SymmetryPattern rel (Var x) (Var z))
                    else Nothing
        _ -> Nothing

-- Scan available formulas to find a real middle term y such that
-- R(x,y) and R(y,z) are both present.
findTransitivityMiddle :: String -> Term -> Term -> [Formula] -> Maybe Term
findTransitivityMiddle rel x z available =
    let fromX = [t2 | Atom r [t1, t2] <- available, r == rel, t1 == x]
        toZ   = [t1 | Atom r [t1, t2] <- available, r == rel, t2 == z]
        hits  = filter (`elem` toZ) fromX
    in case hits of
        (mid:_) -> Just mid
        []      -> Nothing

-- Get required premises based on the inference pattern.
-- Now uses the relation name stored in the pattern, so premises are accurate.
getRequiredPremises :: Maybe InferencePattern -> [Formula]
getRequiredPremises Nothing = []
getRequiredPremises (Just pat) = case pat of
    TransitivityPattern rel x y z -> [Atom rel [x, y], Atom rel [y, z]]
    SymmetryPattern rel x z       -> [Atom rel [z, x]]
    ReflexivityPattern _          -> []
    _                             -> []

-- Find which required premises are missing from available context.
-- Uses show-based comparison because Formula Eq is always True.
findMissingPremises :: [Formula] -> [Formula] -> [Formula]
findMissingPremises required available =
    filter (\f -> not (formulaElem f available)) required

-- Generate error explanation based on analysis
generateErrorExplanation :: String -> Formula -> Context -> ProofAnalysis -> ErrorExplanation
generateErrorExplanation stepId target context analysis =
    let missing = missingFormulas analysis
        patternStr = case inferencePattern analysis of
            Just pattern -> show pattern
            Nothing -> "unknown inference"
        errorType = if null missing 
                   then UnknownError
                   else MissingPremiseError missing
    in ErrorExplanation {
        failedStep = case reads (drop (length idPrefix) stepId) of
                         [(n, "")] -> n
                         _         -> 0,
        attemptedRule = patternStr,
        targetFormula = target,
        requiredPremises = requiredFormulas analysis,
        availablePremises = availableFormulas analysis,
        missingPremises = missing,
        contextInfo = context,
        errorType = errorType
    }

-- Generate timeout explanation
generateTimeoutExplanation :: String -> Formula -> Context -> ProofAnalysis -> ErrorExplanation  
generateTimeoutExplanation stepId target context analysis =
    ErrorExplanation {
        failedStep = case reads (drop (length idPrefix) stepId) of
                         [(n, "")] -> n
                         _         -> 0,
        attemptedRule = "ATP timeout",
        targetFormula = target,
        requiredPremises = requiredFormulas analysis,
        availablePremises = availableFormulas analysis,
        missingPremises = missingFormulas analysis,
        contextInfo = context,
        errorType = ATPTimeoutError
    } 

foldStatus :: [StatementStatus] -> ProofStatus
foldStatus [] = Correct NotProven
foldStatus ((StatementStatus _ _ s _ _):sts) = if isCorrect s
                        then foldStatus sts
                        else Incorrect NotProven

isCorrect :: ProofStatus -> Bool
isCorrect (Correct _) = True
isCorrect _ = False