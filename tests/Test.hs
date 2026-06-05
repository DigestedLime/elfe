module Main where

import Data.Char (toLower)
import Data.List (isInfixOf)
import System.Exit (exitFailure)

import Elfe.Language
import Elfe.Verifier

-- ---------------------------------------------------------------------------
-- Minimal test framework
-- ---------------------------------------------------------------------------

check :: String -> Bool -> IO ()
check name True  = putStrLn $ "  PASS  " ++ name
check name False = do
    putStrLn $ "  FAIL  " ++ name
    exitFailure

checkEq :: (Show a, Eq a) => String -> a -> a -> IO ()
checkEq name expected got
    | expected == got = putStrLn $ "  PASS  " ++ name
    | otherwise = do
        putStrLn $ "  FAIL  " ++ name
        putStrLn $ "    expected: " ++ show expected
        putStrLn $ "    got:      " ++ show got
        exitFailure

-- ---------------------------------------------------------------------------
-- Shared fixtures
-- ---------------------------------------------------------------------------

rxy, ryz, rxz, rzx, rxx :: Formula
rxy = Atom "R" [Var "x", Var "y"]
ryz = Atom "R" [Var "y", Var "z"]
rxz = Atom "R" [Var "x", Var "z"]
rzx = Atom "R" [Var "z", Var "x"]
rxx = Atom "R" [Var "x", Var "x"]

emptyCtx :: Context
emptyCtx = Context [] Empty

dummyExpl :: ErrorType -> ErrorExplanation
dummyExpl et = ErrorExplanation
    { failedStep        = 1
    , attemptedRule     = "test"
    , targetFormula     = Top
    , requiredPremises  = []
    , availablePremises = []
    , missingPremises   = []
    , contextInfo       = emptyCtx
    , errorType         = et
    }

mkStmt :: String -> Formula -> Statement
mkStmt name f = Statement name f Assumed None

ctxFrom :: [Formula] -> Context
ctxFrom fs = Context (zipWith mkStmt (map show [1::Int ..]) fs) Empty

mkAnalysis :: Formula -> [Formula] -> [Formula] -> [Formula] -> ProofAnalysis
mkAnalysis target available required missing = ProofAnalysis
    { analysisTarget    = target
    , availableFormulas = available
    , inferencePattern  = Nothing
    , requiredFormulas  = required
    , missingFormulas   = missing
    , intendedRule      = Nothing
    }

-- ---------------------------------------------------------------------------
-- Tests
-- ---------------------------------------------------------------------------

testPatternMatching :: IO ()
testPatternMatching = do
    check "reflexivity detected for R(x,x)" $
        matchInferencePattern rxx [] == Just (ReflexivityPattern (Var "x"))

    check "transitivity with middle y present" $
        matchInferencePattern rxz [rxy, ryz]
            == Just (TransitivityPattern "R" (Var "x") (Var "y") (Var "z"))

    check "no transitivity when only R(x,y) in context" $
        matchInferencePattern rxz [rxy] == Nothing

    check "symmetry detected when R(z,x) in context" $
        matchInferencePattern rxz [rzx]
            == Just (SymmetryPattern "R" (Var "x") (Var "z"))

    check "Top has no inference pattern" $
        matchInferencePattern Top [] == Nothing

testPremiseTracking :: IO ()
testPremiseTracking = do
    let transPat = Just (TransitivityPattern "R" (Var "x") (Var "y") (Var "z"))
    let symPat   = Just (SymmetryPattern     "R" (Var "x") (Var "z"))
    let refPat   = Just (ReflexivityPattern (Var "x"))

    check "transitivity required premises carry relation name" $
        map show (getRequiredPremises transPat) == [show rxy, show ryz]

    check "symmetry required premise is R(z,x)" $
        map show (getRequiredPremises symPat) == [show rzx]

    check "reflexivity has no required premises" $
        null (getRequiredPremises refPat)

    check "no pattern yields empty required premises" $
        null (getRequiredPremises Nothing)

testTransitivityMiddle :: IO ()
testTransitivityMiddle = do
    check "finds y when R(x,y) and R(y,z) both present" $
        findTransitivityMiddle "R" (Var "x") (Var "z") [rxy, ryz]
            == Just (Var "y")

    check "Nothing when only R(x,y) present" $
        findTransitivityMiddle "R" (Var "x") (Var "z") [rxy] == Nothing

    check "Nothing when only R(y,z) present" $
        findTransitivityMiddle "R" (Var "x") (Var "z") [ryz] == Nothing

    check "Nothing on empty context" $
        findTransitivityMiddle "R" (Var "x") (Var "z") [] == Nothing

    check "Nothing when relation name differs" $
        findTransitivityMiddle "R" (Var "x") (Var "z")
            [Atom "S" [Var "x", Var "y"], Atom "S" [Var "y", Var "z"]]
            == Nothing

testFormatCoverage :: IO ()
testFormatCoverage = do
    check "MissingPremiseError formats non-empty" $
        not (null (formatErrorExplanation (dummyExpl (MissingPremiseError []))))

    check "ATPTimeoutError formats non-empty" $
        not (null (formatErrorExplanation (dummyExpl ATPTimeoutError)))

    check "ATPContradictionError formats non-empty" $
        not (null (formatErrorExplanation (dummyExpl (ATPContradictionError []))))

    check "InvalidInferenceError formats non-empty" $
        not (null (formatErrorExplanation (dummyExpl (InvalidInferenceError "mp" []))))

    check "QuantifierScopeError formats non-empty" $
        not (null (formatErrorExplanation (dummyExpl (QuantifierScopeError "x" Top))))

    check "VariableCaptureError formats non-empty" $
        not (null (formatErrorExplanation (dummyExpl (VariableCaptureError "x" Top))))

    check "UnknownError formats non-empty" $
        not (null (formatErrorExplanation (dummyExpl UnknownError)))

    let explMissing = (dummyExpl (MissingPremiseError [])) { attemptedRule = "transitivity" }
    check "MissingPremiseError output contains rule name" $
        "transitivity" `isInfixOf` formatErrorExplanation explMissing

    check "ATPTimeoutError output mentions timeout" $
        "timeout" `isInfixOf` map toLower (formatErrorExplanation (dummyExpl ATPTimeoutError))

    let explQS = dummyExpl (QuantifierScopeError "myVar" Top)
    check "QuantifierScopeError output contains variable name" $
        "myVar" `isInfixOf` formatErrorExplanation explQS

-- ---------------------------------------------------------------------------
-- analyzeProofAttempt integration
-- ---------------------------------------------------------------------------

testAnalyzeProofAttempt :: IO ()
testAnalyzeProofAttempt = do
    let analysis1 = analyzeProofAttempt rxz (ctxFrom [rxy, ryz])
    check "transitivity pattern matched when both halves in context" $
        inferencePattern analysis1 == Just (TransitivityPattern "R" (Var "x") (Var "y") (Var "z"))
    check "missingFormulas empty when both halves present (design invariant)" $
        null (missingFormulas analysis1)
    check "both halves appear in requiredFormulas" $
        map show (requiredFormulas analysis1) == [show rxy, show ryz]
    check "intendedRule is Nothing for analyzeProofAttempt" $
        intendedRule analysis1 == Nothing

    let analysis2 = analyzeProofAttempt rxz (ctxFrom [rxy])
    check "no pattern when only R(x,y) in context" $
        inferencePattern analysis2 == Nothing
    check "missingFormulas empty when pattern not found" $
        null (missingFormulas analysis2)

    let analysis3 = analyzeProofAttempt rxz (ctxFrom [rzx])
    check "symmetry matched when R(z,x) in context" $
        inferencePattern analysis3 == Just (SymmetryPattern "R" (Var "x") (Var "z"))
    check "required premise for symmetry is R(z,x)" $
        map show (requiredFormulas analysis3) == [show rzx]

    let analysis4 = analyzeProofAttempt rxz (ctxFrom [])
    check "no pattern on empty context" $
        inferencePattern analysis4 == Nothing
    check "available formulas empty on empty context" $
        null (availableFormulas analysis4)

-- ---------------------------------------------------------------------------
-- analyzeByRules — the core fix: uses rule names to find missing premises
-- even when the middle term is absent from context.
-- ---------------------------------------------------------------------------

testAnalyzeByRules :: IO ()
testAnalyzeByRules = do
    -- Transitivity with only left half: R(y,z) should be identified as missing
    let a1 = analyzeByRules ["transitivity"] rxz (ctxFrom [rxy])
    check "transitivity rule sets intendedRule" $
        intendedRule a1 == Just "transitivity"
    check "transitivity pattern set even with only left half" $
        case inferencePattern a1 of
            Just (TransitivityPattern _ _ _ _) -> True
            _                                  -> False
    check "R(y,z) identified as missing when only R(x,y) present" $
        any (\f -> show f == show ryz) (missingFormulas a1)

    -- Transitivity with only right half: R(x,y) should be missing
    let a2 = analyzeByRules ["transitivity"] rxz (ctxFrom [ryz])
    check "R(x,y) identified as missing when only R(y,z) present" $
        any (\f -> show f == show rxy) (missingFormulas a2)

    -- Transitivity with both halves: nothing missing
    let a3 = analyzeByRules ["transitivity"] rxz (ctxFrom [rxy, ryz])
    check "nothing missing when both transitivity halves present" $
        null (missingFormulas a3)

    -- Transitivity with empty context: uses placeholder pivot Var "y"
    let a4 = analyzeByRules ["transitivity"] rxz (ctxFrom [])
    check "both R(x,y) and R(y,z) missing when context empty" $
        length (missingFormulas a4) == 2

    -- Symmetry with no reversed form: R(z,x) should be missing
    let a5 = analyzeByRules ["symmetry"] rxz (ctxFrom [])
    check "symmetry rule sets intendedRule" $
        intendedRule a5 == Just "symmetry"
    check "R(z,x) identified as missing for symmetry" $
        any (\f -> show f == show rzx) (missingFormulas a5)

    -- Symmetry with reversed form present: nothing missing
    let a6 = analyzeByRules ["symmetry"] rxz (ctxFrom [rzx])
    check "nothing missing for symmetry when R(z,x) present" $
        null (missingFormulas a6)

    -- Unknown rule: falls back to analyzeProofAttempt behaviour
    let a7 = analyzeByRules ["unknownRule"] rxz (ctxFrom [])
    check "unknown rule still sets intendedRule" $
        intendedRule a7 == Just "unknownRule"
    check "unknown rule with empty context finds no pattern" $
        inferencePattern a7 == Nothing

    -- Empty rule list: same as analyzeProofAttempt
    let a8 = analyzeByRules [] rxz (ctxFrom [rxy, ryz])
    check "empty rule list falls back to pattern inference" $
        inferencePattern a8 == Just (TransitivityPattern "R" (Var "x") (Var "y") (Var "z"))

-- ---------------------------------------------------------------------------
-- generateErrorExplanation
-- ---------------------------------------------------------------------------

testGenerateExplanation :: IO ()
testGenerateExplanation = do
    let analysis = mkAnalysis rxz [rxy] [rxy, ryz] [ryz]
    let expl = generateErrorExplanation "s5" rxz emptyCtx analysis
    check "failedStep parsed from id" $
        failedStep expl == 5
    check "missingPremises in explanation matches analysis" $
        map show (missingPremises expl) == [show ryz]
    check "MissingPremiseError produced when missing is non-empty" $
        case errorType expl of
            MissingPremiseError _ -> True
            _                     -> False

    let analysis2 = mkAnalysis rxz [rxy, ryz] [rxy, ryz] []
    let expl2 = generateErrorExplanation "s3" rxz emptyCtx analysis2
    check "UnknownError produced when nothing is missing" $
        case errorType expl2 of
            UnknownError -> True
            _            -> False

    -- intendedRule is used as attemptedRule when present
    let analysisWithRule = (mkAnalysis rxz [rxy] [rxy, ryz] [ryz])
                               { intendedRule = Just "transitivity" }
    let explWithRule = generateErrorExplanation "s7" rxz emptyCtx analysisWithRule
    check "intendedRule used as attemptedRule in explanation" $
        attemptedRule explWithRule == "transitivity"

-- ---------------------------------------------------------------------------
-- formatErrorExplanation with real missing premises
-- ---------------------------------------------------------------------------

testFormatMissingPremises :: IO ()
testFormatMissingPremises = do
    let expl = ErrorExplanation
          { failedStep        = 4
          , attemptedRule     = "transitivity"
          , targetFormula     = rxz
          , requiredPremises  = [rxy, ryz]
          , availablePremises = [rxy]
          , missingPremises   = [ryz]
          , contextInfo       = emptyCtx
          , errorType         = MissingPremiseError [ryz]
          }
    let out = formatErrorExplanation expl
    check "step number appears in output" $
        "4" `isInfixOf` out
    check "attempted rule appears in output" $
        "transitivity" `isInfixOf` out
    check "missing formula name appears in output" $
        show ryz `isInfixOf` out
    check "Missing section present" $
        "Missing" `isInfixOf` out

    let expl2 = expl
          { missingPremises = [rxy, ryz]
          , errorType       = MissingPremiseError [rxy, ryz]
          }
    let out2 = formatErrorExplanation expl2
    check "first missing formula appears when two are missing" $
        show rxy `isInfixOf` out2
    check "second missing formula appears when two are missing" $
        show ryz `isInfixOf` out2

-- ---------------------------------------------------------------------------
-- Modus ponens and conjunction elimination patterns
-- ---------------------------------------------------------------------------

pq, p, q :: Formula
p  = Atom "P" []
q  = Atom "Q" []
pq = Impl p q       -- P → Q

testLogicalPatterns :: IO ()
testLogicalPatterns = do
    -- Modus ponens: P→Q and P both in context, target Q
    check "modus ponens detected when P→Q and P both present" $
        case matchInferencePattern q [pq, p] of
            Just (ModusPonensPattern _ _) -> True
            _                             -> False

    -- Required premises for modus ponens
    check "modus ponens requires both implication and premise" $
        case matchInferencePattern q [pq, p] of
            Just pat -> length (getRequiredPremises (Just pat)) == 2
            _        -> False

    -- No modus ponens when P is missing from context
    check "no modus ponens when premise P is absent" $
        case matchInferencePattern q [pq] of
            Just (ModusPonensPattern _ _) -> False
            _                             -> True

    -- Conjunction elimination: P∧Q in context, target P
    let conj = And p q
    check "conjunction elim detected when P∧Q in context, target P" $
        case matchInferencePattern p [conj] of
            Just (ConjunctionPattern _) -> True
            _                           -> False

    -- Conjunction elimination: P∧Q in context, target Q
    check "conjunction elim detected when P∧Q in context, target Q" $
        case matchInferencePattern q [conj] of
            Just (ConjunctionPattern _) -> True
            _                           -> False

    -- Required premise for conjunction is the And formula itself
    check "conjunction elim requires the conjunction formula" $
        case matchInferencePattern p [conj] of
            Just pat -> map show (getRequiredPremises (Just pat)) == [show conj]
            _        -> False

    -- No pattern when neither applies
    check "no logical pattern when context is unrelated" $
        matchInferencePattern q [p] == Nothing

-- ---------------------------------------------------------------------------
-- Entry point
-- ---------------------------------------------------------------------------

main :: IO ()
main = do
    putStrLn "=== Elfe Error Explanation Tests ==="
    putStrLn "\n-- Pattern Matching --"
    testPatternMatching
    putStrLn "\n-- Premise Tracking --"
    testPremiseTracking
    putStrLn "\n-- Transitivity Middle Search --"
    testTransitivityMiddle
    putStrLn "\n-- Format Coverage --"
    testFormatCoverage
    putStrLn "\n-- analyzeProofAttempt Integration --"
    testAnalyzeProofAttempt
    putStrLn "\n-- analyzeByRules (rule-aware analysis) --"
    testAnalyzeByRules
    putStrLn "\n-- generateErrorExplanation --"
    testGenerateExplanation
    putStrLn "\n-- formatErrorExplanation with real missing premises --"
    testFormatMissingPremises
    putStrLn "\n-- Logical Patterns (modus ponens, conjunction elim) --"
    testLogicalPatterns
    putStrLn "\nAll tests passed."
