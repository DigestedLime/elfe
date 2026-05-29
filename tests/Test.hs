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

-- ---------------------------------------------------------------------------
-- Tests
-- ---------------------------------------------------------------------------

testPatternMatching :: IO ()
testPatternMatching = do
    -- Reflexivity guard must fire before the general two-variable branch
    check "reflexivity detected for R(x,x)" $
        matchInferencePattern rxx [] == Just (ReflexivityPattern (Var "x"))

    -- Transitivity: middle term found in context
    check "transitivity with middle y present" $
        matchInferencePattern rxz [rxy, ryz]
            == Just (TransitivityPattern "R" (Var "x") (Var "y") (Var "z"))

    -- Transitivity: no match when context has only the left half
    check "no transitivity when only R(x,y) in context" $
        matchInferencePattern rxz [rxy] == Nothing

    -- Symmetry: reverse form present in context
    check "symmetry detected when R(z,x) in context" $
        matchInferencePattern rxz [rzx]
            == Just (SymmetryPattern "R" (Var "x") (Var "z"))

    -- Non-relational formula matches nothing
    check "Top has no inference pattern" $
        matchInferencePattern Top [] == Nothing

testPremiseTracking :: IO ()
testPremiseTracking = do
    let transPat = Just (TransitivityPattern "R" (Var "x") (Var "y") (Var "z"))
    let symPat   = Just (SymmetryPattern     "R" (Var "x") (Var "z"))
    let refPat   = Just (ReflexivityPattern (Var "x"))

    -- The relation name must appear in the required premises (was "temp" before fix)
    check "transitivity required premises carry relation name" $
        map show (getRequiredPremises transPat) == [show rxy, show ryz]

    -- Symmetry requires the reversed form
    check "symmetry required premise is R(z,x)" $
        map show (getRequiredPremises symPat) == [show rzx]

    -- Reflexivity needs no additional premises
    check "reflexivity has no required premises" $
        null (getRequiredPremises refPat)

    -- Nothing yields empty list
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

    -- Should not match on a different relation name
    check "Nothing when relation name differs" $
        findTransitivityMiddle "R" (Var "x") (Var "z")
            [Atom "S" [Var "x", Var "y"], Atom "S" [Var "y", Var "z"]]
            == Nothing

testFormatCoverage :: IO ()
testFormatCoverage = do
    -- Every ErrorType constructor must produce non-empty output
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

    -- MissingPremiseError should mention the attempted rule
    let explMissing = (dummyExpl (MissingPremiseError [])) { attemptedRule = "transitivity" }
    check "MissingPremiseError output contains rule name" $
        "transitivity" `isInfixOf` formatErrorExplanation explMissing

    -- ATPTimeoutError should mention timeout (case-insensitive)
    check "ATPTimeoutError output mentions timeout" $
        "timeout" `isInfixOf` map toLower (formatErrorExplanation (dummyExpl ATPTimeoutError))

    -- QuantifierScopeError should mention the variable name
    let explQS = dummyExpl (QuantifierScopeError "myVar" Top)
    check "QuantifierScopeError output contains variable name" $
        "myVar" `isInfixOf` formatErrorExplanation explQS

-- ---------------------------------------------------------------------------
-- analyzeProofAttempt integration tests
--
-- These test the full pipeline from a Formula + Context to ProofAnalysis.
-- NOTE: missingFormulas is always [] in normal flow because matchInferencePattern
-- only identifies transitivity when BOTH halves are already in context, so
-- findMissingPremises finds nothing absent. Tests below document that invariant
-- explicitly and verify the intermediate results are correct anyway.
-- ---------------------------------------------------------------------------

mkStmt :: String -> Formula -> Statement
mkStmt name f = Statement name f Assumed None

ctxFrom :: [Formula] -> Context
ctxFrom fs = Context (zipWith mkStmt (map show [1::Int ..]) fs) Empty

testAnalyzeProofAttempt :: IO ()
testAnalyzeProofAttempt = do
    -- Both halves present → transitivity matched, nothing missing
    let analysis1 = analyzeProofAttempt rxz (ctxFrom [rxy, ryz])
    check "transitivity pattern matched when both halves in context" $
        inferencePattern analysis1 == Just (TransitivityPattern "R" (Var "x") (Var "y") (Var "z"))
    check "missingFormulas empty when both halves present (design invariant)" $
        null (missingFormulas analysis1)
    check "both halves appear in requiredFormulas" $
        map show (requiredFormulas analysis1) == [show rxy, show ryz]

    -- Only left half present → no pattern (middle not found), nothing missing
    let analysis2 = analyzeProofAttempt rxz (ctxFrom [rxy])
    check "no pattern when only R(x,y) in context" $
        inferencePattern analysis2 == Nothing
    check "missingFormulas empty when pattern not found" $
        null (missingFormulas analysis2)

    -- Reversed form present → symmetry matched
    let analysis3 = analyzeProofAttempt rxz (ctxFrom [rzx])
    check "symmetry matched when R(z,x) in context" $
        inferencePattern analysis3 == Just (SymmetryPattern "R" (Var "x") (Var "z"))
    check "required premise for symmetry is R(z,x)" $
        map show (requiredFormulas analysis3) == [show rzx]

    -- Empty context → nothing matched
    let analysis4 = analyzeProofAttempt rxz (ctxFrom [])
    check "no pattern on empty context" $
        inferencePattern analysis4 == Nothing
    check "available formulas empty on empty context" $
        null (availableFormulas analysis4)

-- ---------------------------------------------------------------------------
-- generateErrorExplanation tests
--
-- generateErrorExplanation reads from a ProofAnalysis. We construct one
-- directly with non-empty missingFormulas to reach the MissingPremiseError
-- branch, which is unreachable via normal analyzeProofAttempt flow (see
-- comment above).
-- ---------------------------------------------------------------------------

mkAnalysis :: Formula -> [Formula] -> [Formula] -> [Formula] -> ProofAnalysis
mkAnalysis target available required missing = ProofAnalysis
    { analysisTarget    = target
    , availableFormulas = available
    , inferencePattern  = Nothing
    , requiredFormulas  = required
    , missingFormulas   = missing
    }

testGenerateExplanation :: IO ()
testGenerateExplanation = do
    -- Non-empty missingFormulas → MissingPremiseError
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

    -- Empty missingFormulas → UnknownError
    let analysis2 = mkAnalysis rxz [rxy, ryz] [rxy, ryz] []
    let expl2 = generateErrorExplanation "s3" rxz emptyCtx analysis2
    check "UnknownError produced when nothing is missing" $
        case errorType expl2 of
            UnknownError -> True
            _            -> False

-- ---------------------------------------------------------------------------
-- formatErrorExplanation content tests for MissingPremiseError
--
-- These verify that the formatted message actually names the missing formula.
-- Tests using dummyExpl (empty premise lists) already ran above; these use
-- real formula content.
-- ---------------------------------------------------------------------------

testFormatMissingPremises :: IO ()
testFormatMissingPremises = do
    -- Single missing premise should appear in the output
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

    -- Multiple missing premises: all should appear
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
    putStrLn "\n-- generateErrorExplanation --"
    testGenerateExplanation
    putStrLn "\n-- formatErrorExplanation with real missing premises --"
    testFormatMissingPremises
    putStrLn "\nAll tests passed."
