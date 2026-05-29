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
    putStrLn "\nAll tests passed."
