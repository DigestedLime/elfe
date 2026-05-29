import System.Environment (getArgs)
import Criterion.Measurement (getTime, secs)

import Elfe

main :: IO ()
main = do
  args <- getArgs
  case args of
    []    -> do raw <- getContents
                check raw
    [arg] -> do raw <- readFile arg
                check raw 
    _ -> error "too many arguments - just give the file"

check :: String -> IO ()
check raw = do
    putStrLn "\n--------------------------PARSING--------------------------"
    startParsing <- getTime
    let included = includeLibraries raw
    sequ <- parseString included
    endParsing <- getTime
    putStrLn $ concat $ map (prettyStatement 0) sequ
    putStrLn "-------------------------VERIFYING--------------------------" 
    startVerifying <- getTime
    res <- verify sequ
    endVerifying <- getTime
    putStrLn "---------------------------RESULT--------------------------" 
    printRes res
    putStrLn "-------------------------STATISTICS------------------------" 
    putStrLn $ "Parsing time: " ++ (secs $ endParsing - startParsing)
    putStrLn $ "Verifying time: " ++ (secs $ endVerifying - startVerifying)
    putStrLn $ "Total: " ++ (secs $ endParsing - startParsing + endVerifying - startVerifying)


printRes :: [StatementStatus] -> IO ()
printRes ss = do
    let explained = collectExplainedFailures ss
        plain     = collectPlainFailures ss
        unknown   = filterSs ss Unknown
        nFailed   = length explained + length plain
        nUnknown  = length unknown
    if nFailed == 0 && nUnknown == 0
        then putStrLn "Everything correct"
        else do
            putStrLn $ "Proof failed: " ++ show nFailed ++ " error(s), " ++ show nUnknown ++ " unknown"
            putStrLn ""
            mapM_ printExplained explained
            mapM_ printPlain     plain

collectExplainedFailures :: [StatementStatus] -> [StatementStatus]
collectExplainedFailures [] = []
collectExplainedFailures (s@(StatementStatus _ _ (IncorrectWithExplanation _ _) cs _):rest) =
    s : collectExplainedFailures cs ++ collectExplainedFailures rest
collectExplainedFailures (StatementStatus _ _ _ cs _:rest) =
    collectExplainedFailures cs ++ collectExplainedFailures rest

collectPlainFailures :: [StatementStatus] -> [StatementStatus]
collectPlainFailures [] = []
collectPlainFailures (s@(StatementStatus _ _ (Incorrect _) cs _):rest) =
    s : collectPlainFailures cs ++ collectPlainFailures rest
collectPlainFailures (StatementStatus _ _ _ cs _:rest) =
    collectPlainFailures cs ++ collectPlainFailures rest

printExplained :: StatementStatus -> IO ()
printExplained (StatementStatus sid _ (IncorrectWithExplanation _ expl) _ _) = do
    putStrLn $ "--- " ++ sid ++ " ---"
    putStrLn $ formatErrorExplanation expl
    putStrLn ""
printExplained _ = return ()

printPlain :: StatementStatus -> IO ()
printPlain (StatementStatus sid f (Incorrect _) _ _) =
    putStrLn $ "--- " ++ sid ++ " failed: " ++ show f
printPlain _ = return ()
