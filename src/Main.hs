import System.Environment (getArgs)
import Criterion.Measurement (getTime, secs)

import Elfe

main :: IO ()
main = do
  args <- getArgs
  case args of
    []               -> check False =<< getContents
    ["--trace"]      -> check True  =<< getContents
    [arg]            -> check False =<< readFile arg
    ["--trace", f]   -> check True  =<< readFile f
    [f, "--trace"]   -> check True  =<< readFile f
    _                -> error "usage: elfe [--trace] [file]"

check :: Bool -> String -> IO ()
check traceMode raw = do
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
    if traceMode
        then do
            putStrLn "--------------------------TRACE----------------------------"
            putStr $ formatTrace (buildTrace res)
        else return ()
    putStrLn "-------------------------STATISTICS------------------------"
    putStrLn $ "Parsing time: "   ++ secs (endParsing   - startParsing)
    putStrLn $ "Verifying time: " ++ secs (endVerifying - startVerifying)
    putStrLn $ "Total: "          ++ secs (endParsing   - startParsing + endVerifying - startVerifying)


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
collectExplainedFailures (s@(StatementStatus _ _ (IncorrectWithExplanation _ _) cs _ _):rest) =
    let childFailures = collectExplainedFailures cs
    in if null childFailures
       then s : collectExplainedFailures rest
       else childFailures ++ collectExplainedFailures rest
collectExplainedFailures (StatementStatus _ _ _ cs _ _:rest) =
    collectExplainedFailures cs ++ collectExplainedFailures rest

collectPlainFailures :: [StatementStatus] -> [StatementStatus]
collectPlainFailures [] = []
collectPlainFailures (s@(StatementStatus _ _ (Incorrect _) cs _ _):rest) =
    let childFailures = collectPlainFailures cs
    in if null childFailures
       then s : collectPlainFailures rest
       else childFailures ++ collectPlainFailures rest
collectPlainFailures (StatementStatus _ _ _ cs _ _:rest) =
    collectPlainFailures cs ++ collectPlainFailures rest

printExplained :: StatementStatus -> IO ()
printExplained (StatementStatus sid _ (IncorrectWithExplanation _ expl) _ _ _) = do
    putStrLn $ "--- " ++ sid ++ " ---"
    putStrLn $ formatErrorExplanation expl
    putStrLn ""
printExplained _ = return ()

printPlain :: StatementStatus -> IO ()
printPlain (StatementStatus sid f (Incorrect _) _ _ _) =
    putStrLn $ "--- " ++ sid ++ " failed: " ++ show f
printPlain _ = return ()
