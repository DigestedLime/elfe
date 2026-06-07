module Elfe.Prover where

import Data.IORef
import Data.List
--import Data.String.Utils (replace)
import System.Process
import System.Exit
import System.IO
import System.IO.Error
import System.Directory (removeFile)
import System.Random
import Control.Concurrent
import Control.Concurrent.Chan
import Control.Exception (SomeException, catch, IOException)
import Control.Monad

import Elfe.Language
import Settings (provers, countermodler, atpTimeout)

fileGenerator :: IO String
fileGenerator = do
  g <- newStdGen
  let rnd = take 12 $ randomRs ('a','z') g
  return $ rnd ++ ".tptp"

prove :: String -> IO ProofStatus
prove task = do
    tptpFile <- fileGenerator
    writeFile tptpFile task
    done <- newEmptyMVar
    chan <- newChan
    handles <- newIORef []
    pThreads <- mapM (\p -> forkIO $ runProver handles chan task p done tptpFile) provers
    cThreads <- mapM (\p -> forkIO $ runCountermodler handles chan task p done tptpFile) countermodler
    timeoutThread <- forkIO $ timeout task chan done
    readMVar done
    result <- readChan chan
    mapM killThread ([timeoutThread] ++ pThreads ++ cThreads)
    hs <- readIORef handles
    mapM_ terminateAndReap hs
    removeFile tptpFile
    return result

-- | Terminate an OS subprocess and reap it. Errors are swallowed because the
--   process may have already exited by the time cleanup runs.
terminateAndReap :: ProcessHandle -> IO ()
terminateAndReap ph = do
    let swallow :: IOException -> IO ()
        swallow _ = return ()
    terminateProcess ph `catch` swallow
    void (waitForProcess ph) `catch` swallow

runProver :: IORef [ProcessHandle] -> Chan ProofStatus -> String -> Prover -> MVar Bool -> String -> IO ()
runProver handles chan task (Prover name command args provedMsg disprovedMsg unknownMsg) done tptpFile = do
    (wh, rh, eh, ph) <- runInteractiveProcess command (tptpFile:args) Nothing Nothing
    atomicModifyIORef' handles (\hs -> (ph:hs, ()))
    hPutStrLn wh task ; hClose wh
    ofl <- hGetContents rh
    let lns = filter (not . null) $ lines ofl
    let pos = any (\l -> any (`isPrefixOf` l) provedMsg) lns
        neg = any (\l -> any (`isPrefixOf` l) disprovedMsg) lns
        unk = any (\l -> any (`isPrefixOf` l) unknownMsg) lns
    hClose eh
    when pos (writeChan chan (Correct (ProverName name "")) >> putMVar done True)

runCountermodler :: IORef [ProcessHandle] -> Chan ProofStatus -> String -> Countermodler -> MVar Bool -> String -> IO ()
runCountermodler handles chan task (Countermodler name command args clauseMarker) done tptpFile = do
    (wh, rh, eh, ph) <- runInteractiveProcess command (tptpFile:args) Nothing Nothing
    atomicModifyIORef' handles (\hs -> (ph:hs, ()))
    hPutStrLn wh task ; hClose wh
    ofl <- hGetContents rh
    let startMarker = elemIndex clauseMarker $ lines ofl
    case startMarker of
      Nothing -> return ()
      Just start -> do
        let contermodel = retrieveClauses $ drop (start+1) $ lines ofl
        writeChan chan (Incorrect (ProverName name contermodel)) >> putMVar done True


retrieveClauses :: [String] -> String
retrieveClauses [] = []
retrieveClauses (s:rs) = if s == ""
                            then ""
                            else cleaned ++ retrieveClauses rs
                              where cleaned = if s `strcontains` ", c" || s `strcontains` "(c"
                                                then s -- replace "(c" "(" (replace ", c" ", " s) ++ "\n" 
                                                else []


timeout :: String -> Chan ProofStatus -> MVar Bool -> IO ()
timeout task chan done = do
  threadDelay $ atpTimeout*1000000
  writeChan chan Unknown >> putMVar done True
  
