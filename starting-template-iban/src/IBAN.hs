--
-- INFOB3CC Concurrency
-- Practical 1: IBAN calculator
--
-- http://ics.uu.nl/docs/vakken/b3cc/assessment.html
--
{-# OPTIONS_GHC -Wno-unused-do-bind #-}
module IBAN (

  Mode(..), Config(..),
  count, list, search

) where

import Control.Concurrent
import Crypto.Hash.SHA1
import Data.Atomics                                       ( readForCAS, casIORef, peekTicket )
import Data.IORef
import Data.List                                          ( elemIndex )
import Data.Word
import Data.Maybe                                         ( fromJust )
import System.Environment
import System.IO
import Data.ByteString.Char8                              ( ByteString )
import qualified Data.ByteString                          as B
import qualified Data.ByteString.Char8                    as B8


-- -----------------------------------------------------------------------------
-- 0. m-test
-- -----------------------------------------------------------------------------

-- Perform the m-test on 'number'. Use `div` and `mod` to extract digits from
-- the number; do not use `show`, as it is too slow.
mtest :: Int -> Int -> Bool
mtest m number = (addDigits number 1) `mod` m == 0
  where
    -- add digits together multiplied by their positions
    addDigits :: Int -> Int -> Int
    addDigits numberChunk position
      | numberChunk == 0 = 0
      | otherwise = addDigits (numberChunk `div` 10) (position + 1) + (numberChunk `mod` 10) * position



-- -----------------------------------------------------------------------------
-- 1. Counting mode (3pt)
-- -----------------------------------------------------------------------------

count :: Config -> IO Int
count (Config b e m p) = do
  -- start counter at 0
  globalCounter <- newIORef 0

  forkThreads p (addToCounter globalCounter . (countThreadMTests . divideWork (Config b e m p)))

  -- return the final value of the counter
  readIORef globalCounter

  where
    -- the amount of values in a range that satisfy the mtest
    countThreadMTests :: (Int, Int) -> Int
    countThreadMTests (lowerThreadRange, upperThreadRange) = sum $ map (boolToInt . mtest m) [lowerThreadRange..upperThreadRange - 1]

    -- CAS loop that adds value to the global counter
    addToCounter :: IORef Int -> Int -> IO()
    addToCounter counter addedValue = do
      ticket <- readForCAS counter
      let newValue = peekTicket ticket + addedValue
      (success, _) <- casIORef counter ticket newValue
      -- If the swap is succesful, return, else try again
      if success then return ()
      else addToCounter counter addedValue


-- -----------------------------------------------------------------------------
-- 2. List mode (3pt)
-- -----------------------------------------------------------------------------

list :: Handle -> Config -> IO ()
list handle (Config b e m p) = do
  sequenceNumber <- newMVar 1

  forkThreads p (listThreadMTests sequenceNumber . divideWork (Config b e m p))

  where
    -- recursively go through all numbers in the range and print them if they satisfy the mtest
    listThreadMTests :: MVar Int -> (Int, Int) -> IO()
    listThreadMTests sequenceNumber (lowerThreadRange, upperThreadRange)
      | lowerThreadRange == upperThreadRange - 1 = printIfPassed sequenceNumber lowerThreadRange  -- stop recursion after reaching upper bound
      | otherwise = do
          printIfPassed sequenceNumber lowerThreadRange
          listThreadMTests sequenceNumber (lowerThreadRange + 1, upperThreadRange)
      
    -- Print a number and its sequencenumber if it passes the mtest
    printIfPassed :: MVar Int -> Int -> IO()
    printIfPassed sequenceNumber accountNumber 
      | mtest m accountNumber = do
          -- take the sequencenumber out of the mvar, print it with the accountnumber, increment it, and fill the mvar again
          currentSequenceNumber <- takeMVar sequenceNumber
          hPutStrLn handle (show currentSequenceNumber ++ show accountNumber)
          let newSequenceNumber = currentSequenceNumber + 1
          putMVar sequenceNumber newSequenceNumber
      | otherwise = return() -- if the mtest isn't passed, don't print anything



-- -----------------------------------------------------------------------------
-- 3. Search mode (4pt)
-- -----------------------------------------------------------------------------

search :: Config -> ByteString -> IO (Maybe Int)
search config query = do
  -- Implement search mode here!
  undefined


-- -----------------------------------------------------------------------------
-- Starting framework
-- -----------------------------------------------------------------------------

data Mode = Count | List | Search ByteString
  deriving Show

data Config = Config
  { cfgLower   :: !Int
  , cfgUpper   :: !Int
  , cfgModulus :: !Int
  , cfgThreads :: !Int
  }
  deriving Show

-- Evaluates a term, before continuing with the next IO operation.
--
evaluate :: a -> IO ()
evaluate x = x `seq` return ()

-- Forks 'n' threads. Waits until those threads have finished. Each thread
-- runs the supplied function given its thread ID in the range [0..n).
--
forkThreads :: Int -> (Int -> IO ()) -> IO ()
forkThreads n work = do
  -- Fork the threads and create a list of the MVars which
  -- per thread tell whether the work has finished.
  finishVars <- mapM work' [0 .. n - 1]
  -- Wait on all MVars
  mapM_ takeMVar finishVars
  where
    work' :: Int -> IO (MVar ())
    work' index = do
      var <- newEmptyMVar
      _   <- forkOn index (work index >> putMVar var ())
      return var

-- Checks whether 'value' has the expected hash.
--
checkHash :: ByteString -> String -> Bool
checkHash expected value = expected == hash (B8.pack value)

-- -----------------------------------------------------------------------------
-- Helper functions
-- -----------------------------------------------------------------------------

-- calculate the range for an individual thread based on its index (inclusive lower, exclusive upper range)
divideWork :: Config -> Int -> (Int, Int)
divideWork (Config b e _ p) index
  | index < threadsWithExtraWork = (b + index * (threadWorkAmount + 1), b + (index + 1) * (threadWorkAmount + 1))
  | otherwise = (b + index * threadWorkAmount + threadsWithExtraWork, b + (index + 1) * threadWorkAmount + threadsWithExtraWork)
  where
    -- how much work a single thread needs to do
    threadWorkAmount = (e - b) `div` p
    -- how much work isn't neatly divisible and up to which thread-index threads will compensate for this
    threadsWithExtraWork = (e - b) `mod` p

boolToInt :: Bool -> Int
boolToInt True = 1
boolToInt False = 0
