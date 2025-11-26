--
-- INFOB3CC Concurrency
-- Practical 1: IBAN calculator
--
-- http://ics.uu.nl/docs/vakken/b3cc/assessment.html
--
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

  forkThreads p (addToCounter globalCounter . (performMTests . divideWork))

  -- return the final value of the counter
  readIORef globalCounter

  where
    -- calculate the range for an individual thread based on its index (inclusive lower, exclusive upper range)
    divideWork :: Int -> (Int, Int)
    divideWork index
      | index < threadsWithExtraWork = (b + index * (threadWorkAmount + 1), b + (index + 1) * (threadWorkAmount + 1))
      | otherwise = (b + index * threadWorkAmount + threadsWithExtraWork, b + (index + 1) * threadWorkAmount + threadsWithExtraWork)
    -- how much work a single thread needs to do
    threadWorkAmount = (e - b) `div` p
    -- how much work isn't neatly divisible and up to which thread-index threads will compensate for this
    threadsWithExtraWork = (e - b) `mod` p

    -- the amount of values in a range that satisfy the mtest
    performMTests :: (Int, Int) -> Int
    performMTests (lowerThreadRange, upperThreadRange) = sum $ map (boolToInt . mtest m) [lowerThreadRange..upperThreadRange]
    boolToInt bool
      | bool = 1
      | otherwise = 0

    -- CAS loop that tries to add a value to the global counter
    addToCounter :: (IORef Int) -> Int -> IO()
    addToCounter counter addedValue = do




      
      oldValue <- readIORef counter
      let newValue = oldValue + addedValue

      ticket <- readForCAS counter
      -- TODO: update counter
      return () -- TODO: change to appropriate output value


-- -----------------------------------------------------------------------------
-- 2. List mode (3pt)
-- -----------------------------------------------------------------------------

list :: Handle -> Config -> IO ()
list handle config = do
  -- Implement list mode here!
  -- Remember to use "hPutStrLn handle" to write your output.
  undefined


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
