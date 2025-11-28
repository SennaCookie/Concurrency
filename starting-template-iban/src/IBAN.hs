--
-- INFOB3CC Concurrency
-- Practical 1: IBAN calculator
--
-- http://ics.uu.nl/docs/vakken/b3cc/assessment.html
--
{-# OPTIONS_GHC -Wno-unused-do-bind #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant if" #-}
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
mtest m number = addDigits number 1 `mod` m == 0
  where
    -- add digits together multiplied by their positions
    addDigits :: Int -> Int -> Int
    addDigits numberChunk position
      | numberChunk == 0 = 0
      | otherwise = addDigits (numberChunk `div` 10) (position + 1) + numberChunk `mod` 10 * position



-- -----------------------------------------------------------------------------
-- 1. Counting mode (3pt)
-- -----------------------------------------------------------------------------

count :: Config -> IO Int
count (Config b e m p) = do
  -- start counter at 0
  globalCounter <- newIORef 0

  forkThreads p (casAdd globalCounter . countThreadMTests . divideWork (Config b e m p))

  -- return the final value of the counter
  readIORef globalCounter

  where
    -- the amount of values in a range that satisfy the mtest
    countThreadMTests :: (Int, Int) -> Int
    countThreadMTests (lowerThreadRange, upperThreadRange) = sum $ map (boolToInt . mtest m) [lowerThreadRange..upperThreadRange - 1]


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
      | lowerThreadRange == upperThreadRange = return ()  -- stop recursion after reaching upper bound
      | otherwise = do
          printIfPassed sequenceNumber lowerThreadRange
          listThreadMTests sequenceNumber (lowerThreadRange + 1, upperThreadRange)

    -- Print a number and its sequencenumber if it passes the mtest
    printIfPassed :: MVar Int -> Int -> IO()
    printIfPassed sequenceNumber accountNumber
      | mtest m accountNumber = do
          -- take the sequencenumber out of the mvar, print it with the accountnumber, increment it, and fill the mvar again
          currentSequenceNumber <- takeMVar sequenceNumber
          hPutStrLn handle (show currentSequenceNumber ++ " " ++ show accountNumber)
          let newSequenceNumber = currentSequenceNumber + 1
          putMVar sequenceNumber newSequenceNumber
      | otherwise = return () -- if the mtest isn't passed, don't print anything



-- -----------------------------------------------------------------------------
-- 3. Search mode (4pt)
-- -----------------------------------------------------------------------------

search :: Config -> ByteString -> IO (Maybe Int)
search (Config b e m p) query = do
  -- Create the initial queue and put the entire range in it as one item
  workQueue <- newQueue
  enqueue workQueue (b, e)
  -- Variable to keep track of how much work is left. When it becomes 0, the program terminates
  workLeft <- newMVar 1
  -- The return value. Its default is nothing, but it will be changed if a thread finds a solution
  outcome <- newIORef Nothing

  forkThreads p $ threadWork workQueue workLeft outcome

  readIORef outcome -- return the outcome

  where
    -- the maximum size of the work one thread can take for itself
    --  - set to one tenth of the size of the total range divided per thread
    --  - if the computed chunksize is too small, set it to 2 instead
    chunkSize
      | (e - b) `div` p `div` 10 < 2 = 2
      | otherwise = (e - b) `div` p `div` 10

    -- because of the way forkthreads is defined, an index needs to be given, but we don't use it, so it is discarded
    threadWork :: Queue (Int, Int) -> MVar Int -> IORef (Maybe Int) -> Int -> IO ()
    threadWork workQueue workLeft outcome _ = do
      currentWorkLeft <- takeMVar workLeft
      currentOutcome <- readIORef outcome
      -- If there is no work left to do or the solution has been found: put the MVar back (so other threads won't wait on it forever) and terminate
      if currentWorkLeft <= 0 || currentOutcome /= Nothing then putMVar workLeft currentWorkLeft else do
        -- take a chunk from the queue
        wholeWorkChunk <- dequeue workQueue
        
        workChunk <- splitWork workQueue workLeft currentWorkLeft wholeWorkChunk

        checkValidInRange outcome workChunk

        -- if a thread has finished its work, take new work from the queue
        -- the int isn't used so it can be undefined
        threadWork workQueue workLeft outcome undefined

    -- break off an appropriately sized piece of the work. The rest is enqueued again
    -- the workLeft MVar is updated so other threads can work on it again
    splitWork :: Queue (Int, Int) -> MVar Int -> Int -> (Int, Int) -> IO (Int, Int)
    splitWork workQueue workLeftMVar currentWorkLeft (lowerRange, upperRange)
      -- If the chunk is appropriately sized, take it in its entirety
      | upperRange - lowerRange <= chunkSize = do
          putMVar workLeftMVar (currentWorkLeft - 1)
          return (lowerRange, upperRange)
      | otherwise = do
          -- Take a chunk for the thread itself 
          let downSizedChunk = (lowerRange, lowerRange + chunkSize)
          let (restLowerRange, restUpperRange) = (lowerRange + chunkSize, upperRange)
          
          if restLowerRange == restUpperRange - 1 -- If the rest has size 1, do not split it in half
            then do enqueue workQueue (restLowerRange, restUpperRange)
                    putMVar workLeftMVar currentWorkLeft
            else do -- divide the rest in 2 halves and enqueue them
              enqueue workQueue (restLowerRange, restLowerRange + (restUpperRange - restLowerRange) `div` 2)
              enqueue workQueue (restLowerRange + (restUpperRange - restLowerRange) `div` 2, restUpperRange)
              putMVar workLeftMVar (currentWorkLeft + 1)

          return downSizedChunk

    -- perform the mtest and hash-test on a thread's range; update the outcome if a solution has been found
    checkValidInRange :: IORef (Maybe Int) -> (Int, Int) -> IO()
    checkValidInRange outcome (lowerRange, upperRange)
      | lowerRange == upperRange = return () -- stop recursion after reaching upper bound
      | otherwise =
          -- since mtest is faster, check that before checking the hash
          if mtest m lowerRange && checkHash query (show lowerRange) then do
            writeIORef outcome (Just lowerRange)
          -- if the solution hasn't been found, recurse and try again
          else do
            checkValidInRange outcome (lowerRange + 1, upperRange)




-- -----------------------------------------------------------------------------
-- Queue implementation
-- -----------------------------------------------------------------------------

-- The queue is defined by its readlock and writelock that point to both ends of the queue. Between these ends exist pointer-value pairs
data Queue a =
  Queue (MVar (List a))
        (MVar (List a))
type List a = MVar (Item a)
data Item a = Item a (List a)

-- In a new empty queue, the read- and writelock point to the same value; the start is the same as the end
newQueue :: IO (Queue a)
newQueue = do
    hole <- newEmptyMVar
    readLock <- newMVar hole
    writeLock <- newMVar hole
    return (Queue readLock writeLock)

enqueue :: Queue a -> a -> IO()
enqueue (Queue _ writeLock) value = do
  newHole <- newEmptyMVar
  let item = Item value newHole
  oldHole <- takeMVar writeLock
  putMVar oldHole item
  putMVar writeLock newHole

dequeue :: Queue a -> IO a
dequeue (Queue readLock _) = do
  -- get the pointer to the first item
  readEnd <- takeMVar readLock
  -- obtain the dequeued item's value and the pointer to the new first item in the list
  (Item value newFirstItemPointer) <- takeMVar readEnd
  -- make the readLock point to the new start of the queue
  putMVar readLock newFirstItemPointer
  return value

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
  -- Distribute the n-amount of undivisible work over the first n threads
  | index < threadsWithExtraWork = (b + index * (threadWorkAmount + 1), b + (index + 1) * (threadWorkAmount + 1))
  | otherwise = (b + index * threadWorkAmount + threadsWithExtraWork, b + (index + 1) * threadWorkAmount + threadsWithExtraWork)
  where
    -- how much work a single thread needs to do
    threadWorkAmount = (e - b) `div` p
    -- the amount of work that isn't neatly divisible
    threadsWithExtraWork = (e - b) `mod` p

-- CAS loop that adds a value to a counter
casAdd :: IORef Int -> Int -> IO()
casAdd counter addedValue = do
  -- obtain the current value and store it in a ticket
  ticket <- readForCAS counter
  let newValue = peekTicket ticket + addedValue
  (success, _) <- casIORef counter ticket newValue
  if success then return ()
  -- If the swap is unsuccessful: try again
  else casAdd counter addedValue

-- TODO: remove this probably
-- -- add a value to an MVar Int
-- mVarAdd :: MVar Int -> Int -> IO()
-- mVarAdd mVar addedValue = do


boolToInt :: Bool -> Int
boolToInt True = 1
boolToInt False = 0
