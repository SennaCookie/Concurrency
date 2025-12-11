{-# LANGUAGE RecordWildCards  #-}
--
-- INFOB3CC Concurrency
-- Practical 2: Single Source Shortest Path
--
--    Δ-stepping: A parallelisable shortest path algorithm
--    https://www.sciencedirect.com/science/article/pii/S0196677403000762
--
-- https://ics.uu.nl/docs/vakken/b3cc/assessment.html
--
-- https://cs.iupui.edu/~fgsong/LearnHPC/sssp/deltaStep.html
--

module DeltaStepping (

  Graph, Node, Distance,
  deltaStepping,

) where

import Sample
import Utils

import Control.Concurrent
import Control.Concurrent.MVar
import Control.Monad
import Data.Bits
import Data.Graph.Inductive                                         ( Gr )
import Data.IORef
import Data.IntMap.Strict                                           ( IntMap )
import Data.IntSet                                                  ( IntSet )
import Data.Vector.Storable                                         ( Vector )
import Data.Word
import Foreign.Ptr
import Foreign.Storable
import Text.Printf
import qualified Data.Graph.Inductive                               as G
import qualified Data.IntMap.Strict                                 as Map
import qualified Data.IntSet                                        as Set
import qualified Data.Vector.Mutable                                as V
import qualified Data.Vector.Storable                               as S ( unsafeFreeze )
import qualified Data.Vector.Storable.Mutable                       as S


type Graph    = Gr String Distance  -- Graphs have nodes labelled with Strings and edges labelled with their distance
type Node     = Int                 -- Nodes (vertices) in the graph are integers in the range [0..]
type Distance = Float               -- Distances between nodes are (positive) floating point values


-- | Find the length of the shortest path from the given node to all other nodes
-- in the graph. If the destination is not reachable from the starting node the
-- distance is 'Infinity'.
--
-- Nodes must be numbered [0..]
--
-- Negative edge weights are not supported.
--
-- NOTE: The type of the 'deltaStepping' function should not change (since that
-- is what the test suite expects), but you are free to change the types of all
-- other functions and data structures in this module as you require.
--
deltaStepping
    :: Bool                             -- Whether to print intermediate states to the console, for debugging purposes
    -> Graph                            -- graph to analyse
    -> Distance                         -- delta (step width, bucket width)
    -> Node                             -- index of the starting node
    -> IO (Vector Distance)
deltaStepping verbose graph delta source = do
  threadCount <- getNumCapabilities             -- the number of (kernel) threads to use: the 'x' in '+RTS -Nx'

  -- Initialise the algorithm
  (buckets, distances)  <- initialise graph delta source
  printVerbose verbose "initialse" graph delta buckets distances

  let
    -- The algorithm loops while there are still non-empty buckets
    loop = do
      done <- allBucketsEmpty buckets
      if done
      then return ()
      else do
        printVerbose verbose "result" graph delta buckets distances
        step verbose threadCount graph delta buckets distances
        loop
  loop

  printVerbose verbose "result" graph delta buckets distances
  -- Once the tentative distances are finalised, convert into an immutable array
  -- to prevent further updates. It is safe to use this "unsafe" function here
  -- because the mutable vector will not be used any more, so referential
  -- transparency is preserved for the frozen immutable vector.
  --
  -- NOTE: The function 'Data.Vector.convert' can be used to translate between
  -- different (compatible) vector types (e.g. boxed to storable)
  --
  S.unsafeFreeze distances


-- Initialise algorithm state
--
initialise
    :: Graph
    -> Distance
    -> Node
    -> IO (Buckets, TentativeDistances)
initialise graph delta source = do

  -- | Tentative distances
  let amountOfNodes = G.noNodes graph
  -- generate an IOVector where all tentative distances are infinity, except the starting node, which is zero
  -- TODO: (Remove this line if it turns out to be true: this code assumes the graph has nodes in the range [0..] where it doesn't skip any indeces)
  tentativeDistances <-  S.generate amountOfNodes (\index -> if index == source then 0 else infinity)

  -- | Buckets
  let longestEdgeDistance = maximum $ map G.edgeLabel $ G.labEdges graph
  let noBuckets = round (longestEdgeDistance / delta) + 1
  -- Create variable that keeps track of the first bucket's index (starts at 0)
  firstBucketIndex <- newIORef 0
  -- fill first bucket with the source node; rest is empty
  initialBucketArray <- V.generate noBuckets (\index -> if index == 0 then Set.singleton source else Set.empty)
  let buckets = Buckets{
    firstBucket = firstBucketIndex,
    bucketArray = initialBucketArray}

  return (buckets, tentativeDistances)

 

-- Take a single step of the algorithm.
-- That is, one iteration of the outer while loop.
--
step
    :: Bool
    -> Int
    -> Graph
    -> Distance
    -> Buckets
    -> TentativeDistances
    -> IO ()
step verbose threadCount graph delta buckets distances = do
  -- Retrieve the first non-empty bucket
  let thisBucketArray = bucketArray buckets 
  thisBucketIndex <- findNextBucket buckets
  
  -- variable to keep track of which nodes have been handled 
  r <- newIORef Set.empty
  --print("r: " ++ show rr)
  -- handle the light edges of the nodes in a bucket
  -- terminate loop when the bucket is empty
  let loop = do 
        thisBucket <- V.read thisBucketArray thisBucketIndex
        if thisBucket == Set.empty
        then return ()--print("Im empty")
        else do
          -- p x = (x < delta) TODO: remove dis line
          -- req = IO (IntMap) TODO: remove dis line
          --print("hallo")
          req <- findRequests threadCount (\x -> x < delta) graph thisBucket distances
          -- update r with the nodes that have been handled
          oldR <- readIORef r
          writeIORef r (Set.union oldR thisBucket)
          -- empty the bucket and relax requests
          V.write thisBucketArray thisBucketIndex Set.empty

          -- Nodes may (re)enter bucket
          relaxRequests threadCount buckets distances delta req
          printVerbose verbose "inner step" graph delta buckets distances
          loop
  loop
  

  -- get all the treated nodes and do the heavy edges at once
  --print("I'm doin the heavy edges woo")
  heavyNodes <- readIORef r
  heavyReq <- findRequests threadCount (\x -> x >= delta) graph heavyNodes distances
  relaxRequests threadCount buckets distances delta heavyReq



-- Once all buckets are empty, the tentative distances are finalised and the
-- algorithm terminates.
-- TODO: Maybe ? I didn't finalize all tentative distances. IDK if ur supposed to do that explicitly here
allBucketsEmpty :: Buckets -> IO Bool
allBucketsEmpty buckets = do
  -- get information about the buckets
  let thisBucketArray = bucketArray buckets
      noBuckets = V.length thisBucketArray -- number of buckets
  
  -- Recursively check if every bucket is empty by index
  -- Starts at index 0, because the real indeces are not important
  theseBucketsEmpty 0 noBuckets thisBucketArray
  
  where
    theseBucketsEmpty index noBuckets thisBucketArray
      | index == noBuckets = return True
      | otherwise = do
          thisBucket <- V.read thisBucketArray index
          if thisBucket == Set.empty
            then theseBucketsEmpty (index + 1) noBuckets thisBucketArray
            else return False -- if any bucket is not empty, stop recursing and return False



-- Return the index of the first non-empty bucket.
-- Assumes that there is at least one non-empty bucket remaining.
--
findNextBucket :: Buckets -> IO Int
findNextBucket buckets = do
  currentFirstBucket <- readIORef $ firstBucket buckets -- the real index
  let bucketIOVector = bucketArray buckets
      noBuckets = V.length bucketIOVector -- number of buckets
  res <- bucketNotEmpty currentFirstBucket noBuckets bucketIOVector
  
  -- Recursively check for every bucket if it's filled, starting with the first bucket
  --print("nextBucket: " ++ show res)
  return res

  where 
    bucketNotEmpty index noBuckets bucketIOVector = do
      thisBucket <- V.read bucketIOVector $ index `mod` noBuckets
      if thisBucket == Set.empty
        then bucketNotEmpty (index + 1) noBuckets bucketIOVector
        else return index
  


-- Create requests of (node, distance) pairs that fulfil the given predicate
--
findRequests
    :: Int
    -> (Distance -> Bool)
    -> Graph
    -> IntSet
    -> TentativeDistances
    -> IO (IntMap Distance)
findRequests threadCount p graph v' distances = do
  -- v' is the set of nodes in the bucket
  let noNodes = Set.size v'
  nodesInBucket <- newMVar v'
  -- a counter that keeps track of which node is  being handled
  count <- newMVar 0
  -- at the start of the method, the Map of requests is empty
  -- threads will add the requests they find to this intMap
  intMap <- newMVar Map.empty

  forkThreads threadCount (searchRequests nodesInBucket intMap count noNodes distances)
  
  -- return the final intMap of requests
  res <- takeMVar intMap
  --print("requesrs: " ++ show res)
  return res
  -- TODO replace above with : takeMVar intMap

  where
    -- find the requests of a single node and add it to the total of requests
    searchRequests nodesInBucket intMap count noNodes tentativeDistances _ = do
      currentCount <- takeMVar count
      -- if all modes have been checked, terminate thread
      if currentCount == noNodes then putMVar count currentCount
      else do
        putMVar count (currentCount + 1)
        -- take a (the lowest indexed) node from the set 
        nodeSet <- takeMVar nodesInBucket
        let (node, newIntSet) = Set.deleteFindMin nodeSet
        putMVar nodesInBucket newIntSet
        -- find edges of the node and turn them into a Map of requests
        nodeCost <- S.read tentativeDistances node
        let edges = [(neighbour, nodeCost + dist) |(_, neighbour, dist) <- (G.out graph node), p dist]
        --print("edges: " ++ show edges)
        let newIntMap = Map.fromList edges
        -- get intMap of requests made by other threads so far
        oldIntMap <- takeMVar intMap
        -- merge the new requests Map with the old one; in case of duplicate requests, take the shortest
        --print("union intmaps requests: " ++ show (Map.unionWith (min) oldIntMap newIntMap))
        putMVar intMap (Map.unionWith (min) oldIntMap newIntMap)
        -- recurse
        searchRequests nodesInBucket intMap count noNodes tentativeDistances undefined



-- Execute requests for each of the given (node, distance) pairs
--
relaxRequests
    :: Int
    -> Buckets
    -> TentativeDistances
    -> Distance
    -> IntMap Distance
    -> IO ()
relaxRequests threadCount buckets distances delta req = do
  requests <- newMVar [req]
  let noReq = Map.size req
  let workload = noReq `div` threadCount
  
  forkThreads threadCount (singleThreadWork requests workload)

  where
    singleThreadWork requests workload _ = do 
      workList <- takeMVar requests
      if workList == [] then putMVar requests []
      else if Map.size (head workList) > workload && Map.size (head workList) > 1 then do
        let work = head workList
        let rest = tail workList
        let chunks = Map.splitRoot work
        let firstChunk = chunks !! 0
        let secondChunk = chunks !! 1
        putMVar requests (firstChunk : secondChunk : rest)
        singleThreadWork requests workload undefined
      else do
        putMVar requests (tail workList)
        let work = head workList
        --print("single relax")
        --print(show $ Map.toList work)
        sequence_ $ map (relax buckets distances delta) (Map.toList work) 
        singleThreadWork requests workload undefined

-- Execute a single relaxation, moving the given node to the appropriate bucket
-- as necessary
--
relax :: Buckets
      -> TentativeDistances
      -> Distance
      -> (Node, Distance) -- (w, x) in the paper
      -> IO ()
relax buckets distances delta (node, newDistance) = do
  --print("relax")
  -- if the newDistance is shorter than the current, update the TentativeDistances
  currentDistance <- S.read distances node
  if newDistance < currentDistance
    then do 
      S.write distances node newDistance
      let thisBucketArray = bucketArray buckets
      let noBuckets = V.length thisBucketArray -- (number of buckets)

      -- the relative index of the bucket we need to add the node to
      let nodeBucketIndex = (round (newDistance / delta)) `mod` noBuckets

      -- insert the node with its correct tentative distance into the correct bucket
      --print("inserting")
      -- TODO: Not in correct bucket yet
      V.modify thisBucketArray (Set.insert node) nodeBucketIndex
  else return()

-- -- the (possibly updated) tentativeDistance of the node
--   tentativeDistance <- S.read distances node

-- -- retrieve information on the buckets
--   let thisBucketArray = bucketArray buckets
--   let noBuckets = V.length thisBucketArray -- (number of buckets)

-- -- the relative index of the bucket we need to add the node to
--   let nodeBucketIndex = (round (tentativeDistance / delta)) `mod` noBuckets

-- -- insert the node with its correct tentative distance into the correct bucket
--   print("inserting")
--   -- TODO: Not in correct bucket yet
--   V.modify thisBucketArray (Set.insert node) nodeBucketIndex


-- -----------------------------------------------------------------------------
-- Starting framework
-- -----------------------------------------------------------------------------
--
-- Here are a collection of (data)types and utility functions that you can use.
-- You are free to change these as necessary.
--

type TentativeDistances = S.IOVector Distance

-- TODO: Make sure indexing of firstBucket starts at 0, but I'm pretty sure it does
data Buckets = Buckets
  { firstBucket   :: {-# UNPACK #-} !(IORef Int)           -- real index of the first bucket (j)
  , bucketArray   :: {-# UNPACK #-} !(V.IOVector IntSet)   -- cyclic array of buckets
  }


-- The initial tentative distance, or the distance to unreachable nodes
--
infinity :: Distance
infinity = 1/0


-- Forks 'n' threads. Waits until those threads have finished. Each thread
-- runs the supplied function given its thread ID in the range [0..n).
--
forkThreads :: Int -> (Int -> IO ()) -> IO ()
forkThreads n action = do
  -- Fork the threads and create a list of the MVars which per thread tell
  -- whether the action has finished.
  finishVars <- mapM work [0 .. n - 1]
  -- Once all the worker threads have been launched, now wait for them all to
  -- finish by blocking on their signal MVars.
  mapM_ takeMVar finishVars
  where
    -- Create a new empty MVar that is shared between the main (spawning) thread
    -- and the worker (child) thread. The main thread returns immediately after
    -- spawning the worker thread. Once the child thread has finished executing
    -- the given action, it fills in the MVar to signal to the calling thread
    -- that it has completed.
    --
    work :: Int -> IO (MVar ())
    work index = do
      done <- newEmptyMVar
      _    <- forkOn index (action index >> putMVar done ())  -- pin the worker to a given CPU core
      return done


printVerbose :: Bool -> String -> Graph -> Distance -> Buckets -> TentativeDistances -> IO ()
printVerbose verbose title graph delta buckets distances = when verbose $ do
  putStrLn $ "# " ++ title
  printCurrentState graph distances
  printBuckets graph delta buckets distances
  putStrLn "Press enter to continue"
  _ <- getLine
  return ()

-- Print the current state of the algorithm (tentative distance to all nodes)
--
printCurrentState
    :: Graph
    -> TentativeDistances
    -> IO ()
printCurrentState graph distances = do
  printf "  Node  |  Label  |  Distance\n"
  printf "--------+---------+------------\n"
  forM_ (G.labNodes graph) $ \(v, l) -> do
    x <- S.read distances v
    if isInfinite x
       then printf "  %4d  |  %5v  |  -\n" v l
       else printf "  %4d  |  %5v  |  %f\n" v l x
  --
  printf "\n"

printBuckets
    :: Graph
    -> Distance
    -> Buckets
    -> TentativeDistances
    -> IO ()
printBuckets graph delta Buckets{..} distances = do
  first <- readIORef firstBucket
  mapM_
    (\idx -> do
      let idx' = first + idx
      printf "Bucket %d: [%f, %f)\n" idx' (fromIntegral idx' * delta) ((fromIntegral idx'+1) * delta)
      b <- V.read bucketArray (idx' `rem` V.length bucketArray)
      printBucket graph b distances
    )
    [ 0 .. V.length bucketArray - 1 ]

-- Print the current bucket
--
printCurrentBucket
    :: Graph
    -> Distance
    -> Buckets
    -> TentativeDistances
    -> IO ()
printCurrentBucket graph delta Buckets{..} distances = do
  j <- readIORef firstBucket
  b <- V.read bucketArray (j `rem` V.length bucketArray)
  printf "Bucket %d: [%f, %f)\n" j (fromIntegral j * delta) (fromIntegral (j+1) * delta)
  printBucket graph b distances

-- Print a given bucket
--
printBucket
    :: Graph
    -> IntSet
    -> TentativeDistances
    -> IO ()
printBucket graph bucket distances = do
  printf "  Node  |  Label  |  Distance\n"
  printf "--------+---------+-----------\n"
  forM_ (Set.toAscList bucket) $ \v -> do
    let ml = G.lab graph v
    x <- S.read distances v
    case ml of
      Nothing -> printf "  %4d  |   -   |  %f\n" v x
      Just l  -> printf "  %4d  |  %5v  |  %f\n" v l x
  --
  printf "\n"

