{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RebindableSyntax  #-}
{-# LANGUAGE TypeOperators     #-}

module Quickhull (

  Point, Line, SegmentedPoints,
  quickhull,

  -- Exported for display
  initialPartition,
  partition,

  -- Exported just for testing
  propagateL, shiftHeadFlagsL, segmentedScanl1,
  propagateR, shiftHeadFlagsR, segmentedScanr1,

) where

import Data.Array.Accelerate
import Data.Array.Accelerate.Debug.Trace
import qualified Prelude                      as P


-- Points and lines in two-dimensional space
--
type Point = (Int, Int)
type Line  = (Point, Point)

-- This algorithm will use a head-flags array to distinguish the different
-- sections of the hull (the two arrays are always the same length).
--
-- A flag value of 'True' indicates that the corresponding point is
-- definitely on the convex hull. The points after the 'True' flag until
-- the next 'True' flag correspond to the points in the same segment, and
-- where the algorithm has not yet decided whether or not those points are
-- on the convex hull.
--
type SegmentedPoints = (Vector Bool, Vector Point)


-- Core implementation
-- -------------------

-- Initialise the algorithm by first partitioning the array into two
-- segments. Locate the left-most (p₁) and right-most (p₂) points. The
-- segment descriptor then consists of the point p₁, followed by all the
-- points above the line (p₁,p₂), followed by the point p₂, and finally all
-- of the points below the line (p₁,p₂).
--
-- To make the rest of the algorithm a bit easier, the point p₁ is again
-- placed at the end of the array.
--
-- We indicate some intermediate values that you might find beneficial to
-- compute.
--
initialPartition :: Acc (Vector Point) -> Acc SegmentedPoints
initialPartition points =
  let
      p1, p2 :: Exp Point
      -- (lowest) left-most point
      p1 = the $ minimum points
      -- (highest) right-most point
      p2 = the $ maximum points 

      -- all points above the line
      isUpper :: Acc (Vector Bool)
      isUpper = map (pointIsLeftOfLine (T2 p1 p2)) points

      -- all points below the line
      isLower :: Acc (Vector Bool)
      isLower = map (pointIsRightOfLine (T2 p1 p2)) points

      offsetUpper :: Acc (Vector Int)
      countUpper  :: Acc (Scalar Int)
      T2 offsetUpper countUpper = T2 (scanl (+) 1 (bool2Int isUpper)) (sum (bool2Int isUpper))

      offsetLower :: Acc (Vector Int)
      countLower  :: Acc (Scalar Int)
      -- start the indeces of the lower points after P1 the upper points and p2 (so countUpper + 2)
      T2 offsetLower countLower = T2 (scanl (+) (the countUpper + 2) (bool2Int isLower)) (sum (bool2Int isLower))
        -- number of points below the line and their relative index

      destination :: Acc (Vector (Maybe DIM1))
      destination = map getDestiny (zip points (generate (I1 (length points))  (\(I1 i) -> i)))
        -- compute the index in the result array for each point (if it is present)
        -- check all points with map
        -- check if point is p1 or p2
        -- check if point is left of line -> get right index from offset
      getDestiny (T2 val index) = if (pointIsLeftOfLine (T2 p1 p2) val) then Just_ (I1 (offsetUpper !! index))
                                  else if (pointIsRightOfLine (T2 p1 p2) val) then Just_ (I1 (offsetLower !! index))
                                  else if val == p1 then Just_ (I1 0)
                                  else if (val == p2) then Just_ (I1 (the (countUpper) + 1))
                                  else Nothing_

      newPoints :: Acc (Vector Point)
      -- The size of the newpoints array is the size of p1, p2, the upper points and the lower point and an extra p1. (So the countUpper + the countLower + 3)
      -- The default value will be P1 so that an extra P1 is added to the end of the array.
      -- place each point into its corresponding segment of the result"
      newPoints = permute (const) (generate (I1 (the countUpper + the countLower + 3)) (\_ -> p1)) (\(I1 i) -> destination !! i) points

      -- Create head flags array demarcating the initial segments
      headFlags :: Acc (Vector Bool)
      headFlags = map (\p -> p == p1 || p == p2) newPoints
  in
  T2 headFlags newPoints

-- The core of the algorithm processes all line segments at once in
-- data-parallel. This is similar to the previous partitioning step, except
-- now we are processing many segments at once.
--
-- For each line segment (p₁,p₂) locate the point furthest from that line
-- p₃. This point is on the convex hull. Then determine whether each point
-- p in that segment lies to the left of (p₁,p₃) or the right of (p₂,p₃).
-- These points are undecided.

partition :: Acc SegmentedPoints -> Acc SegmentedPoints
partition (T2 headFlags points) = let
  

  --TODO FIX DIT!!!
  -- Indeces denoting the start of every point's segment
  trueFlagIndecesL :: Acc (Vector Bool) -> Acc (Vector Int)
  trueFlagIndecesL flagList = atraceId "starts" (propagateL flagList (generate (I1 (length (atraceId "points" points))) (\(I1 i) -> i)))

  -- Indeces denoting the end of every point's segment
  trueFlagIndecesR :: Acc (Vector Bool) -> Acc (Vector Int)
  trueFlagIndecesR flagList = atraceId "ends" (propagateR flagList (generate (I1 (length points)) (\(I1 i) -> i)))

  -- Array of all points, stored together with the start- and end-indicators of their segment 
  segmentedPoints :: Acc (Array DIM1 (Point, Int, Int))
  segmentedPoints = atraceId "segmentedPoints" (zip3 points (trueFlagIndecesL headFlags) (trueFlagIndecesR (atraceId "headFlags" headFlags)))

  -- The function compares the distances of two points to the line in question and returns the point with the biggest distance
  getBiggerDistance (T3 p s e) (T3 p2 s2 e2) = if (nonNormalizedDistance (T2 (points !! s) (points !! e)) p) > (nonNormalizedDistance (T2 (points !! s2) (points !! e2)) p2) then T3 p s e
                                               else T3 p2 s2 e2
  
  -- Unzip the vector of triples
  vecP3 = map (\(T3 p _ _) -> p) (segmentedScanl1 (getBiggerDistance) headFlags segmentedPoints)
  -- If a point's value is equal to the largest value in its segment, it is on the convex hull
  newFlags :: Acc (Vector Bool)
  newFlags = atraceId "newFlags" (map (\(T2 a b) -> a == b) (zip (atraceId "vecP3" vecP3) points))

  newSegmentedPoints :: Acc (Array DIM1 (Point, Int, Int, Bool))
  newSegmentedPoints = zip4 points (trueFlagIndecesL newFlags) (trueFlagIndecesR newFlags) newFlags

  -- All points outside of the convex hull and the new headflags
  outsideHull :: Acc (Vector Bool)
  outsideHull = map (\(T4 p s e f) -> (f || pointIsLeftOfLine (T2 (points !! s) (points !! e)) p)) newSegmentedPoints
  outsideHullInt = bool2Int outsideHull
  countNewPoints = sum outsideHullInt
  tempIndeces = segmentedScanl1 (+) newFlags outsideHullInt


  -- Calculate the offset of every partition
  shiftedIndecesL = scatter (generate (I1 (length tempIndeces)) (\(I1 i) -> i + 1)) (generate (I1 (length tempIndeces)) (\(I1 i) -> i - i)) (init tempIndeces) 
  offset = propagateL newFlags shiftedIndecesL
  offsetPastPart = scatter (generate (I1 (length offset)) (\(I1 i) -> i + 1)) (generate (I1 (length offset)) (\(I1 i) -> i - i)) (init offset)

  -- Calculate the new indeces of the headflags
  tempIndecesFlags = map (\(T4 f b o op) -> if f then b + o + op else b)(zip4 newFlags outsideHullInt offset offsetPastPart)
 
  -- Calculate the new indeces
  newIndeces = map (\val -> val - 1) (segmentedScanl1 (+) newFlags tempIndecesFlags)

  destination = map getDestiny (zip outsideHull newIndeces)

  getDestiny (T2 f index) = if f then Just_ (I1 index)
                            else Nothing_


  -- [1, 0, 0, 1, 0, 0, 1] newFlags
  -- [1, 0, 1, 1, 1, 1, 1] outside hull
  -- [1, 1, 2, 1, 2, 3, 1] newIndeces (left)
  -- [0, 1, 1, 2, 1, 2, 3] scatter and fill 0 with 0 (shifted right with default 0)
  -- [0, 0, 0, 2, 2, 2, 3] propagateL with the scatter and newFlags -- offset
  -- [0, 0, 0, 0, 2, 2, 2] scatter shift to right with 0 as default -- offsetPastPartition

  -- zip 4 
  -- newFlags
  -- outsiddHull
  -- offset
  -- offsetPast
  -- if headFlag -> offset + offsetPast + newFlags
  -- else -> outsideHull   map
  -- [1, 0, 1, 3, 1, 1, 6] headFlagsIndeces
  -- segmentedScanL + newFlags headFlagsIndeces 
  -- [1, 1, 2, 3, 4, 5, 6] ActualIndeces
  -- [0, 0, 1, 2, 3, 4, 5] map (-1) ActualIndeces
  -- get destiny
  -- zip 4
  -- newFlags
  -- outsideHull
  -- ActualIndeces
  -- points
  -- get destiny map
  -- [0, n, 1, 2, 3, 4, 5S]
  -- 
  -- permute


  zipped = zip newFlags points
  p1 = zipped !! 0
  -- newHeadFlags and newPoints should have the length of the amount of True's in outsideHull
  result = permute (const) (generate (I1 (the countNewPoints)) (\_ -> p1)) (\(I1 i) -> destination !! i) zipped

  newHeadFlags = map (\(T2 b _) -> b) result
  newPoints = map (\(T2 _ p) -> p) result

  in 
  T2 newHeadFlags newPoints


-- The completed algorithm repeatedly partitions the points until there are
-- no undecided points remaining. What remains is the convex hull.
--
quickhull :: Acc (Vector Point) -> Acc (Vector Point)
quickhull = init . (\(T2 _ points) -> points) . partition . initialPartition -- remove last point
-- maybe something with awhile

-- Helper functions
-- ----------------

-- Converts booleans to integers
bool2Int :: Acc (Vector Bool) -> Acc (Vector Int)
bool2Int boolList = map (\b -> if b == True_ then 1 else 0) boolList

-- >>> import Data.Array.Accelerate.Interpreter
-- >>> let flags  = fromList (Z :. 9) [True,False,False,True,True,False,False,False,True]
-- >>> let values = fromList (Z :. 9) [1   ,2    ,3    ,4   ,5   ,6    ,7    ,8    ,9   ] :: Vector Int
-- >>> run $ propagateL (use flags) (use values)
--
-- should be:
-- Vector (Z :. 9) [1,1,1,4,5,5,5,5,9]
propagateL :: Elt a => Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
propagateL flags values = segmentedScanl1 (\ a _ -> a) flags values

-- >>> import Data.Array.Accelerate.Interpreter
-- >>> let flags  = fromList (Z :. 9) [True,False,False,True,True,False,False,False,True]
-- >>> let values = fromList (Z :. 9) [1   ,2    ,3    ,4   ,5   ,6    ,7    ,8    ,9   ] :: Vector Int
-- >>> run $ propagateR (use flags) (use values)
--
-- should be:
-- Vector (Z :. 9) [1,4,4,4,5,9,9,9,9]
propagateR :: Elt a => Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
propagateR flags values = segmentedScanr1 (\ a _ -> a) flags values

-- >>> import Data.Array.Accelerate.Interpreter
-- >>> run $ shiftHeadFlagsL (use (fromList (Z :. 6) [False,False,False,True,False,True]))
--
-- should be:
-- Vector (Z :. 6) [False,False,True,False,True,True]
shiftHeadFlagsL :: Acc (Vector Bool) -> Acc (Vector Bool)
shiftHeadFlagsL flags = scatter (generate (I1 (length flags)) (\(I1 i) -> i)) (generate (I1 (length flags)) (\_ -> True_)) (tail flags)

-- >>> import Data.Array.Accelerate.Interpreter
-- >>> run $ shiftHeadFlagsR (use (fromList (Z :. 6) [True,False,False,True,False,False]))
--
-- should be:
-- Vector (Z :. 6) [True,True,False,False,True,False]
shiftHeadFlagsR :: Acc (Vector Bool) -> Acc (Vector Bool)
shiftHeadFlagsR flags = scatter (generate (I1 (length flags)) (\(I1 i) -> i + 1)) (generate (I1 (length flags)) (\_ -> True_)) (init flags)

-- >>> import Data.Array.Accelerate.Interpreter
-- >>> let flags  = fromList (Z :. 9) [True,False,False,True,True,False,False,False,True]
-- >>> let values = fromList (Z :. 9) [1   ,2    ,3    ,4   ,5   ,6    ,7    ,8    ,9   ] :: Vector Int
-- >>> run $ segmentedScanl1 (+) (use flags) (use values)
--
-- Expected answer:
-- >>> fromList (Z :. 9) [1, 1+2, 1+2+3, 4, 5, 5+6, 5+6+7, 5+6+7+8, 9] :: Vector Int
-- Vector (Z :. 9) [1,3,6,4,5,11,18,26,9]
--
-- Mind that the interpreter evaluates scans and folds sequentially, so
-- non-associative combination functions may seem to work fine here -- only to
-- fail spectacularly when testing with a parallel backend on larger inputs. ;)
segmentedScanl1 :: Elt a => (Exp a -> Exp a -> Exp a) -> Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
segmentedScanl1 func flags values = map (\(T2 _ v) -> v) (scanl1 (segmented func) (zip flags values))

-- >>> import Data.Array.Accelerate.Interpreter
-- >>> let flags  = fromList (Z :. 9) [True,False,False,True,True,False,False,False,True]
-- >>> let values = fromList (Z :. 9) [1   ,2    ,3    ,4   ,5   ,6    ,7    ,8    ,9   ] :: Vector Int
-- >>> run $ segmentedScanr1 (+) (use flags) (use values)
--
-- Expected answer:
-- >>> fromList (Z :. 9) [1, 2+3+4, 3+4, 4, 5, 6+7+8+9, 7+8+9, 8+9, 9] :: Vector Int
-- Vector (Z :. 9) [1,9,7,4,5,30,24,17,9]
segmentedScanr1 :: Elt a => (Exp a -> Exp a -> Exp a) -> Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
segmentedScanr1 func flags values = map (\(T2 _ v) -> v) (scanr1 (\ a b -> (segmented func) b a) (zip flags values))


-- Given utility functions
-- -----------------------

pointIsLeftOfLine :: Exp Line -> Exp Point -> Exp Bool
pointIsLeftOfLine (T2 (T2 x1 y1) (T2 x2 y2)) (T2 x y) = nx * x + ny * y > c
  where
    nx = y1 - y2
    ny = x2 - x1
    c  = nx * x1 + ny * y1

pointIsRightOfLine :: Exp Line -> Exp Point -> Exp Bool
pointIsRightOfLine (T2 (T2 x1 y1) (T2 x2 y2)) (T2 x y) = nx * x + ny * y < c
  where
    nx = y1 - y2
    ny = x2 - x1
    c  = nx * x1 + ny * y1

nonNormalizedDistance :: Exp Line -> Exp Point -> Exp Int
nonNormalizedDistance (T2 (T2 x1 y1) (T2 x2 y2)) (T2 x y) = nx * x + ny * y - c
  where
    nx = y1 - y2
    ny = x2 - x1
    c  = nx * x1 + ny * y1

segmented :: Elt a => (Exp a -> Exp a -> Exp a) -> Exp (Bool, a) -> Exp (Bool, a) -> Exp (Bool, a)
segmented f (T2 aF aV) (T2 bF bV) = T2 (aF || bF) (if bF then bV else f aV bV)

-- | Read a file (such as "inputs/1.dat") and return a vector of points,
-- suitable as input to 'quickhull' or 'initialPartition'. Not to be used in
-- your quickhull algorithm, but can be used to test your functions in ghci.
readInputFile :: P.FilePath -> P.IO (Vector Point)
readInputFile filename =
  (\l -> fromList (Z :. P.length l) l)
  P.. P.map (\l -> let ws = P.words l in (P.read (ws P.!! 0), P.read (ws P.!! 1)))
  P.. P.lines
  P.<$> P.readFile filename
