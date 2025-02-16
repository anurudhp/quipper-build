{-# LANGUAGE FlexibleContexts #-}

-- | This module provides functions for solving one- and
-- two-dimensional grid problems.

module Quantum.Synthesis.GridProblems where

import Quantum.Synthesis.Ring
import Quantum.Synthesis.Matrix
import Quantum.Synthesis.QuadraticEquation

import Control.Monad
import Data.Maybe
import System.Random

-- ----------------------------------------------------------------------
-- * 1-dimensional grid problems

-- $ The /1-dimensional grid problem/ is the following: given closed
-- intervals /A/ and /B/ of the real numbers, find all α ∈ ℤ[√2] such
-- that α ∈ /A/ and α[sup •] ∈ /B/.
-- 
-- Let Δx be the size of /A/, and Δy the size of /B/. It is a theorem
-- that the 1-dimensional grid problem has at least one solution if
-- ΔxΔy ≥ (1 + √2)², and at most one solution if ΔxΔy < 1.
-- Asymptotically, the expected number of solutions is ΔxΔy/\√8.
-- 
-- The following functions provide solutions to a number of variations
-- of the grid problem.  All functions are formulated so that the
-- intervals can be specified exactly (using a type such as
-- 'QRootTwo'), or approximately (using a type such as 'Double' or
-- 'FixedPrec' /e/).

-- ----------------------------------------------------------------------
-- ** General solutions

-- | Given two intervals /A/ = [/x/₀, /x/₁] and /B/ = [/y/₀, /y/₁] of
-- real numbers, output all solutions α ∈ ℤ[√2] of the 1-dimensional
-- grid problem for /A/ and /B/. The list is produced lazily, and is
-- sorted in order of increasing α. 
gridpoints :: (RootTwoRing r, Fractional r, Floor r, Ord r) => (r, r) -> (r, r) -> [ZRootTwo]
gridpoints (x0, x1) (y0, y1) = do
  [ beta | beta' <- gridpoints_internal (x0', x1') (y0', y1'),
           let beta = beta' + alpha,
           test beta ]
  where
    a = floor_of (x0 + y0) `div` 2
    b = floor_of (roottwo * (x0 - y0)) `div` 4
    alpha = RootTwo a b
    xoff = fromZRootTwo alpha
    yoff = fromZRootTwo (adj2 alpha)
    x0' = x0 - xoff 
    x1' = x1 - xoff 
    y0' = y0 - yoff 
    y1' = y1 - yoff 

    test x = fromZRootTwo x `within` (x0, x1) && fromZRootTwo (adj2 x) `within` (y0, y1)
  
-- | Like 'gridpoints', but only produce solutions /a/ + /b/√2 where
-- /a/ has the same parity as the given integer.
gridpoints_parity :: (RootTwoRing r, Fractional r, Floor r, Ord r) => Integer -> (r, r) -> (r, r) -> [ZRootTwo]
gridpoints_parity e (x0,x1) (y0,y1) = do
  z' <- gridpoints (x0', x1') (-y1', -y0')
  return (roottwo * z' + fromInteger e2)
  where 
    x0' = (x0 - e') / roottwo
    x1' = (x1 - e') / roottwo
    y0' = (y0 - e') / roottwo
    y1' = (y1 - e') / roottwo
    e' = fromInteger e2
    e2 = e `mod` 2

-- ----------------------------------------------------------------------
-- ** Randomized solutions

-- | Given two intervals /A/ = [/x/₀, /x/₁] and /B/ = [/y/₀, /y/₁] of
-- real numbers, and a source of randomness, output a random solution
-- α ∈ ℤ[√2] of the 1-dimensional grid problem for /A/ and /B/.
-- 
-- Note: the randomness is not uniform. To ensure that the set of
-- solutions is non-empty, we must have ΔxΔy ≥ (1 + √2)², where Δx =
-- /x/₁ − /x/₀ ≥ 0 and Δy = /y/₁ − /y/₀ ≥ 0. If there are no solutions
-- at all, the function returns 'Nothing'.
gridpoint_random :: (RootTwoRing r, Fractional r, Floor r, Ord r, RandomGen g) => (r, r) -> (r, r) -> g -> Maybe ZRootTwo
gridpoint_random (x0, x1) (y0, y1) g = z
  where
    dx = max 0 (x1 - x0)
    dy = max 0 (y1 - y0)
    area = dx * dy
    n = floor_of (area + 1)
    (i,_) = randomR (0, n-1) g
    r = fromInteger i / fromInteger n
    pts = gridpoints (x0 + r * dx, x1) (y0, y1) ++ gridpoints (x0, x1) (y0, y1)
    z = case pts of
      h:t -> Just h
      [] -> Nothing

-- | Like 'gridpoint_random', but only produce solutions /a/ + /b/√2
-- where /a/ has the same parity as the given integer.
gridpoint_random_parity :: (RootTwoRing r, Fractional r, Floor r, Ord r, RandomGen g) => Integer -> (r, r) -> (r, r) -> g -> Maybe ZRootTwo
gridpoint_random_parity e (x0,x1) (y0,y1) g = do
  z' <- gridpoint_random (x0', x1') (-y1', -y0') g
  return (roottwo * z' + fromInteger e2)
  where 
    x0' = (x0 - e') / roottwo
    x1' = (x1 - e') / roottwo
    y0' = (y0 - e') / roottwo
    y1' = (y1 - e') / roottwo
    e' = fromInteger e2
    e2 = e `mod` 2

-- ----------------------------------------------------------------------
-- ** Scaled solutions

-- $ The scaled version of the 1-dimensional grid problem is the
-- following: given closed intervals /A/ and /B/ of the real numbers,
-- and /k/ ≥ 0, find all α ∈ ℤ[√2] \/ √2[sup /k/] such that α ∈ /A/
-- and α[sup •] ∈ /B/.

-- | Given intervals /A/ = [/x/₀, /x/₁] and /B/ = [/y/₀, /y/₁], and an
-- integer /k/ ≥ 0, output all solutions α ∈ ℤ[√2] \/ √2[sup /k/] of
-- the scaled 1-dimensional grid problem for /A/, /B/, and /k/.  The
-- list is produced lazily, and is sorted in order of increasing /α/.
gridpoints_scaled :: (RootTwoRing r, Fractional r, Floor r, Ord r) => (r, r) -> (r, r) -> Integer -> [DRootTwo]
gridpoints_scaled (x0, x1) (y0, y1) k = do
  w <- gridpoints (x0', x1') (y0', y1')
  return (scale * fromZRootTwo w)
  where
    scale = roothalf^k
    scale_inv = roottwo^k
    (x0', x1') = (scale_inv * x0, scale_inv * x1)
    (y0', y1') 
      | even k = (scale_inv * y0, scale_inv * y1)
      | otherwise = (-scale_inv * y1, -scale_inv * y0)

-- | Like 'gridpoints_scaled', but assume /k/ ≥ 1, take an additional
-- parameter β ∈ ℤ[√2] \/ √2[sup /k/], and return only those α such
-- that β − α ∈ ℤ[√2] \/ √2[sup /k-1/].
gridpoints_scaled_parity :: (RootHalfRing r, Fractional r, Floor r, Ord r) => DRootTwo -> (r, r) -> (r, r) -> Integer -> [DRootTwo]
gridpoints_scaled_parity beta (x0, x1) (y0, y1) k 
  | denomexp beta <= k-1   = gridpoints_scaled (x0, x1) (y0, y1) (k-1)
  | otherwise              = do
    z' <- gridpoints_scaled (x0+offs', x1+offs') (y0+offs_bul', y1+offs_bul') (k-1)
    return (z' - offs)
  where 
    offs = roothalf^k
    offs_bul = adj2 offs
    offs' = fromDRootTwo offs
    offs_bul' = fromDRootTwo offs_bul

-- ----------------------------------------------------------------------
-- * 2-dimensional grid problems
    
-- $ The /2-dimensional grid problem/ is the following: given bounded
-- convex subsets /A/ and /B/ of ℂ with non-empty interior, find all
-- /u/ ∈ ℤ[ω] such that /u/ ∈ /A/ and /u/[sup •] ∈ /B/.
    
-- ----------------------------------------------------------------------
-- ** Representation of convex sets
    
-- $ Since convex sets /A/ and /B/ are inputs of the 2-dimensional
-- grid problem, we need a way to specify convex subsets of ℂ. Our
-- specification of a convex sets consists of three parts:
-- 
-- * a /bounding ellipse/ for the convex set;
-- 
-- * a /characteristic function/, which tests whether any given point
-- is an element of the convex set; and
-- 
-- * a /line intersector/, which estimates the intersection of any
-- given straight line and the convex set.

-- | A point in the plane.
type Point r = (r,r)

-- | Convert a point with coordinates in 'DRootTwo' to a point with
-- coordinates in any 'RootHalfRing'.
point_fromDRootTwo :: (RootHalfRing r) => Point DRootTwo -> Point r
point_fromDRootTwo (x, y) = (fromDRootTwo x, fromDRootTwo y)

-- | An operator is a real 2×2-matrix.
type Operator a = Matrix Two Two a

-- | An /ellipse/ is given by an operator /D/ and a center /p/; the
-- ellipse in this case is
-- 
-- /A/ = { /v/ | (/v/-/p/)[sup †] /D/ (/v/-/p/) ≤ 1}.
data Ellipse r = Ellipse (Operator r) (Point r)
                 deriving (Show)

-- | The /characteristic function/ of a set /A/ inputs a point /p/,
-- and outputs 'True' if /p/ ∈ /A/ and 'False' otherwise.
-- 
-- The point /p/ is given of an exact type, so characteristic
-- functions have the opportunity to use infinite precision.
type CharFun = Point DRootTwo -> Bool

-- | A /line intersector/ knows about some compact convex set
-- /A/. Given a straight line /L/, it computes an approximation of the
-- intersection of /L/ and /A/.
-- 
-- More specifically, /L/ is given as a parametric equation /p/(/t/) =
-- /v/ + /tw/, where /v/ and /w/ ≠ 0 are vectors.  Given /v/ and /w/,
-- the line intersector returns (an approximation of) /t/₀ and /t/₁
-- such that /p/(/t/) ∈ /A/ iff /t/ ∈ [/t/₀, /t/₁].
type LineIntersector r = (Point DRootTwo -> Point DRootTwo -> Maybe (r, r))

-- | A compact convex set is given by a bounding ellipse, a
-- characteristic function, and a line intersector.
data ConvexSet r = ConvexSet (Ellipse r) CharFun (LineIntersector r)

instance (Show r) => Show (ConvexSet r) where
  show (ConvexSet ell tst int) = "ConvexSet (" ++ show ell ++ ", ..., ...)"

-- ----------------------------------------------------------------------
-- ** Specific convex sets
      
-- | The closed unit disk.
unitdisk :: (Fractional r, Ord r, RootHalfRing r, Quadratic QRootTwo r) => ConvexSet r
unitdisk = ConvexSet ell tst int where
  ell = Ellipse 1 (0,0)
  
  int p v
    | q == Nothing         = Nothing
    | otherwise            = Just (t0, t1)
    where
      a = iprod v v
      b = 2 * iprod v p
      c = iprod p p - 1
      q = quadratic (fromDRootTwo a :: QRootTwo) (fromDRootTwo b) (fromDRootTwo c)
      Just (t0, t1) = q
    
  tst (x,y) = x^2 + y^2 <= 1

-- | A closed disk of radius √/s/, centered at the origin. Assume /s/ > 0.
disk :: (Fractional r, Ord r, RootHalfRing r, Quadratic QRootTwo r) => DRootTwo -> ConvexSet r
disk s = ConvexSet ell tst int where
  ell = Ellipse (1/fromDRootTwo s `scalarmult` 1) (0,0)

  int p v
    | q == Nothing         = Nothing
    | otherwise            = Just (t0, t1)
    where
      a = iprod v v
      b = 2 * iprod v p
      c = iprod p p - s
      q = quadratic (fromDRootTwo a :: QRootTwo) (fromDRootTwo b) (fromDRootTwo c)
      Just (t0, t1) = q
    
  tst (x,y) = x^2 + y^2 <= s

-- | A closed rectangle with the given dimensions.
rectangle :: (Fractional r, Ord r, RootHalfRing r) => (r,r) -> (r,r) -> ConvexSet r
rectangle (x0,x1) (y0,y1) = ConvexSet ell tst int where
  w = x1-x0
  h = y1-y0
  center = ((x0+x1) / 2, (y0+y1) / 2)
  mat = toOperator ((2/w^2,0), (0,2/h^2))
  ell = Ellipse mat center
  tst (x, y) = (fromDRootTwo x `within` (x0, x1)) && (fromDRootTwo y `within` (y0, y1))
  int p v = int_internal (point_fromDRootTwo p) (point_fromDRootTwo v)
  int_internal p v
    | vx == 0 && px `within` (x0, x1) = Just (min t0y t1y, max t0y t1y)
    | vx == 0 = Nothing
    | vy == 0 && py `within` (y0, y1) = Just (min t0x t1x, max t0x t1x)
    | vy == 0 = Nothing
    | otherwise = Just (t0, t1)
    where
      (px, py) = p
      (vx, vy) = v
      t0x = (x0 - px) / vx
      t1x = (x1 - px) / vx
      t0y = (y0 - py) / vy
      t1y = (y1 - py) / vy
      t0 = max (min t0x t1x) (min t0y t1y)
      t1 = min (max t0x t1x) (max t0y t1y)

-- ----------------------------------------------------------------------
-- ** General solutions

-- | Given bounded convex sets /A/ and /B/, enumerate all solutions
-- /u/ ∈ ℤ[ω] of the 2-dimensional grid problem for /A/ and /B/.
gridpoints2 :: (RealFrac r, Floating r, Ord r, RootTwoRing r, RootHalfRing r, Adjoint r, Floor r) => ConvexSet r -> ConvexSet r -> [DOmega]
gridpoints2 setA setB = gridpoints2_scaled setA setB 0

-- ----------------------------------------------------------------------
-- ** Scaled solutions

-- $ The scaled version of the 2-dimensional grid problem is the
-- following: given bounded convex subsets /A/ and /B/ of ℂ with
-- non-empty interior, and /k/ ≥ 0, find all /u/ ∈ ℤ[ω] \/ √2[sup /k/]
-- such that /u/ ∈ /A/ and /u/[sup •] ∈ /B/.

-- | Given bounded convex sets /A/ and /B/, return a function that can
-- input a /k/ and enumerate all solutions of the two-dimensional
-- scaled grid problem for /A/, /B/, and /k/.
-- 
-- Note: a large amount of precomputation is done on the sets /A/ and
-- /B/, so it is beneficial to call this function only once for a
-- given pair of sets, and then possibly call the result many times
-- for different /k/. In other words, for optimal performance, the
-- function should be used like this:
-- 
-- > let solver = gridpoints2_scaled setA setB
-- > let solutions0 = solver 0
-- > let solutions1 = solver 1
-- > ...
-- 
-- Note: the gridpoints are computed in some deterministic (but
-- unspecified) order. They are not randomized.
gridpoints2_scaled :: (RealFrac r, Floating r, Ord r, RootTwoRing r, RootHalfRing r, Adjoint r, Floor r) => ConvexSet r -> ConvexSet r -> Integer -> [DOmega]
gridpoints2_scaled setA setB = gridpoints2_scaled_with_gridop setA setB opG
  where
    opG = to_upright_sets setA setB

-- | Like 'gridpoints2_scaled', except that instead of performing a
-- precomputation, we input the desired grid operator. It must make
-- the two given sets upright.
gridpoints2_scaled_with_gridop :: (RealFrac r, Floating r, Ord r, RootTwoRing r, RootHalfRing r, Adjoint r, Floor r) => ConvexSet r -> ConvexSet r -> Operator DRootTwo -> Integer -> [DOmega]
gridpoints2_scaled_with_gridop setA setB opG = solutions_fun
  where
    ConvexSet ellA tstA intA = setA
    ConvexSet ellB tstB intB = setB
    
    -- Find the grid operator
    opG_inv = special_inverse opG
    
    -- Change the coordinate system
    setA' = convex_transform opG_inv setA
    setB' = convex_transform (adj2 opG_inv) setB
    bboxA' = boundingbox setA'
    bboxB' = boundingbox setB'
    ConvexSet ellA' tstA' intA' = setA'
    ConvexSet ellB' tstB' intB' = setB'
    ((x0A, x1A), (y0A, y1A)) = bboxA'
    ((x0B, x1B), (y0B, y1B)) = bboxB'
    
    solutions_fun k = do
      
      -- Enumerate the solutions in the y-coordinate
      beta' <- gridpoints_scaled (fatten_interval (y0A, y1A)) (fatten_interval (y0B, y1B)) (k+1)
      let beta'_bul = adj2 beta'
      
      let xs = gridpoints_scaled (x0A, x1A+lambda) (x0B, x1B+lambda) (k+1)
      x0 <- take 1 xs
      let x0_bul = adj2 x0
      let dx = roothalf^k
      let dx_bul = adj2 dx
      
      -- Intersect that y-coordinate with the convex sets
      let iA = intA' (x0, beta') (dx, 0)
      let iB = intB' (x0_bul, beta'_bul) (dx_bul, 0)
      guard (isJust iA)
      guard (isJust iB)
      let Just (t0A, t1A) = iA
      let Just (t0B, t1B) = iB
      
      -- offsets for slightly fattening the intervals, in a way that
      -- does not add more than a small constant number of candidates
      -- alpha' on both sides of the interval.
      let dtA = 10 / max 10 (2^k * (t1B - t0B))
      let dtB = 10 / max 10 (2^k * (t1A - t0A))

      -- Enumerate the solutions in the x-coordinate (ensuring correct
      -- parity to make sure it's a grid point)
      -- 
      -- For parity, we need: 
      --          1/√2^k | alpha' - beta'
      --      <=> 1/√2^k | alpha'_offs * dx + x0 - beta'
      --      <=> 1 | alpha'_offs + (x0 - beta') * √2^k
      alpha'_offs <- gridpoints_scaled_parity ((beta'-x0)*roottwo^k) (t0A-dtA, t1A+dtA) (t0B-dtB, t1B+dtB) 1
      let alpha' = alpha'_offs * dx + x0

      -- Convert back to the original coordinate system
      let (alpha,beta) = point_transform opG (alpha',beta')
      
      case tstA (alpha,beta) && tstB (adj2 alpha, adj2 beta) of
        True -> do
          let z = fromDRootTwo alpha + i * fromDRootTwo beta :: DOmega
          return z
        False -> do
          []

-- | Given bounded convex sets /A/ and /B/, enumerate all solutions of
-- the two-dimensional scaled grid problem for all /k/ ≥ 0. Each
-- solution is only enumerated once, and the solutions are enumerated
-- in order of increasing /k/. The results are returned in the form
-- 
-- > [ (0, l0), (1, l1), (2, l2), ... ],
-- 
-- where /l0/ is a list of solutions for /k/=0, /l1/ is a list of
-- solutions for /k/=1, and so on.
gridpoints2_increasing :: (RealFrac r, Floating r, Ord r, RootTwoRing r, RootHalfRing r, Adjoint r, Floor r) => ConvexSet r -> ConvexSet r -> [(Integer, [DOmega])]
gridpoints2_increasing setA setB = gridpoints2_increasing_with_gridop setA setB opG
  where
    opG = to_upright_sets setA setB

-- | Like 'gridpoints2_increasing', except that instead of performing
-- a precomputation, we input the desired grid operator. It must make
-- the two given sets upright.
gridpoints2_increasing_with_gridop :: (RealFrac r, Floating r, Ord r, RootTwoRing r, RootHalfRing r, Adjoint r, Floor r) => ConvexSet r -> ConvexSet r -> Operator DRootTwo -> [(Integer, [DOmega])]
gridpoints2_increasing_with_gridop setA setB opG = solutions 
  where
    solutions_fun = gridpoints2_scaled_with_gridop setA setB opG
    solutions = (0, solutions_fun 0) : additional_solutions 1
    additional_solutions k = (k, exact_solutions k) : additional_solutions (k+1)
    exact_solutions k = [ z | z <- solutions_fun k, denomexp z == k ]

-- ----------------------------------------------------------------------
-- * Implementation details

-- ----------------------------------------------------------------------
-- ** One-dimensional grid problems

-- | Similar to 'gridpoints', except:
-- 
-- 1. Assume that /x0/ and /y0/ are not too far from the origin (say,
-- between -10 and 10). This is to avoid problems with numeric
-- instability when /x0/ and /y0/ are much larger than /dx/ and /dy/,
-- respectively.
-- 
-- 2. The function potentially returns some non-solutions, so the
-- caller should test for accuracy.
gridpoints_internal :: (RootTwoRing r, Fractional r, Floor r, Ord r) => (r, r) -> (r, r) -> [ZRootTwo]
gridpoints_internal (x0, x1) (y0, y1)
  | dy <= 0 && dx > 0 = 
        map adj2 $ gridpoints_internal (y0, y1) (x0, x1)
  | dy >= lambda && even n =
        map (lambda_inv_n *) $ gridpoints_internal (lambda_n*x0, lambda_n*x1) (lambda_bul_n*y0, lambda_bul_n*y1)
  | dy >= lambda && odd n =
        map (lambda_inv_n *) $ gridpoints_internal (lambda_n*x0, lambda_n*x1) (lambda_bul_n*y1, lambda_bul_n*y0)
  | dy > 0 && dy < 1 && even n = 
        map (lambda_m *) $ gridpoints_internal (lambda_inv_m*x0, lambda_inv_m*x1) (lambda_bul_inv_m*y0, lambda_bul_inv_m*y1)
  | dy > 0 && dy < 1 && odd n = 
        map (lambda_m *) $ gridpoints_internal (lambda_inv_m*x0, lambda_inv_m*x1) (lambda_bul_inv_m*y1, lambda_bul_inv_m*y0)
  | otherwise =
        [ RootTwo a b | a <- [amin..amax], b <- [bmin a..bmax a] ] 
  where
    dx = x1 - x0
    dy = y1 - y0
    (n, _) = floorlog lambda dy
    m = -n
    
    lambda_m = lambda^m
    lambda_n = lambda^n
    lambda_bul_n = (-lambda_inv)^n
    lambda_inv_m = lambda_inv^m
    lambda_bul_inv_m = (-lambda)^m
    lambda_inv_n = lambda_inv^n

    within x (x0, x1) = x0 <= x && x <= x1
    amin = ceiling_of ((x0 + y0) / 2)
    amax = floor_of ((x1 + y1) / 2)
    bmin a = ceiling_of ((fromInteger a - y1) / roottwo)
    bmax a = floor_of ((fromInteger a - y0) / roottwo)

-- ----------------------------------------------------------------------
-- ** Two-dimensional grid problems

-- $ Our solution of the 2-dimensional grid problem follows the paper
-- 
-- * N. J. Ross and P. Selinger, \"Optimal ancilla-free Clifford+/T/
-- approximation of /z/-rotations\". <http://arxiv.org/abs/1403.2975>.

-- ----------------------------------------------------------------------
-- *** Positive operators and ellipses

-- | Construct a 2×2-matrix, by rows.
toOperator :: ((a, a), (a, a)) -> Operator a
toOperator ((a, b), (c, d)) = matrix2x2 (a,b) (c,d)

-- | Extract the entries of a 2×2-matrix, by rows.
fromOperator :: Operator a -> ((a, a), (a, a))
fromOperator m = from_matrix2x2 m

-- | Convert an operator with entries in 'DRootTwo' to an operator with
-- entries in any 'RootHalfRing'.
op_fromDRootTwo :: (RootHalfRing r) => Operator DRootTwo -> Operator r
op_fromDRootTwo m = matrix_map fromDRootTwo m

-- | The (/b/,/z/)-representation of a positive operator with determinant 1 is
-- 
-- \[image bz.png]
-- 
-- where /b/, /z/ ∈ ℝ and /e/ > 0 with /e/² = /b/² + 1. Create such an
-- operator from parameters /b/ and /z/.
operator_from_bz :: (RootTwoRing a, Floating a) => a -> a -> Operator a
operator_from_bz b z = toOperator ((a, b), (b, d)) where
  lambda_z = lambda**z
  a = e/lambda_z
  d = e*lambda_z
  e = sqrt(1 + b^2)

-- | Conversely, given a positive definite real operator of
-- determinant 1, return the parameters (/b/, /z/). This is the
-- inverse of 'operator_from_bz'. For efficiency reasons, the
-- parameter /z/, which is a logarithm, is modeled as a 'Double'.
operator_to_bz :: (Fractional a, Real a, RootTwoRing a) => Operator a -> (a, Double)
operator_to_bz m = (b, z) where
  ((a, b), (c, d)) = fromOperator m
  lambda_z_squared = d / a
  z = 0.5 * logBase_double lambda lambda_z_squared
  
-- | A version of 'operator_to_bz' that returns (/b/, λ[sup 2/z/])
-- instead of (/b/, /z/).
-- This is a critical optimization, as this function is called often,
-- and logarithms are relatively expensive to compute.
operator_to_bl2z :: (Floating a, Real a) => Operator a -> (a, a)
operator_to_bl2z m = (b, l2z) where
  ((a, b), (c, d)) = fromOperator m
  l2z = d / a
  
-- | The determinant of a 2×2-matrix.
det :: (Ring a) => Operator a -> a
det m = a*d - b*c where
  ((a, b), (c, d)) = fromOperator m

-- | Compute the skew of a positive operator of determinant 1.  We
-- define the /skew/ of a positive definite real operator /D/ to be
-- 
-- \[image skew.png]
operator_skew :: (Ring a) => Operator a -> a
operator_skew m = b*c where
  ((a, b), (c, d)) = fromOperator m
  
-- | Compute the uprightness of a positive operator /D/. 
-- 
-- The /uprightness/ of /D/ is the ratio of the area of the ellipse
-- /E/ = {/v/ | /v/[sup †]/D//v/ ≤ 1} to the area of its bounding box
-- /R/. It is given by
-- 
-- \[image area.png]
--   
-- \[image ellipse-rectangle.png]
uprightness :: (Floating a) => Operator a -> a
uprightness m = pi/4 * sqrt(det m / (a*d))
  where
    ((a, b), (c, d)) = fromOperator m

-- ----------------------------------------------------------------------
-- *** States

-- | A state is a pair (/D/, Δ) of real positive definite matrices of
-- determinant 1. It encodes a pair of ellipses.
type OperatorPair a = (Operator a, Operator a)

-- | The /skew/ of a state is the sum of the skews of the two
-- operators.
skew :: (Ring a) => OperatorPair a -> a
skew (m1,m2) = operator_skew m1 + operator_skew m2

-- | The /bias/ of a state is ζ - /z/.
bias :: (Fractional a, Real a, RootTwoRing a) => OperatorPair a -> Double
bias (matA,matB) = (zeta - z) where
    (b, z) = operator_to_bz matA
    (beta, zeta) = operator_to_bz matB

-- ----------------------------------------------------------------------
-- *** Grid operators
    
-- $ Consider the set ℤ[ω] ⊆ ℂ. In identifying ℂ with ℝ², we can
-- alternatively identify ℤ[ω] with the set of all vectors (/x/,
-- /y/)[sup †] ∈ ℝ² of the form
-- 
-- * /x/ = /a/ + /a/'\/√2,
--
-- * /y/ = /b/ + /b/'\/√2,
-- 
-- such that /a/, /a/', /b/, /b/' ∈ ℤ and /a/' ≡ /b/' (mod 2).
--
-- A /grid operator/ is a linear operator /G/ : ℝ² → ℝ² such that /G/
-- maps ℤ[ω] to itself.  We can characterize the grid operators as
-- the operators of the form 
-- 
-- \[image gridop.png]
-- 
-- such that:
-- 
-- * /a/ + /b/ + /c/ + /d/ ≡ 0 (mod 2) and
-- 
-- * /a/' ≡ /b/' ≡ /c/' ≡ /d/' (mod 2).
-- 
-- A /special grid operator/ is a grid operator of determinant ±1. All
-- special grid operators are invertible, and the inverse is again a
-- special grid operator.
-- 
-- Since all coordinates of ℤ[ω] (as a subset of ℝ²), and all entries
-- of grid operators, can be represented as elements of the ring [bold
-- D][√2], the automorphism /x/ ↦ /x/[sup •], which maps /a/ + /b/√2
-- to /a/ - /b/√2 (for rational /a/ and /b/), is well-defined for
-- them.
--     
-- In this section, we define some particular special grid operators
-- that are used in the Step Lemma.

-- | The special grid operator /R/: a clockwise rotation by 45°.
-- 
-- \[image gridop-R.png]
opR :: (RootHalfRing r) => Operator r
opR = roothalf * toOperator ((1, -1), (1, 1))

-- | The special grid operator /A/: a clockwise shearing with offset
-- 2, parallel to the /x/-axis.
-- 
-- \[image gridop-A.png]
opA :: (Ring r) => Operator r
opA = matrix2x2 (1, -2) (0, 1)

-- | The special grid operator /A/⁻¹: a counterclockwise shearing with offset
-- 2, parallel to the /x/-axis.
-- 
-- \[image gridop-Ai.png]
opA_inv :: (Ring r) => Operator r
opA_inv = matrix2x2 (1, 2) (0, 1)

-- | The operator /A/[sup /k/].
opA_power :: (RootTwoRing r) => Integer -> Operator r
opA_power k 
  | k >= 0    = opA^k
  | otherwise = opA_inv^(-k)

-- | The special grid operator /B/: a clockwise shearing with offset
-- √2, parallel to the /x/-axis.
-- 
-- \[image gridop-B.png]
opB :: (RootTwoRing r) => Operator r
opB = matrix2x2 (1, roottwo) (0, 1)

-- | The special grid operator /B/⁻¹: a counterclockwise shearing with offset
-- √2, parallel to the /x/-axis.
-- 
-- \[image gridop-Bi.png]
opB_inv :: (RootTwoRing r) => Operator r
opB_inv = matrix2x2 (1, -roottwo) (0, 1)

-- | The operator /B/[sup /k/].
opB_power :: (RootTwoRing r) => Integer -> Operator r
opB_power k 
  | k >= 0    = opB^k
  | otherwise = opB_inv^(-k)

-- | The special grid operator /K/.
-- 
-- \[image gridop-K.png]
opK :: (RootHalfRing r) => Operator r
opK = roothalf * matrix2x2 (-lambda_inv, -1) (lambda, 1)

-- | The Pauli /X/ operator is a special grid operator. 
-- 
-- \[image gridop-X.png]
opX :: (Ring r) => Operator r
opX = matrix2x2 (0, 1) (1, 0)

-- | The Pauli operator /Z/ is a special grid operator.
-- 
-- \[image gridop-Z.png]
opZ :: (Ring r) => Operator r
opZ = matrix2x2 (1, 0) (0, -1)

-- | The special grid operator /S/: a scaling by λ = 1+√2 in the
-- /x/-direction, and by λ⁻¹ = -1+√2 in the /y/-direction.
-- 
-- \[image gridop-S.png]
-- 
-- The operator /S/ is not used in the paper, but we use it here for
-- a more efficient implementation of large shifts. The point is that
-- /S/ is a grid operator, but shifts in increments of 4, whereas the
-- Shift Lemma uses non-grid operators but shifts in increments of 2.
opS :: (RootTwoRing r) => Operator r
opS = toOperator((lambda, 0), (0, lambda_inv))

-- | The special grid operator /S/⁻¹, the inverse of 'opS'.
-- 
-- \[image gridop-Si.png]
opS_inv :: (RootTwoRing r) => Operator r
opS_inv = matrix2x2 (lambda_inv, 0) (0, lambda)

-- | Return /S/[sup /k/].
opS_power :: (RootTwoRing r) => Integer -> Operator r
opS_power k 
  | k >= 0    = opS^k
  | otherwise = opS_inv^(-k)

-- ----------------------------------------------------------------------
-- *** Action of grid operators on states

-- | Compute the right action of a grid operator /G/ on a state (/D/,
-- Δ). This is defined as:
-- 
-- (/D/, Δ) ⋅ /G/  :=  (/G/[sup †]/D//G/, /G/[sup •T]Δ/G/[sup •]).
action :: (RealFrac r, RootHalfRing r, Adjoint r) => (Operator r, Operator r) -> Operator DRootTwo -> (Operator r, Operator r)
action (a,b) g = (g1 * a * g2, g3 * b * g4) where
  g1 = adj g2
  g2 = op_fromDRootTwo g
  g3 = adj g4
  g4 = op_fromDRootTwo (adj2 g)

-- ----------------------------------------------------------------------
-- *** Shifts
  
-- $ A shift is not quite the application of a grid operator, because
-- the shifts σ and τ actually involve a square root of λ. However,
-- they can be used to define an operation on states.
  
-- | Given an operator /D/, compute σ[sup /k/]/D/σ[sup /k/].
shift_sigma :: (RootTwoRing a) => Integer -> Operator a -> Operator a
shift_sigma k m = matrix2x2 (lambdapower k * a, b) (c, lambdapower (-k) * d) where
  ((a,b),(c,d)) = fromOperator m

-- | Given an operator Δ, compute τ[sup /k/]Δτ[sup /k/].
shift_tau :: (RootTwoRing a) => Integer -> Operator a -> Operator a
shift_tau k m = matrix2x2 (lambdapower (-k) * a, signpower k * b) (c * signpower k, lambdapower k * d) where
  ((a,b),(c,d)) = fromOperator m

-- | Compute the /k/-shift of a state (/D/,Δ).
shift_state :: (RootTwoRing a) => Integer -> OperatorPair a -> OperatorPair a
shift_state k (d,delta) = (shift_sigma k d, shift_tau k delta)

-- ----------------------------------------------------------------------
-- *** Skew reduction

-- | An implementation of the /A/-Lemma. Given /z/ and ζ, compute the
-- integer /m/ such that the operator /A/[sup /m/] reduces the skew.
lemma_A :: (RealFrac r, RootTwoRing r, Floating r) => r -> r -> Integer
lemma_A z zeta = n where
  n = max 1 (floor (lambda ** c / 2))
  c = min z zeta

-- | An implementation of the /B/-Lemma. Given /z/ and ζ, compute the
-- integer /m/ such that the operator /B/[sup /m/] reduces the skew.
lemma_B :: (RealFrac r, RootTwoRing r, Floating r) => r -> r -> Integer
lemma_B z zeta = n where
  n = max 1 (floor (lambda ** c / roottwo))
  c = min z zeta

-- | A version of 'lemma_A' that inputs λ[sup 2/z/] instead of /z/ and
-- λ[sup 2ζ] instead of ζ. Compute the constant /m/ such that the
-- operator /A/[sup /m/] reduces the skew.
lemma_A_l2 :: (RealFrac r, RootTwoRing r, Floating r) => r -> r -> Integer
lemma_A_l2 l2z l2zeta = n where
  n = max 1 (intsqrt (floor (l2c / 4)))
  l2c = min l2z l2zeta

-- | A version of 'lemma_B' that inputs λ[sup 2/z/] instead of /z/ and
-- λ[sup 2ζ] instead of ζ. Compute the constant /m/ such that the
-- operator /B/[sup /m/] reduces the skew.
lemma_B_l2 :: (RealFrac r, RootTwoRing r, Floating r) => r -> r -> Integer
lemma_B_l2 l2z l2zeta = n where
  n = max 1 (intsqrt (floor (l2c / 2)))
  l2c = min l2z l2zeta

-- | An implementation of the Step Lemma. Input a state (/D/,Δ). If
-- the skew is > 15, produce a special grid operator whose action
-- reduces Skew(/D/,Δ) by at least 5%. If the skew is ≤ 15 and β ≥ 0
-- and z + ζ ≥ 0, do nothing. Otherwise, produce a special grid
-- operator that ensures β ≥ 0 and z + ζ ≥ 0.
step_lemma :: (RealFrac r, Floating r, Ord r, RootTwoRing r, RootHalfRing r, Adjoint r) => OperatorPair r -> Maybe (Operator DRootTwo)
step_lemma (matA,matB)
  -- First ensure that β ≥ 0, by applying /Z/ if necessary.
  | beta < 0
    = wlog_using opZ
      
  -- Then ensure that z + ζ ≥ 0, by applying /X/ if necessary.
  -- Case: z + zeta < 0.
  | l2z * l2zeta < 1   
    = wlog_using opX

  -- If the bias is greater than 2, use the grid operator /S/. This is
  -- more efficient than applying the Shift Lemma.
  -- Todo: ensure numeric stability
  -- Case: |z-ζ| > 2.
  | l2z_minus_zeta > 33.971 || l2z_minus_zeta < 0.029437
    = wlog_using (opS_power (round (logLambda l2z_minus_zeta / 8)))

  -- If the skew is below threshold, stop.
  | skew (matA,matB) <= 15
    = Nothing
  
  -- If the bias is greater than 1, apply a shift.
  -- Todo: ensure numeric stability
  -- Case: |z-ζ| > 1.
  | l2z_minus_zeta > 5.8285 || l2z_minus_zeta < 0.17157
    = with_shift (round (logLambda l2z_minus_zeta / 4))

  -- Cases 1.1 and 2.1: z ∈ [-0.8, 0.8] and ζ ∈ [-0.8, 0.8].
  -- Region R.
  | l2z `within` (0.24410, 4.0968) && l2zeta `within` (0.24410, 4.0968)
    = Just opR

  -- Case 1.2: b ≥ 0 and z ≤ 0.3 and ζ ≥ 0.8.
  -- Region K.
  | b >= 0 && l2z <= 1.6969
    = Just opK
     
  -- Case 1.4: b ≥ 0 and z ≥ 0.8 and ζ ≤ 0.3.
  -- Region K•.
  | b >= 0 && l2zeta <= 1.6969
    = Just (adj2 opK)
     
  -- Case 1.6: b ≥ 0 and z ≥ 0.3 and zeta ≥ 0.3.
  -- Region A^m.
  | b >= 0
    = Just (opA_power (lemma_A_l2 l2z l2zeta))

  -- Case 2.2: b ≤ 0 and z ≥ -0.2 and zeta ≥ -0.2.
  -- Region B^m.
  | otherwise
    = Just (opB_power (lemma_B_l2 l2z l2zeta))
      
  where
    (b, l2z) = operator_to_bl2z matA
    (beta, l2zeta) = operator_to_bl2z matB

    logLambda a = logBase_double lambda a
    l2z_minus_zeta = l2z / l2zeta  -- λ[sup 2(/z/-ζ)]

    wlog_using op =
      let (matA',matB') = action (matA, matB) op
          maybe_op2 = step_lemma (matA',matB')
      in
       case maybe_op2 of
         Nothing -> Just op
         Just op2 -> Just (op * op2)

    with_shift k =
      let (matA', matB') = shift_state k (matA, matB)
          maybe_op2 = step_lemma (matA', matB')
      in
       case maybe_op2 of
         Nothing -> Nothing
         Just op2 -> Just (shift_sigma k op2)

-- | Repeatedly apply the Step Lemma to the given state, until the
-- skew is 15 or less.
reduction :: (RealFrac r, Floating r, Ord r, RootTwoRing r, RootHalfRing r, Adjoint r) => OperatorPair r -> Operator DRootTwo
reduction st = 
  case step_lemma st of
    Nothing -> 1
    Just opG -> opG * opG'
      where
        opG' = reduction (action st opG)
      
-- | Given a pair of ellipses, return a grid operator /G/ such that
-- the uprightness of each ellipse is greater than 1\/6. This is
-- essentially the same as 'reduction', except we do not assume that
-- the input operators have determinant 1.
to_upright :: (RealFrac r, Floating r, Ord r, RootTwoRing r, RootHalfRing r, Adjoint r) => OperatorPair r -> Operator DRootTwo
to_upright (a,b) = opG
    where
      a' = a `scalardiv` (sqrt (det a))
      b' = b `scalardiv` (sqrt (det b))
      opG = reduction (a',b')

-- | Given a pair of convex sets, return a grid operator /G/ making
-- both sets upright.
to_upright_sets :: (Adjoint r, RootHalfRing r, RealFrac r, Floating r) => ConvexSet r -> ConvexSet r -> Operator DRootTwo
to_upright_sets setA setB = opG where
    ConvexSet ellA tstA intA = setA
    ConvexSet ellB tstB intB = setB
    Ellipse matA ctrA = ellA
    Ellipse matB ctrB = ellB
    
    opG = to_upright (matA, matB)
  
-- ----------------------------------------------------------------------
-- *** Action of special grid operators on convex sets

-- | Apply a linear transformation /G/ to a point /p/.
point_transform :: (Ring r) => Operator r -> Point r -> Point r
point_transform opG (x,y) = (x',y') where
  ((a,b), (c,d)) = fromOperator opG
  x' = a * x + b * y
  y' = c * x + d * y

-- | Apply a special linear transformation /G/ to an ellipse /A/. This
-- results in the new ellipse /G/(/A/) = { /G/(/z/) | /z/ ∈ /A/ }.
ellipse_transform :: (Ring r, Adjoint r) => Operator r -> Ellipse r -> Ellipse r
ellipse_transform opG (Ellipse matA ctrA) = (Ellipse matA' ctrA') where
  matA' = adj opG_inv * matA * opG_inv
  ctrA' = point_transform opG ctrA
  opG_inv = special_inverse opG

-- | Apply a special grid operator /G/ to a characteristic function.
charfun_transform :: Operator DRootTwo -> CharFun -> CharFun
charfun_transform opG f = f' where
  f' p = f (point_transform opG_inv p)
  opG_inv = special_inverse opG

-- | Apply a special linear transformation /G/ to a line
-- intersector. If the input line intersector was for a convex set
-- /A/, then the output line intersector is for the set /G/(/A/) 
-- = { /G/(/z/) | /z/ ∈ /A/ }.
lineintersector_transform :: (Ring r) => Operator DRootTwo -> LineIntersector r -> LineIntersector r
lineintersector_transform opG intA = intA' 
  where
    opG_inv = special_inverse opG
    intA' v' w' = intA v w
      where 
        v = point_transform opG_inv v'
        w = point_transform opG_inv w'

-- | Apply a special linear transformation /G/ to a convex set
-- /A/. This results in the new convex set /G/(/A/) = { /G/(/z/) | /z/
-- ∈ /A/ }.
convex_transform :: (Ring r, Adjoint r, RootHalfRing r) => Operator DRootTwo -> ConvexSet r -> ConvexSet r
convex_transform opG (ConvexSet ellA tstA intA) = (ConvexSet ellA' tstA' intA') where
  ellA' = ellipse_transform (op_fromDRootTwo opG) ellA
  intA' = lineintersector_transform (op_fromDRootTwo opG) intA
  tstA' = charfun_transform opG tstA

-- ----------------------------------------------------------------------
-- *** Bounding boxes
      
-- | Calculate the bounding box for an ellipse.
boundingbox_ellipse :: (Floating r) => Ellipse r -> ((r, r), (r, r))
boundingbox_ellipse (Ellipse matA ctrA) = ((x-w, x+w), (y-h, y+h)) where
  (x,y) = ctrA
  ((a, b), (c, d)) = fromOperator matA
  w = sqrt d / sqrt_det
  h = sqrt a / sqrt_det
  sqrt_det = sqrt (det matA)

-- | Calculate a bounding box for a convex set. Returns ((/x/₀, /x/₁),
-- (/y/₀, /y/₁)).
boundingbox :: (Floating r) => ConvexSet r -> ((r, r), (r, r))
boundingbox (ConvexSet ell tst int) = boundingbox_ellipse ell

-- ----------------------------------------------------------------------
-- * Auxiliary functions

-- | We write /x/ \`@within@\` (/a/,/b/) for /a/ ≤ /x/ ≤ /b/, or
-- equivalently, /x/ ∈ [/a/, /b/].
within :: (Ord a) => a -> (a,a) -> Bool
within x (a,b) = a <= x && x <= b

-- | Given an interval, return a slightly bigger one.
fatten_interval :: (Fractional a) => (a,a) -> (a,a)
fatten_interval (x,y) = (x - epsilon, y + epsilon) where
  epsilon = 0.0001 * (y-x)

-- | The constant λ = 1 + √2.
lambda :: (RootTwoRing r) => r
lambda = 1 + roottwo

-- | The constant λ⁻¹ = √2 - 1.
lambda_inv :: (RootTwoRing r) => r
lambda_inv = roottwo - 1

-- | Return λ[sup /k/], where /k/ ∈ ℤ. This works in any 'RootTwoRing'.
-- 
-- Note that we can't use '^', because it requires /k/ ≥ 0, nor '**',
-- because it requires the 'Floating' class.
lambdapower :: (RootTwoRing r) => Integer -> r
lambdapower k
  | k >= 0 = lambda^k
  | otherwise = lambda_inv^(-k)

-- | Return (-1)[sup /k/], where /k/ ∈ ℤ.
signpower :: (Num r) => Integer -> r
signpower k
  | even k    = 1
  | otherwise = -1

-- | Given positive numbers /b/ and /x/, return (/n/, /r/) such that
-- 
-- * /x/ = /r/ /b/[sup /n/] and                           
--                                   
-- * 1 ≤ /r/ < /b/.                                  
--                                   
-- In other words, let /n/ = ⌊log[sub /b/] /x/⌋ and 
-- /r/ = /x/ /b/[sup −/n/]. This can be more efficient than 'floor'
-- ('logBase' /b/ /x/) depending on the type; moreover, it also works
-- for exact types such as 'Rational' and 'QRootTwo'.
floorlog :: (Fractional b, Ord b) => b -> b -> (Integer, b)
floorlog b x 
    | x <= 0            = error "floorlog: argument not positive"    
    | 1 <= x && x < b   = (0, x)
    | 1 <= x*b && x < 1 = (-1, b*x)
    | r < b             = (2*n, r)
    | otherwise         = (2*n+1, r/b)
    where
      (n, r) = floorlog (b^2) x

-- | A version of the natural logarithm that returns a 'Double'. The
-- logarithm of just about any value can fit into a 'Double'; so if
-- not a lot of precision is required in the mantissa, this function
-- is often faster than 'log'.
logBase_double :: (Fractional a, Real a) => a -> a -> Double
logBase_double b x 
  | b > 1  = y 
  | b <= 0 = 0/0 -- NaN
  | b == 1 = 1/0 -- Infinity
  | otherwise = - logBase_double (1/b) x
  where
    (n, r) = floorlog b x
    y = fromInteger n + logBase (to_double b) (to_double r)
    to_double = fromRational . toRational

-- | The inner product of two points.
iprod :: (Num r) => Point r -> Point r -> r
iprod (x,y) (a,b) = x*a + y*b

-- | Subtract two points.
point_sub :: (Num r) => Point r -> Point r -> Point r
point_sub (x,y) (a,b) = (x-a, y-b)

-- | Calculute the inverse of an operator of determinant 1. Note: this
-- does not work correctly for operators whose determinant is not 1.
special_inverse :: (Ring r) => Operator r -> Operator r
special_inverse opG = opG_inv where
  ((a,b), (c,d)) = fromOperator opG
  opG_inv = det opG `scalarmult` toOperator ((d,-b), (-c,a))

