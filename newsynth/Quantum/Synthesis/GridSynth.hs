{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}

-- | This module implements the approximate single-qubit synthesis
-- algorithm of
-- 
-- * N. J. Ross and P. Selinger, \"Optimal ancilla-free Clifford+/T/
-- approximation of /z/-rotations\". <http://arxiv.org/abs/1403.2975>.
-- 
-- The algorithm is near-optimal in the following sense: it produces
-- an operator whose expected /T/-count exceeds the /T/-count of the
-- second-to-optimal solution to the approximate synthesis problem by
-- at most /O/(log(log(1/ε))).

module Quantum.Synthesis.GridSynth where

import Quantum.Synthesis.Ring
import Quantum.Synthesis.Ring.FixedPrec()
import Quantum.Synthesis.Matrix
import Quantum.Synthesis.CliffordT
import Quantum.Synthesis.SymReal
import Quantum.Synthesis.GridProblems
import Quantum.Synthesis.Diophantine
import Quantum.Synthesis.StepComp
import Quantum.Synthesis.QuadraticEquation

import System.Random
import Data.Function

-- ----------------------------------------------------------------------
-- * Approximate synthesis

-- ----------------------------------------------------------------------
-- ** User-friendly functions

-- | Output a unitary operator in the Clifford+/T/ group that
-- approximates /R/[sub /z/](θ) = [exp −/i/θ/Z/\/2] to within ε in the
-- operator norm. This operator can then be converted to a list of
-- gates with 'to_gates'.
-- 
-- The parameters are:
-- 
-- * a source of randomness /g/;
-- 
-- * the angle θ;
--   
-- * the precision /b/ ≥ 0 in bits, such that ε = 2[sup -/b/];
-- 
-- * an integer that determines the amount of \"effort\" to put into
-- factoring. A larger number means more time spent on factoring. 
-- A good default for this is 25.
-- 
-- Note: the argument /theta/ is given as a symbolic real number. It
-- will automatically be expanded to as many digits as are necessary
-- for the internal calculation. In this way, the caller can specify,
-- e.g., an angle of pi\/128 @::@ 'SymReal', without having to worry
-- about how many digits of π to specify.
gridsynth :: (RandomGen g) => g -> Double -> SymReal -> Int -> U2 DOmega
gridsynth g prec theta effort = m where
  (m, _, _) = gridsynth_stats g prec theta effort

-- | A version of 'gridsynth' that returns a list of gates instead of a
-- matrix.
-- 
-- Note: the list of gates will be returned in right-to-left order,
-- i.e., as in the mathematical notation for matrix multiplication.
-- This is the opposite of the quantum circuit notation.
gridsynth_gates :: (RandomGen g) => g -> Double -> SymReal -> Int -> [Gate]
gridsynth_gates g prec theta effort = synthesis_u2 (gridsynth g prec theta effort)
    
-- | Information about the status of an attempt to solve a Diophantine
-- equation. 'Success' means the Diophantine equation was solved;
-- 'Fail' means that it was proved that there was no solution;
-- 'Timeout' means that the question was not decided within the
-- allotted time.
data DStatus = Success | Fail | Timeout
             deriving (Eq, Show)
                                
-- | A version of 'gridsynth' that also returns some statistics:
-- log[sub 0.5] of the actual approximation error (or 'Nothing' if the
-- error is 0), and a data structure with information on the
-- candidates tried.
gridsynth_stats :: (RandomGen g) => g -> Double -> SymReal -> Int -> (U2 DOmega, Maybe Double, [(DOmega, Integer, DStatus)])
gridsynth_stats g prec theta effort = dynamic_fixedprec2 digits f prec theta where
  digits = ceiling (15 + 2.5 * prec * logBase 10 2) -- heuristic formula!
  f prec theta = gridsynth_internal g prec theta effort
        
-- | A version of 'gridsynth_stats' that returns the optimal operator
-- /up to a global phase/.  (The default behavior is to return the
-- optimal operator exactly).
gridsynth_phase_stats :: (RandomGen g) => g -> Double -> SymReal -> Int -> (U2 DOmega, Maybe Double, [(DOmega, Integer, DStatus)])
gridsynth_phase_stats g prec theta effort = dynamic_fixedprec2 digits f prec theta where
  digits = ceiling (15 + 2.5 * prec * logBase 10 2) -- heuristic formula!
  f prec theta = gridsynth_phase_internal g prec theta effort

-- ----------------------------------------------------------------------
-- * Implementation details

-- ----------------------------------------------------------------------
-- ** The ε-region

-- | The ε-/region/ for given ε and θ is a convex subset of the closed
-- unit disk, given by [nobr /u/ ⋅ /z/ ≥ 1 - ε²\/2], where [nobr /z/ =
-- [exp −/i/θ\/2]], and “⋅” denotes the dot product of ℝ² (identified
-- with ℂ).
-- 
-- \[center [image Re.png]]

epsilon_region :: (Floating r, Ord r, RootHalfRing r, Quadratic QRootTwo r) => r -> r -> ConvexSet r
epsilon_region epsilon theta = ConvexSet ell tst int where
  
  -- A bounding ellipse for the ε-region.
  ell = Ellipse mat ctr
  ctr = (d*zx, d*zy)
  mat = bmat * mmat * special_inverse bmat
  mmat = toOperator ((ev1, 0), (0, ev2))
  bmat = toOperator ((zx, -zy), (zy, zx))
  ev1 = 4 * (1 / epsilon)^4
  ev2 = (1 / epsilon)^2
  
  -- A line intersector for the ε-region.
  int p v
    | q == Nothing         = Nothing
    | vz == 0 && rhs <= 0  = Just (t0, t1)
    | vz == 0 && otherwise = Nothing
    | vz > 0               = Just (max t0 t2, t1)
    | otherwise            = Just (t0, min t1 t2)
    where
      a = iprod v v
      b = 2 * iprod v p
      c = iprod p p - 1
      q = quadratic (fromDRootTwo a :: QRootTwo) (fromDRootTwo b) (fromDRootTwo c)
      Just (t0, t1) = q
    
      -- solve (p + tv) * z >= d
      -- equivalently, t * vz >= d - pz
      vz = iprod (point_fromDRootTwo v) z
      rhs = d - iprod (point_fromDRootTwo p) z
      t2 = rhs / vz

  -- The characteristic function of the ε-region.
  tst (x,y) = x^2 + y^2 <= 1 && zx * fromDRootTwo x + zy * fromDRootTwo y >= d
  
  zx = cos (-theta/2)
  zy = sin (-theta/2)
  d = 1 - epsilon^2/2
  z = (zx, zy)
  
-- | The ε-/region/, scaled by an additional factor of √/s/, where
-- /s/ > 0. The center of scaling is the origin.
epsilon_region_scaled :: (Floating r, Ord r, RootHalfRing r, Quadratic QRootTwo r) => DRootTwo -> r -> r -> ConvexSet r
epsilon_region_scaled s epsilon theta = ConvexSet ell tst int where
  
  -- A bounding ellipse for the ε-region.
  ell = Ellipse mat ctr
  ctr = (rd*zx, rd*zy)
  mat = bmat * mmat * special_inverse bmat
  mmat = toOperator ((ev1, 0), (0, ev2))
  bmat = toOperator ((zx, -zy), (zy, zx))
  ev1 = 4 * (1 / epsilon)^4 / fromDRootTwo s
  ev2 = (1 / epsilon)^2 / fromDRootTwo s
  
  -- A line intersector for the ε-region.
  int p v
    | q == Nothing         = Nothing
    | vz == 0 && rhs <= 0  = Just (t0, t1)
    | vz == 0 && otherwise = Nothing
    | vz > 0               = Just (max t0 t2, t1)
    | otherwise            = Just (t0, min t1 t2)
    where
      a = iprod v v
      b = 2 * iprod v p
      c = iprod p p - s
      q = quadratic (fromDRootTwo a :: QRootTwo) (fromDRootTwo b) (fromDRootTwo c)
      Just (t0, t1) = q
    
      -- solve (p + tv) * z >= d * r
      -- equivalently, t * vz >= d * r - pz
      vz = iprod (point_fromDRootTwo v) z
      rhs = rd - iprod (point_fromDRootTwo p) z
      t2 = rhs / vz

  -- The characteristic function of the ε-region.
  tst (x, y) = x^2 + y^2 <= s && zx * fromDRootTwo x + zy * fromDRootTwo y >= rd
  
  zx = cos (-theta/2)
  zy = sin (-theta/2)
  rd = (1 - epsilon^2/2) * sqrt (fromDRootTwo s)
  z = (zx, zy)
  
-- ----------------------------------------------------------------------
-- ** Main algorithm implementation
    
-- | The internal implementation of the ellipse-based approximate
-- synthesis algorithm. The parameters are a source of randomness /g/,
-- the angle θ, the precision /b/ ≥ 0 in bits, and an amount of
-- \"effort\" to put into factoring.
-- 
-- The outputs are a unitary operator in the Clifford+/T/ group that
-- approximates /R/[sub /z/](θ) to within ε in the operator norm;
-- log[sub 0.5] of the actual error, or 'Nothing' if the error is 0;
-- and the number of candidates tried.
-- 
-- Note: the parameter θ must be of a real number type that has enough
-- precision to perform intermediate calculations; this typically
-- requires precision O(ε[sup 2]).  A more user-friendly function that
-- selects the required precision automatically is 'gridsynth'.
gridsynth_internal :: forall r g.(RootHalfRing r, Ord r, Floating r, Adjoint r, Floor r, RealFrac r, Quadratic QRootTwo r, RandomGen g) => g -> r -> r -> Int -> (U2 DOmega, Maybe Double, [(DOmega, Integer, DStatus)])
gridsynth_internal g prec theta effort = (uU, log_err, candidate_info) where
  epsilon = 2 ** (-prec)
  region = epsilon_region epsilon theta
  raw_candidates = gridpoints2_increasing region unitdisk
  candidates = [ (u, t) | (k, us) <- raw_candidates,
                          let t = tcount k,
                          u <- us ]
  (uU, log_err, candidate_info) = first_solvable [] g candidates
  
  tcount k = if k > 0 then 2*k - 2 else 0

  first_solvable candidate_info g [] = error "gridsynth: internal error: finite list of candidates?"
  first_solvable candidate_info g ((u, tcount) : us) = case answer_t of
    Just (Just t) -> let (uU, log_err) = with_successful_candidate u t in (uU, log_err, ((u, tcount, Success) : candidate_info))
    Just Nothing -> first_solvable ((u, tcount, Fail) : candidate_info) g2 us
    Nothing -> first_solvable ((u, tcount, Timeout) : candidate_info) g2 us
    where
      (g1, g2) = split g
      xi = real (1 - adj u * u)
      answer_t = run_bounded effort $ diophantine_dyadic g1 xi
  
  with_successful_candidate u t = (uU, log_err) where
    uU | denomexp (u + t) < denomexp (u + omega * t)
               = matrix2x2 (u, -(adj t)) (t, adj u)
       | otherwise
               = matrix2x2 (u, -(adj (omega*t))) (omega*t, adj u)
    log_err 
      | err <= 0  = Nothing
      | otherwise = Just (logBase_double 0.5 err)
    err = sqrt (real (hs_sqnorm (uU_fixed - zrot_fixed)) / 2)
    uU_fixed = matrix_map fromDOmega uU
    zrot_fixed = zrot (theta :: r)

data Phase = Phase0 | Phase1

-- | The internal implementation of the ellipse-based approximate
-- synthesis algorithm, up to a phase. The parameters are the same as
-- for 'gridsynth_internal'.
gridsynth_phase_internal :: forall r g.(RootHalfRing r, Ord r, Floating r, Adjoint r, Floor r, RealFrac r, Quadratic QRootTwo r, Quadratic r r, RandomGen g) => g -> r -> r -> Int -> (U2 DOmega, Maybe Double, [(DOmega, Integer, DStatus)])
gridsynth_phase_internal g prec theta effort = (uU, log_err, candidate_info) where
  epsilon = 2 ** (-prec)
  region0 = epsilon_region epsilon theta
  disk0 = unitdisk
  region1 = epsilon_region_scaled (2 + roottwo) epsilon theta
  disk1 = disk (2 - roottwo)
  opG = to_upright_sets region0 disk0
  raw_candidates0 = gridpoints2_increasing_with_gridop region0 disk0 opG
  raw_candidates1 = gridpoints2_increasing_with_gridop region1 disk1 opG
  candidates0 = [ (t, Phase0, us) | (k, us) <- raw_candidates0,
                               let t = tcount k ]
  candidates1 = [ (t, Phase1, us') | (k, us) <- raw_candidates1,
                                let t = 1 + tcount k,
                                let us' = [ u * delta_inv | u <- us ] ]
  merged = mergeBy (compare `on` first) candidates0 candidates1
  candidates = [ (t, ph, u) | (t, ph, us) <- merged, u <- us ]
  (uU, log_err, candidate_info) = first_solvable [] g candidates
  
  fabs (Cplx a b) = sqrt(a^2 + b^2)

  tcount k = if k > 0 then 2*k - 2 else 0

  first_solvable candidate_info g [] = error "gridsynth: internal error: finite list of candidates?"
  first_solvable candidate_info g ((tcount, phase, u) : us) = case answer_t of
    Just (Just t) -> 
      let (uU, log_err) = with_successful_candidate u t phase in 
      (uU, log_err, ((u, tcount, Success) : candidate_info))
    Just Nothing -> first_solvable ((u, tcount, Fail) : candidate_info) g2 us
    Nothing -> first_solvable ((u, tcount, Timeout) : candidate_info) g2 us
    where
      (g1, g2) = split g
      xi = real (1 - adj u * u)
      answer_t = run_bounded effort $ diophantine_dyadic g1 xi
  
  with_successful_candidate u t Phase0 = (uU, log_err) where
    uU | denomexp (u + t) < denomexp (u + omega * t)
               = matrix2x2 (u, -(adj t)) (t, adj u)
       | otherwise
               = matrix2x2 (u, -(adj (omega*t))) (omega*t, adj u)
    log_err 
      | err <= 0  = Nothing
      | otherwise = Just (logBase_double 0.5 err)
    err = sqrt (real (hs_sqnorm (uU_fixed - zrot_fixed)) / 2)
    uU_fixed = matrix_map fromDOmega uU
    zrot_fixed = zrot (theta :: r)
    
  with_successful_candidate u t Phase1 = (uU, log_err) where
    uU | denomexp (u + t) < denomexp (u + omega * t)
               = matrix2x2 (u, -(adj t) * omega_inv) (t, adj u * omega_inv)
       | otherwise
               = matrix2x2 (u, -(adj t)) (t * omega_inv, adj u * omega_inv)
    log_err 
      | err <= 0  = Nothing
      | otherwise = Just (logBase_double 0.5 err)
    err = sqrt (real (hs_sqnorm (sqrt_omega `scalarmult` uU_fixed - zrot_fixed)) / 2)
    uU_fixed = matrix_map fromDOmega uU
    zrot_fixed = zrot (theta :: r)
    sqrt_omega = Cplx (cos (pi/8)) (sin (pi/8))    
    omega_inv = omega^7

  delta_inv = roothalf * (omega - i)

-- ----------------------------------------------------------------------
-- * Auxiliary functions

-- | Merge the elements of two lists in increasing order, assuming
-- that each of the lists is already sorted. The first argument is a
-- comparison function for elements.
mergeBy :: (a -> a -> Ordering) -> [a] -> [a] -> [a]
mergeBy c [] l2 = l2
mergeBy c l1 [] = l1
mergeBy c (h1:t1) (h2:t2)
  | c h1 h2 == LT  = h1:(mergeBy c t1 (h2:t2))
  | otherwise      = h2:(mergeBy c (h1:t1) t2)

-- | Return the first component of a triple.
first :: (a,b,c) -> a
first (a,b,c) = a
