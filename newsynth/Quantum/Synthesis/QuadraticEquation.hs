{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

-- | This module provides a type class 'Quadratic', for solving
-- quadratic equations.

module Quantum.Synthesis.QuadraticEquation (
  Quadratic (..)
  ) where

import Data.Number.FixedPrec
import Quantum.Synthesis.Ring
import Quantum.Synthesis.ToReal

-- | This type class provides a primitive method for solving quadratic
-- equations. For many floating-point or fixed-precision
-- representations of real numbers, using the usual \"quadratic
-- formula\" results in a significant loss of precision. Instances of
-- the 'Quadratic' class should provide an efficient high-precision
-- method when possible.
class Quadratic t a where
  -- | 'quadratic' /a/ /b/ /c/: solve the quadratic equation
  -- /ax/² + /bx/ + /c/ = 0. Return the pair of solutions (/x/₁, /x/₂)
  -- with /x/₁ ≤ /x/₂, or 'Nothing' if no solution exists. Note that
  -- the coefficients /a/, /b/, and /c/ can be taken to be of an exact
  -- type; therefore instances have the opportunity to work with
  -- infinite precision.
  quadratic :: t -> t -> t -> Maybe (a, a)

-- ----------------------------------------------------------------------
-- FixedPrec instance

-- | Given /b/, /c/ ∈ ℚ[√2], consider the quadratic function /f/(/t/)
-- = /t/² + /b//t/ + /c/.
-- 
-- * If /f/(/t/) = 0 has no real solutions, return 'Nothing'.
-- 
-- * If /f/(/t/) = 0 has real solutions /t/₀ ≤ /t/₁, return /t/'₀,
-- /t/'₁ ∈ ℤ such that /t/'₀ ≤ /t/₀, /t/₁ ≤ /t/'₁, and |/t/'₀ - /t/₀|,
-- |/t/'₁ - /t/₁| ≤ 1.
int_quadratic :: (Fractional t, Floor t, Ord t) => t -> t -> Maybe (Integer, Integer)
int_quadratic b c
  | radix < 0  = Nothing
  | otherwise  = Just (t0, t1)
  where
    radix = b^2/4 - c
    tm = -b / 2
    rootradix' = intsqrt (floor_of radix)
    t1' = floor_of tm + rootradix'
    t1 
      | is_solution1 (t1'+2) = t1'+2
      | is_solution1 (t1'+1) = t1'+1
      | otherwise = t1'
    t0' = ceiling_of tm - rootradix'
    t0
      | is_solution0 (t0'-2) = t0'-2
      | is_solution0 (t0'-1) = t0'-1
      | otherwise = t0'
    is_solution1 x = f x' >= 0 && (f (x'-1) < 0 || x'-1 < tm) where
        x' = fromInteger x
    is_solution0 x = f x' >= 0 && (f (x'+1) < 0 || x'-1 > tm) where
        x' = fromInteger x
    f x = x^2 + b*x + c

-- | Given /a/, /b/, /c/ ∈ ℚ[√2] with /a/ > 0, consider the quadratic
-- function /f/(/t/) = /a//t/² + /b//t/ + /c/.
-- 
-- * If /f/(/t/) = 0 has no real solutions, return 'Nothing'.
-- 
-- * If /f/(/t/) = 0 has real solutions /t/₀ ≤ /t/₁, return (/t/'₀,
-- /t/'₁) such that /t/'₀ ≤ /t/₀, /t/₁ ≤ /t/'₁, and |/t/'₀ - /t/₀|,
-- |/t/'₁ - /t/₁| ≤ 10[sup -/d/], where /d/ is the precision of the
-- fixed-point real number type.
quadratic_fixedprec :: (Fractional t, Floor t, Ord t, Precision e) => t -> t -> t -> Maybe (FixedPrec e, FixedPrec e)
quadratic_fixedprec a b c 
  | False = Just (r, r)
  | otherwise = do
    (x0, x1) <- int_quadratic b' c'
    return (fromInteger x0 / prec, fromInteger x1 / prec)
  where
    r = 0
    d = getprec r
    prec = 10^d
    prec' = 10^d
    b' = prec' * b/a
    c' = prec'^2 * c/a
    q = int_quadratic b' c'
  
instance (Fractional t, Floor t, Ord t, Precision e) => Quadratic t (FixedPrec e) where
  quadratic = quadratic_fixedprec

-- ----------------------------------------------------------------------
-- Double instance

instance (ToReal t) => Quadratic t Double where
  quadratic a' b' c'
    | radix < 0 = Nothing
    | b >= 0 = Just (t1, t2)
    | otherwise = Just (t1', t2')
   where
    radix = b^2 - 4*a*c
    s1 = -b - sqrt radix
    s2 = -b + sqrt radix
    t1 = s1 / (2*a)
    t2 = (2*c) / s1
    t1' = (2*c) / s2
    t2' = s2 / (2*a)
    a = to_real a'
    b = to_real b'
    c = to_real c'
