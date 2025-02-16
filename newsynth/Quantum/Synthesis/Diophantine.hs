-- | This module provides some number-theoretic functions,
-- particularly functions for solving the Diophantine equation
-- 
-- \[center /t/[sup †]/t/ = ξ,]
-- 
-- where ξ ∈ ℤ[√2] and /t/ ∈ ℤ[ω], or ξ ∈ [bold D][√2] and /t/ ∈ [bold D][ω].
-- 
-- In general, solving this equation can be hard, as it depends on the
-- ability to factor the integer /n/ = ξ[sup •]ξ into primes. We
-- formulate the solution as a step computation (see
-- "Quantum.Synthesis.StepComp"), so that the caller can dynamically
-- determine how much time to spend on solving the equation, or can
-- attempt to solve several such equations in parallel.
-- 
-- In many cases, even a partial factorization of /n/ is sufficient to
-- determine that no solution exists. This implementation is written
-- to take advantage of such cases.

module Quantum.Synthesis.Diophantine (
  -- * Diophantine solvers
  diophantine,
  diophantine_dyadic,
  diophantine_associate,
  
  -- * Factoring
  find_factor,
  relatively_prime_factors,
  
  -- * Computations in ℤ[sub /n/]
  power_mod,
  root_of_negative_one,
  root_mod,
  ) where

import Quantum.Synthesis.StepComp
import Quantum.Synthesis.EuclideanDomain
import Quantum.Synthesis.Ring

import System.Random
import Control.Exception

-- ----------------------------------------------------------------------
-- * Diophantine solvers

-- | Given ξ ∈ ℤ[√2], find /t/ ∈ ℤ[ω] such that /t/[sup †]/t/ = ξ, if
-- such /t/ exists, or return 'Nothing' otherwise.
diophantine :: (RandomGen g) => g -> ZRootTwo -> StepComp (Maybe ZOmega)
diophantine g xi
  | xi == 0 = return (Just 0)
  | xi < 0 = return Nothing
  | adj2 xi < 0 = return Nothing
  | otherwise = do
    t <- diophantine_associate g xi
    case t of
      Nothing -> return Nothing
      Just t -> do
        let xi_associate = zroottwo_of_zomega (adj t * t)
        let u = euclid_div xi xi_associate
        case zroottwo_root u of
          Nothing -> return Nothing
          Just v -> return (Just (fromZRootTwo v * t))
    
-- | Given an element ξ ∈ [bold D][√2], find /t/ ∈ [bold D][ω] such
-- that /t/[sup †]/t/ = ξ, if such /t/ exists, or return 'Nothing'
-- otherwise.

-- Implementation note: In the reduction from [bold D][√2] to ℤ[√2],
-- we can multiply by a power of λ√2 instead of √2. This has the same
-- effect of reducing the denominator exponent to 0 (note that λ is a
-- unit of the ring ℤ[√2]), but has the additional advantage that λ√2
-- (unlike √2) is doubly positive, thereby preserving solvability of
-- the Diophantine equation.
-- 
-- Similarly, in translating the solution back from ℤ[ω] to 
-- [bold D][ω], we use the fact that 1\/(λ√2) = /u/[sup †]/u/, where
-- /u/ = (ω - /i/)\/√2. Also note that /u/ = δ⁻¹, where δ = 1 + ω.
diophantine_dyadic :: (RandomGen g) => g -> DRootTwo -> StepComp (Maybe DOmega)
diophantine_dyadic g xi = do
  let k = denomexp xi
  let (k',k'') = k `divMod` 2
  let xi' = to_whole ((lambda * roottwo)^k'' * 2^k' * xi)
  t' <- diophantine g xi'
  case t' of
    Nothing -> return Nothing
    Just t' -> return (Just (u^k'' * roothalf^k' * from_whole t'))
  where
    u = roothalf * (omega - i)
    lambda = 1 + roottwo

-- | Given ξ ∈ ℤ[√2], find /t/ ∈ ℤ[ω] such that /t/[sup †]/t/ ~ ξ, if
-- such /t/ exists, or 'Nothing' otherwise. Unlike 'diophantine', the
-- equation is only solved up to associates, i.e., up to a unit of the
-- ring.
diophantine_associate :: (RandomGen g) => g -> ZRootTwo -> StepComp (Maybe ZOmega)
diophantine_associate g xi 
  | xi == 0 = return (Just 0)
  | otherwise = do
    let d = euclid_gcd xi (adj2 xi)
    let xi' = euclid_div xi d
    res <- parallel_maybe (dioph_zroottwo_selfassociate g1 d) (dioph_zroottwo_assoc g2 xi')
    case res of
      Nothing -> return Nothing
      Just (t1, t2) -> return (Just (t1*t2))
  where 
    (g1, g2) = split g

-- ----------------------------------------------------------------------
-- * Factoring

-- | Given a positive composite integer /n/, find a non-trivial factor
-- of /n/ using a simple Pollard-rho method. The expected runtime is
-- O(√/p/), where /p/ is the size of the smallest prime factor.  If
-- /n/ is not composite (i.e., if /n/ is prime or 1), this function
-- diverges.
find_factor :: (RandomGen g) => g -> Integer -> StepComp Integer
find_factor g n
  | even n && n > 2 = return 2
  | otherwise = tick >> aux 2 (f 2)
  where
    (a, g2) = randomR (1, n-1) g
    f x = (x^2 + a) `mod` n
    aux x y
      | d == 1 = tick >> aux (f x) (f (f y))
      | d == n = find_factor g2 n
      | otherwise = return d
      where
        d = gcd (x-y) n

-- | Given a factorization /n/ = /ab/ of some element of a Euclidean domain, find a factorization of /n/ into relatively prime factors,
-- 
-- \[center /n/ = /u/ /c/[sub 1][sup /k/[sub 1]] ⋅ … ⋅ /c/[sub /m/][sup /k/[sub /m/]],]
-- 
-- where /m/ ≥ 2, /u/ is a unit, and /c/[sub 1], …, /c/[sub /m/] are
-- pairwise relatively prime.
-- 
-- While this is not quite a prime factorization of /n/, it can be a
-- useful intermediate step for computations that proceed by recursion
-- on relatively prime factors (such as Euler's φ-function, the
-- solution of Diophantine equations, etc.).
relatively_prime_factors :: (EuclideanDomain a) => a -> a -> (a, [(a, Integer)])
relatively_prime_factors a b = aux 1 [a,b] [] where
  aux u [] fs = (u, fs)
  aux u (h:t) fs
    | is_unit h = aux (h*u) t fs
  aux u (h:t) fs = aux (u'*u) (hs ++ t) fs' where
    (u', hs, fs') = aux2 h fs
      
  aux2 h [] = (1, [], [(h,1)])
  aux2 h ((f,k) : fs)
    | euclid_associates h f = (u', [], (f,k+1) : fs)      
    | is_unit d = (u, hs, (f,k) : fs')
    | otherwise = (1, [h `euclid_div` d, d] ++ replicate (fromInteger k) (f `euclid_div` d) ++ replicate (fromInteger k) d, fs)
    where
      d = euclid_gcd h f
      (u, hs, fs') = aux2 h fs
      u' = h `euclid_div` f

-- ----------------------------------------------------------------------
-- * Computations in ℤ[sub /n/]

-- | Modular exponentiation, using the method of repeated squaring.
-- 'power_mod' /a/ /k/ /n/ computes /a/[sup /k/] (mod /n/).
power_mod :: Integer -> Integer -> Integer -> Integer
power_mod a k n
  | k == 0 = 1
  | k == 1 = a `mod` n
  | even k = (b*b) `mod` n
  | otherwise = (b*b*a) `mod` n
  where
    b = power_mod a (k `div` 2) n

-- | Compute a root of −1 in ℤ[sub /n/], where /n/ > 0. If /n/ is a
-- positive prime satisfying /n/ ≡ 1 (mod 4), this succeeds within an
-- expected number of 2 ticks. Otherwise, it probably diverges.
-- 
-- As a special case, if this function notices that /n/ is not prime,
-- then it diverges without doing any additional work.
root_of_negative_one :: (RandomGen g) => g -> Integer -> StepComp Integer
root_of_negative_one g n = do
  tick
  let (b, g') = randomR (1, n-1) g
  let h = power_mod b ((n-1) `div` 4) n
  let r = (h*h) `mod` n
  if r == n-1 then
    return h
    else 
    if r /= 1 then
      diverge
    else
      root_of_negative_one g' n

-- | Compute a root of /a/ in ℤ[sub /n/], where /n/ > 0.  If /n/ is an
-- odd prime and /a/ is a non-zero square in ℤ[sub /n/], then this
-- succeeds in an expected number of 2 ticks. Otherwise, it probably
-- diverges.
root_mod :: (RandomGen g) => g -> Integer -> Integer -> StepComp Integer
root_mod g n a 
  | a `mod` n == -1 -- handle this special case more efficiently
                    = root_of_negative_one g n
  | otherwise = tick >> res 
  where
    (b, g') = randomR (0, n-1) g
    (r,s) = (2*b `mod` n, b^2-a `mod` n)
    (c,d) = pow (1,0) ((n-1) `div` 2)
    res = case inv_mod n c of
      Just c'
        | (t1^2 - a) `mod` n == 0 -> return t1
        where
          t = (1-d) * c'
          t1 = (t+b) `mod` n    
      _ -> root_mod g' n a

    -- | 'mul' performs a multiplication in the ring
    -- ℤ[sub /n/][t]\/(/t/²+/rt/+/s/). The elements /at/+/b/ are
    -- represented as pairs (/a/,/b/).
    mul :: (Integer, Integer) -> (Integer, Integer) -> (Integer, Integer)
    mul (a,b) (c,d) = (a'',b'') where
      (x,y,z) = (a*c, a*d+b*c, b*d)        -- multiply polynomials
      (a',b') = (y - x*r,z - x*s)          -- reduce modulo /t/²+/rt/+/s/
      (a'',b'') = (a' `mod` n, b' `mod` n) -- reduce modulo /n/

    -- | 'pow' takes a power in the ring
    -- ℤ[sub /n/][t]\/(/t/²+/rt/+/s/. The elements /at/+/b/ are
    -- represented as pairs (/a/,/b/).
    pow :: (Integer, Integer) -> Integer -> (Integer, Integer)
    pow x m
      | m <= 0 = (0,1)
      | odd m = x `mul` (x `pow` (m-1))
      | otherwise = y `mul` y where y = x `pow` (m `div` 2)

-- ----------------------------------------------------------------------
-- * Implementation details

-- $ Our implementation of the top-level Diophantine equation solvers
-- proceeds through a series of special cases. The following functions
-- handle the special cases, and are not of independent interest.

-- ----------------------------------------------------------------------
-- ** Case: ξ is an integer                                 

-- | Given an integer /n/ ∈ ℤ, attempt to find /t/ ∈ ℤ[ω] such that
-- /t/[sup †]/t/ ~ /n/, or return 'Nothing' if no such /t/ exists.
-- 
-- This function is optimized for the case when /n/ is prime, and
-- succeeds in an expected number of 2 ticks in this case.  If /n/ is
-- not prime, this function probably diverges.
dioph_int_assoc_prime :: (RandomGen g) => g -> Integer -> StepComp (Maybe ZOmega)
dioph_int_assoc_prime g n
  | n < 0 = dioph_int_assoc_prime g (-n)
  | n == 0 = return (Just 0)
  | n == 2 = return (Just roottwo)
  | n_mod_4 == 1 = do
    h <- root_of_negative_one g n
    let t = euclid_gcd (fromInteger h+i) (fromInteger n) :: ZOmega
    assert (adj t * t == fromInteger n) $ return (Just t)
  | n_mod_8 == 3 = do
    h <- root_mod g n (-2)
    let t = euclid_gcd (fromInteger h+i*roottwo) (fromInteger n) :: ZOmega
    assert (adj t * t == fromInteger n) $ return (Just t)
  | n_mod_8 == 7 = do
    h <- root_mod g n 2
    -- if n is prime, then 2 is a square. Conversely, if 2 is a
    -- square, even if n is not prime, it implies that the Diophantine
    -- equation has no solution. Because in this case, 2 is a square
    -- for every prime divisor of n, so each such divisor must be
    -- congruent to 1 or 7 (mod 8), so there must be at least one
    -- prime divisor that occurs as an odd power and is congruent to 7
    -- mod n.
    return Nothing
  | otherwise = diverge -- If n is even and not 2, then it is not prime, so diverge.
  where
    n_mod_4 = n `mod` 4
    n_mod_8 = n `mod` 8
    
-- | Given an integer /n/ ∈ ℤ, find /t/ ∈ ℤ[ω] such that /t/[sup †]/t/
-- ~ /n/, if such /t/ exists, or return 'Nothing' if no such /t/
-- exists. 
-- 
-- This function alternately calls 'dioph_int_assoc_prime' and
-- attempts to factor /n/. Therefore, it will eventually succeed;
-- however, the runtime depends on how hard it is to factor ξ.
dioph_int_assoc :: (RandomGen g) => g -> Integer -> StepComp (Maybe ZOmega)
dioph_int_assoc g n
  | n < 0 = dioph_int_assoc g (-n)
  | n == 0 = return (Just 0)
  | n == 1 = return (Just 1)
  | otherwise = interleave prime_solver factor_solver where
    interleave p f = do
      p <- subtask 4 p
      case p of 
        Done res -> return res
        _ -> do
          f <- subtask 1000 f
          case f of
            Done (a, k) -> do
              let b = n `div` a
              let (u, facs) = relatively_prime_factors a b
              forward (k `div` 2) $ dioph_int_assoc_powers g3 facs
            _ -> interleave p f
  
    (g1, g') = split g
    (g2, g3) = split g'
    prime_solver = dioph_int_assoc_prime g1 n 
    factor_solver = with_counter $ speedup 30 $ find_factor g2 n
    
-- | Given a factorization /n/ = /q/[sub 1][sup /k/[sub 1]]⋅…⋅/q/[sub
-- /m/][sup /k/[sub /m/]] of an integer /n/, where /q/[sub 1], …,
-- /q/[sub /m/] are pairwise relatively prime, find /t/ ∈ ℤ[ω] such
-- that /t/[sup †]/t/ ~ /n/, if such /t/ exists, or return 'Nothing'
-- if no such /t/ exists.
dioph_int_assoc_powers :: (RandomGen g) => g -> [(Integer, Integer)] -> StepComp (Maybe ZOmega)
dioph_int_assoc_powers g facs = do
  res <- parallel_list_maybe [dioph_int_assoc_power g (n,k) | (n,k) <- facs]
  case res of
    Nothing -> return Nothing
    Just sols -> return (Just (product sols))

-- | Given a pair of integers (/n/, /k/), find /t/ ∈ ℤ[ω] such that
-- /t/[sup †]/t/ ~ /n/[sup /k/], if such /t/ exists, or return
-- 'Nothing' if no such /t/ exists.
dioph_int_assoc_power :: (RandomGen g) => g -> (Integer, Integer) -> StepComp (Maybe ZOmega)
dioph_int_assoc_power g (n,k)
  | even k = return (Just (fromInteger (n^(k `div` 2))))
  | otherwise = do
    t <- dioph_int_assoc g n
    case t of
      Nothing -> return Nothing
      Just t -> return (Just (t^k))

-- ----------------------------------------------------------------------
-- ** Case: ξ ~ ξ[sup •]

-- | Given ξ ∈ ℤ[√2] such that ξ ~ ξ[sup •], find /t/ ∈ ℤ[ω] such that
-- /t/[sup †]/t/ ~ ξ, if such /t/ exists, or return 'Nothing' if no
-- such /t/ exists.
dioph_zroottwo_selfassociate :: (RandomGen g) => g -> ZRootTwo -> StepComp (Maybe ZOmega)
dioph_zroottwo_selfassociate g xi 
  | xi == 0 = return (Just 0)
  | otherwise = do
    res <- dioph_int_assoc g n
    case res of 
      Nothing -> return Nothing
      Just t -> if euclid_divides roottwo r then
                  return (Just ((1+omega) * t))
                else
                  return (Just t)
  where 
    RootTwo a b = xi
    n = gcd a b
    r = euclid_div xi (fromInteger n)

-- ----------------------------------------------------------------------
-- ** Case: gcd(ξ, ξ[sup •]) = 1

-- | Given ξ ∈ ℤ[√2] such that gcd(ξ, ξ[sup •]) = 1, attempt to find
-- /t/ ∈ ℤ[ω] such that /t/[sup †]/t/ ~ ξ, or return 'Nothing' if no
-- such /t/ exists. 
-- 
-- This function is optimized for the case when ξ is a prime in the
-- ring ℤ[√2]. In this case, it succeeds quickly, in an expected
-- number of 2 ticks.  If ξ is not prime, this function probably
-- diverges.
dioph_zroottwo_assoc_prime :: (RandomGen g) => g -> ZRootTwo -> StepComp (Maybe ZOmega)
dioph_zroottwo_assoc_prime g xi
  | xi == 0 = return (Just 0)
  | n_mod_8 == 1 = do
    h <- root_of_negative_one g n
    let t = euclid_gcd (fromInteger h+i) (fromZRootTwo xi) :: ZOmega
    assert ((adj t * t) `euclid_associates` fromZRootTwo xi) $ return (Just t)
  | n_mod_8 == 7 = return Nothing
  | otherwise = diverge
  where
    n_mod_8 = n `mod` 8
    n = abs (norm xi)
    
-- | Given ξ ∈ ℤ[√2] such that gcd(ξ, ξ[sup •]) = 1, find /t/ ∈ ℤ[ω]
-- such that /t/[sup †]/t/ ~ ξ, if such /t/ exists, or return
-- 'Nothing' if no such /t/ exists.
-- 
-- This function alternately calls 'dioph_int_assoc_prime' and
-- attempts to factor ξ. Therefore, it will eventually succeed.
-- However, the runtime depends on how hard it is to factor ξ.
dioph_zroottwo_assoc :: (RandomGen g) => g -> ZRootTwo -> StepComp (Maybe ZOmega)
dioph_zroottwo_assoc g xi
  | xi == 0 = return (Just 0)
  | otherwise = interleave prime_solver factor_solver where
    interleave p f = do
      p <- subtask 4 p
      case p of 
        Done res -> return res
        _ -> do
          f <- subtask 1000 f
          case f of
            Done (a, k) -> do
              let alpha = euclid_gcd xi (fromInteger a)
              let beta = xi `euclid_div` alpha
              let (u, facs) = relatively_prime_factors alpha beta   
              forward (k `div` 2) $ dioph_zroottwo_assoc_powers g3 facs
            _ -> interleave p f
  
    (g1, g') = split g
    (g2, g3) = split g'
    prime_solver = dioph_zroottwo_assoc_prime g1 xi
    factor_solver = with_counter $ speedup 30 $ find_factor g2 n
    
    n = abs (norm xi)

-- | Given a factorization ξ = /q/[sub 1][sup /k/[sub 1]]⋅…⋅/q/[sub
-- /m/][sup /k/[sub /m/]] of some ξ ∈ ℤ[√2], where /q/[sub 1], …,
-- /q/[sub /m/] are pairwise relatively prime, find /t/ ∈ ℤ[ω] such
-- that /t/[sup †]/t/ ~ ξ, if such /t/ exists, or return 'Nothing'
-- if it can be proven not to exist.
dioph_zroottwo_assoc_powers :: (RandomGen g) => g -> [(ZRootTwo, Integer)] -> StepComp (Maybe ZOmega)
dioph_zroottwo_assoc_powers g facs = do
  res <- parallel_list_maybe [dioph_zroottwo_assoc_power g (q,k) | (q,k) <- facs]
  case res of
    Nothing -> return Nothing
    Just sols -> return (Just (product sols))

-- | Given a pair (ξ, /k/), with ξ ∈ ℤ[√2] and /k/ ≥ 0, find /t/ ∈
-- ℤ[ω] such that /t/[sup †]/t/ ~ ξ[sup /k/], if such /t/ exists, or
-- return 'Nothing' if no such /t/ exists.
dioph_zroottwo_assoc_power :: (RandomGen g) => g -> (ZRootTwo, Integer) -> StepComp (Maybe ZOmega)
dioph_zroottwo_assoc_power g (xi,k)
  | even k = return (Just (fromZRootTwo (xi^(k `div` 2))))
  | otherwise = do
    t <- dioph_zroottwo_assoc g xi
    case t of
      Nothing -> return Nothing
      Just t -> return (Just (t^k))



