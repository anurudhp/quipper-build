{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Rank2Types #-}

-- | This module provides a type class of things that can be converted
-- to arbitrary precision real numbers.
module Quantum.Synthesis.ToReal where

import Quantum.Synthesis.ArcTan2
import Data.Number.FixedPrec

-- ----------------------------------------------------------------------
-- * Conversion to real number types

-- | A type class for things that can be converted to a real number at
-- arbitrary precision.
class ToReal a where
  to_real :: (Floating r, ArcTan2 r) => a -> r

instance ToReal Rational where
  to_real = fromRational
  
instance ToReal Integer where
  to_real = fromInteger
  
instance ToReal Int where
  to_real = fromIntegral
  
instance ToReal Double where
  to_real = fromRational . toRational

instance ToReal Float where
  to_real = fromRational . toRational

instance (Precision e) => ToReal (FixedPrec e) where
  to_real = fromRational . toRational

-- ----------------------------------------------------------------------
-- ** Dynamic conversion to FixedPrec

-- | It would be useful to have a function for converting a symbolic
-- real number to a fixed-precision real number with a chosen
-- precision, such that the precision /e/ depends on a parameter /d/:
-- 
-- > to_fixedprec :: (ToReal r) => Integer -> r -> FixedPrec e
-- > to_fixedprec d x = ...
--  
-- However, since /e/ is a type, /d/ is a term, and Haskell is not
-- dependently typed, this cannot be done directly.
-- 
-- The function 'dynamic_fixedprec' is the closest thing we have to a
-- workaround. The call @dynamic_fixedprec@ /d/ /f/ /x/ calls
-- /f/(/x/'), where /x/' is the value /x/ converted to /d/ digits of
-- precision.  In other words, we have
-- 
-- > dynamic_fixedprec d f x = f (to_fixedprec d x),
-- 
-- with the restriction that the precision /e/ cannot occur freely in
-- the result type of /f/.
dynamic_fixedprec :: forall a r.(ToReal r) => Integer -> (forall e.(Precision e) => FixedPrec e -> a) -> r -> a
dynamic_fixedprec d f x = loop d (undefined :: P0)
  where 
    loop :: forall e.(Precision e) => Integer -> e -> a
    loop d e
      | d >= 1000 = loop (d-1000) (undefined :: PPlus1000 e)
      | d >= 100  = loop (d-100)  (undefined :: PPlus100 e)
      | d >= 10   = loop (d-10) (undefined :: PPlus10 e)
      | d > 0     = loop (d-1) (undefined :: PPlus1 e)
      | otherwise = f (to_real x :: FixedPrec e)

-- | Like 'dynamic_fixedprec', but take two real number arguments. In
-- terms of the fictitious function @to_fixedprec@, we have:
-- 
-- > dynamic_fixedprec2 d f x y = f (to_fixedprec d x) (to_fixedprec d y).
dynamic_fixedprec2 :: forall a r s.(ToReal r, ToReal s) => Integer -> (forall e.(Precision e) => FixedPrec e -> FixedPrec e -> a) -> r -> s -> a
dynamic_fixedprec2 d f x y = loop d (undefined :: P0)
  where 
    loop :: forall e.(Precision e) => Integer -> e -> a
    loop d e
      | d >= 1000 = loop (d-1000) (undefined :: PPlus1000 e)
      | d >= 100  = loop (d-100)  (undefined :: PPlus100 e)
      | d >= 10   = loop (d-10) (undefined :: PPlus10 e)
      | d > 0     = loop (d-1) (undefined :: PPlus1 e)
      | otherwise = f (to_real x :: FixedPrec e) (to_real y :: FixedPrec e)

