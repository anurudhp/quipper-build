{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | This module provides ring instances for "Data.Number.FixedPrec".

module Quantum.Synthesis.Ring.FixedPrec where

import Quantum.Synthesis.Ring

import Data.Number.FixedPrec

instance Precision e => RootHalfRing (FixedPrec e) where
  roothalf = sqrt 0.5
  fromDRootTwo (RootTwo x y)
   | y >= 0    = fromDyadic x + sqrt (fromDyadic (2*y^2))
   | otherwise = fromDyadic x - sqrt (fromDyadic (2*y^2))

instance Precision e => RootTwoRing (FixedPrec e) where
  roottwo = sqrt 2
  fromZRootTwo (RootTwo x y)
   | y >= 0    = fromInteger x + sqrt (fromInteger (2*y^2))
   | otherwise = fromInteger x - sqrt (fromInteger (2*y^2))

instance Precision e => HalfRing (FixedPrec e) where
  half = 0.5
  fromDyadic x
    | n >= 0    = fromInteger a / 2^n
    | otherwise = fromInteger a * 2^n
    where
      (a,n) = decompose_dyadic x

instance Precision e => Adjoint (FixedPrec e) where
  adj x = x
  
instance Precision e => Adjoint2 (FixedPrec e) where
  adj2 x = x

instance Precision e => Floor (FixedPrec e) where
  floor_of = floor
  ceiling_of = ceiling
