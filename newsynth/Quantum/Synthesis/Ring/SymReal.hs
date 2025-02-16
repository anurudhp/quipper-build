{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | This module provides ring instances for "Quantum.Synthesis.SymReal".

module Quantum.Synthesis.Ring.SymReal where

import Quantum.Synthesis.Ring
import Quantum.Synthesis.SymReal

instance RootHalfRing SymReal where
  roothalf = sqrt 0.5

instance RootTwoRing SymReal where
  roottwo = sqrt 2

instance HalfRing SymReal where
  half = 0.5

instance Adjoint SymReal where
  adj x = x
  
instance Adjoint2 SymReal where
  adj2 x = x
