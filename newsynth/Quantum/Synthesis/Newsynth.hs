-- | This module provides backward compatibility with older versions
-- of the newsynth package. Formerly, it contained an implementation of
-- the single-qubit Clifford+/T/ approximation algorithm of
-- 
-- * Peter Selinger. Efficient Clifford+/T/ approximation of
-- single-qubit operators. <http://arxiv.org/abs/1212.6253>.
-- 
-- Since the new algorithm in "Quantum.Synthesis.GridSynth" is better
-- in all cases, we now simply provide a compatible interface to that
-- algorithm.
-- 
-- New software should not use this module, and it may eventually be
-- removed.

module Quantum.Synthesis.Newsynth where

import Quantum.Synthesis.Ring
import Quantum.Synthesis.SymReal
import Quantum.Synthesis.Matrix
import Quantum.Synthesis.CliffordT
import Quantum.Synthesis.GridSynth

import System.Random

-- | Backward compatible interface to the approximate synthesis
-- algorithm. The parameters are:
-- 
-- * an angle θ, to implement a /R/[sub /z/](θ) = [exp −/i/θ/Z/\/2]
-- gate;
--   
-- * a precision /b/ ≥ 0 in bits, such that ε = 2[sup -/b/];
-- 
-- * a source of randomness /g/.
-- 
-- Output a unitary operator in the Clifford+/T/ group that
-- approximates /R/[sub /z/](θ) to within ε in the operator norm. This
-- operator can then be converted to a list of gates with
-- 'to_gates'.
-- 
-- Note: the argument /theta/ is given as a symbolic real number. It
-- will automatically be expanded to as many digits as are necessary
-- for the internal calculation. In this way, the caller can specify,
-- e.g., an angle of 'pi'\/128 @::@ 'SymReal', without having to worry
-- about how many digits of π to specify.
newsynth :: (RandomGen g) => Double -> SymReal -> g -> U2 DOmega
newsynth prec theta g = gridsynth g prec theta 25

-- | A version of 'newsynth' that also returns some statistics:
-- log[sub 0.1] of the actual approximation error (or 'Nothing' if the
-- error is 0), and the number of candidates tried.
newsynth_stats :: (RandomGen g) => Double -> SymReal -> g -> (U2 DOmega, Maybe Double, Integer)
newsynth_stats prec theta g = (op, err_d, n) where
  (op, err_b, cinfo) = gridsynth_stats g prec theta 25
  err_d = case err_b of 
    Nothing -> Nothing
    Just b -> Just (b * logBase 10 2)
  n = fromIntegral (length cinfo)
  
-- | A version of 'newsynth' that returns a list of gates instead of a
-- matrix. The inputs are the same as for 'newsynth'.
-- 
-- Note: the list of gates will be returned in right-to-left order,
-- i.e., as in the mathematical notation for matrix multiplication.
-- This is the opposite of the quantum circuit notation.
newsynth_gates :: (RandomGen g) => Double -> SymReal -> g -> [Gate]
newsynth_gates prec theta g = gridsynth_gates g prec theta 25
