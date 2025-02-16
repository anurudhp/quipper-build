{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE EmptyDataDecls #-}

-- | A reasonably efficient implementation of arbitrary-but-fixed
-- precision real numbers. This is inspired by, and partly based on,
-- "Data.Number.Fixed" and "Data.Number.CReal", but more efficient.

module Data.Number.FixedPrec (
  -- * Type-level integers for precision
  Precision,
  P0, P1, P10, P100, P1000, P2000,
  PPlus1, PPlus3, PPlus10, PPlus100, PPlus1000,
  
  -- * Fixed-precision numbers
  FixedPrec,
  getprec,
  
  -- * Static and dynamic casts
  cast,
  upcast,
  downcast,
  with_added_digits,
  
  -- * Other operations
  fractional,
  solve_quadratic,
  log_double
  ) where

import Data.Ratio
import System.Random

-- ----------------------------------------------------------------------
-- * Auxiliary functions

-- ----------------------------------------------------------------------
-- ** Integer functions

-- | Integer division with rounding to the closest. Note: rounding
-- could be improved. Right now, we always round up in case of a tie.
divi :: Integer -> Integer -> Integer
divi a b = (a + (b `div` 2)) `div` b
infixl 7 `divi`

-- | Shift the integer to the right by the given number of decimal
-- digits, with rounding.
decshiftR :: Int -> Integer -> Integer
decshiftR n x = x `divi` 10^n

-- | Shift the integer to the right by the given number of decimal
-- digits, without rounding (i.e., truncate)
dectruncR :: Int -> Integer -> Integer
dectruncR n x = x `quot` 10^n

-- | Shift the integer to the left by the given number of decimal
-- digits.
decshiftL :: Int -> Integer -> Integer
decshiftL n x = x * 10^n

-- | Return 1 + the position of the leftmost \"1\" bit of a
-- non-negative 'Integer'. Do this in time O(/n/ log /n/), where /n/
-- is the size of the integer (in digits).
hibit :: Integer -> Int
hibit 0 = 0
hibit n = aux 1 where
  aux k 
    | n >= 2^k  = aux (2*k)
    | otherwise = aux2 k (k `div` 2)    -- 2^(k/2) <= n < 2^k
  aux2 upper lower 
    | upper - lower < 2  = upper
    | n >= 2^middle = aux2 upper middle
    | otherwise = aux2 middle lower
    where
      middle = (upper + lower) `div` 2

-- | For /n/ ≥ 0, return the floor of the square root of /n/. This is
-- done using integer arithmetic, so there are no rounding errors.
intsqrt :: (Integral n) => n -> n
intsqrt n 
  | n <= 0 = 0
  | otherwise = iterate a
    where
      iterate m
        | m_sq <= n && m_sq + 2*m + 1 > n = m
        | otherwise = iterate ((m + n `div` m) `div` 2)
          where
            m_sq = m*m
      a = 2^(b `div` 2)
      b = hibit (fromIntegral n)

-- | Find the ceiling of the larger solution of a quadratic
-- equation. Specifically, given the polynomial /p/(/x/) = /x/² + /bx/
-- + /c/, where /b/ and /c/ are integers, find the smallest integer
-- /x/ ≥ -/b/\/2 satisfying /p/(/x/) ≥ 0, if /b/^2 - 4/c/ ≥ 0.
-- 
-- This is done using integer arithmetic, so there are no rounding
-- errors. It generalizes 'intsqrt'.
intquad :: Integer -> Integer -> Maybe Integer
intquad b c
  | b^2 - 4*c < 0 = Nothing
  | x1^2 + b*x1 + c >= 0 = Just x1
  | otherwise = Just (iterate x0)
  where
    iterate x
      | px <= 0 && px + 2*x+1+b > 0 = x+1
      | otherwise = iterate ((x^2 - c) `div` (2*x + b))
      where
        px = x^2 + b*x + c
    x1 = -(b `div` 2)
    x0 = x1 + 2^(h `div` 2)
    h = hibit (b^2 - 4*c)

-- ----------------------------------------------------------------------
-- ** Other general-purpose functions
            
-- | Given positive /b/ > 1 and /x/ > 0, return (/n/, /r/) such that
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
log_double :: (Floating a, Real a) => a -> Double
log_double x = y where
  e = exp 1
  (n, r) = floorlog e x
  y = fromInteger n + log (to_double r)
  to_double = fromRational . toRational

-- ----------------------------------------------------------------------
-- * Type-level integers for precision

-- | A type class for type-level integers, capturing a precision
-- parameter. Precision is measured in decimal digits.
class Precision e where
  -- | Get the precision, in decimal digits.
  digits :: e -> Int
  
-- | Precision of 0 digits.
data P0
instance Precision P0 where
  digits e = 0

-- | Precision of 1 digit.
data P1
instance Precision P1 where
  digits e = 1

-- | Precision of 10 digits.
data P10
instance Precision P10 where
  digits e = 10

-- | Precision of 100 digits.
data P100
instance Precision P100 where
  digits e = 100

-- | Precision of 1000 digits.
data P1000
instance Precision P1000 where
  digits e = 1000

-- | Precision of 2000 digits.
data P2000
instance Precision P2000 where
  digits e = 2000

-- | Add 1 digit to the given precision.
data PPlus1 e
instance Precision e => Precision (PPlus1 e) where
  digits e = digits (un e) + 1 where
    un :: PPlus1 e -> e
    un = undefined

-- | Add 3 digits to the given precision.
data PPlus3 e
instance Precision e => Precision (PPlus3 e) where
  digits e = digits (un e) + 3 where
    un :: PPlus3 e -> e
    un = undefined

-- | Add 10 digits to the given precision.
data PPlus10 e
instance Precision e => Precision (PPlus10 e) where
  digits e = digits (un e) + 10 where
    un :: PPlus10 e -> e
    un = undefined

-- | Add 100 digits to the given precision.
data PPlus100 e
instance Precision e => Precision (PPlus100 e) where
  digits e = digits (un e) + 100 where
    un :: PPlus100 e -> e
    un = undefined

-- | Add 1000 digits to the given precision.
data PPlus1000 e
instance Precision e => Precision (PPlus1000 e) where
  digits e = digits (un e) + 1000 where
    un :: PPlus1000 e -> e
    un = undefined

----------------------------------------------------------------------
-- * Fixed-precision numbers
    
-- $ Fixed-precision numbers are simply implemented as integers. The
-- integer /n/ represents the real number /n/⋅10[sup −/d/], where /d/
-- is the precision in digits.

-- | The type of fixed-precision numbers.
newtype FixedPrec e = F Integer
                    deriving (Eq, Ord)


-- | Get the precision of a fixed-precision number, in decimal digits.
getprec :: (Precision e) => FixedPrec e -> Int
getprec = digits . un where
  un :: FixedPrec e -> e
  un = undefined

-- ----------------------------------------------------------------------
-- ** Static and dynamic casts

-- | Cast from any 'FixedPrec' type to another.
cast :: (Precision e, Precision f) => FixedPrec e -> FixedPrec f
cast a@(F x) = b where
  b = F y
  px = getprec a
  py = getprec b
  y = if (px >= py) then
        decshiftR (px - py) x
      else
        decshiftL (py - px) x

-- | Cast to a fixed-point type with three additional digits of accuracy.
upcast :: (Precision e) => FixedPrec e -> FixedPrec (PPlus3 e)
upcast = cast

-- | Cast to a fixed-point type with three fewer digits of accuracy.
downcast :: (Precision e) => FixedPrec (PPlus3 e) -> FixedPrec e
downcast = cast

-- | The function 'with_added_digits' /d/ /f/ /x/ evaluates /f/(/x/), adding
-- /d/ digits of accuracy to /x/ during the computation.
with_added_digits :: forall a f.(Precision f) => Int -> (forall e.(Precision e) => FixedPrec e -> a) -> FixedPrec f -> a
with_added_digits d f x = loop d (un x)
  where
    un :: FixedPrec e -> e
    un = undefined
    loop :: forall e.(Precision e) => Int -> e -> a
    loop d e
      | d >= 1000 = loop (d-1000) (undefined :: PPlus1000 e)
      | d >= 100  = loop (d-100)  (undefined :: PPlus100 e)
      | d >= 10   = loop (d-10)   (undefined :: PPlus10 e)
      | d > 0     = loop (d-1)    (undefined :: PPlus1 e)
      | otherwise = f (cast x :: FixedPrec e)

-- ----------------------------------------------------------------------
-- ** Some primitive operations

-- | Multiply an integer by a fixed-precision number. This is
-- marginally more efficient than multiplying two fixed-precision
-- numbers.
(..*) :: Integer -> FixedPrec e -> FixedPrec e
n ..* (F x) = F (n * x)
infixl 7 ..*

-- | Divide a fixed-precision number by an integer. This is marginally
-- more efficient than dividing two fixed-precision numbers.
(/..) :: FixedPrec e -> Integer -> FixedPrec e
(F x) /.. n = F (x `divi` n)
infixl 7 /..
  
-- | Return the positive fractional part of a fixed-precision
-- number. The result is always in [0,1), regardless of the sign of
-- the input.
fractional :: (Precision e) => FixedPrec e -> FixedPrec e
fractional a@(F x) = F (x `mod` one) where
  p = getprec a
  one = (decshiftL p 1)

-- | Solve the quadratic equation /x/^2 + /bx/ + /c/ = 0 with maximal
-- possible precision, using a numerically stable method. Return the
-- pair (/x1/, /x2/) of solutions with /x1/ <= /x2/, or 'Nothing' if no
-- solution exists.
-- 
-- This is far more precise, and probably more efficient, than naively
-- using the quadratic formula.
solve_quadratic :: (Precision e) => FixedPrec e -> FixedPrec e -> Maybe (FixedPrec e, FixedPrec e)
solve_quadratic b c = do
  let p = getprec b + 3
      b' = floor (b * 10^p)
      c' = floor (c * 100^p)
  x2' <- intquad b' c'
  let x1' = -b' - x2'
  return (fromInteger x1' / 10^p, fromInteger x2' / 10^p)

-- ----------------------------------------------------------------------
-- ** Power series

-- | Define a list of rational numbers (i.e., the coefficients of a
-- power series) from a recursive formula.
accs :: (Rational -> Integer -> Rational) -> [Rational]
accs f = scanl f 1 [1..]
  
-- | The power series stops when the last term is smaller than the
-- precision. This is accurate for alternating and decreasing series,
-- and provided |/x/| ≤ 1.
powerseries :: (Precision e) => [Rational] -> FixedPrec e -> FixedPrec e
powerseries [] x = 0
powerseries (h:t) x 
  -- we could improve upon this by checking that h' * x^n < 1.
  | h' == 0   = a
  | otherwise = a + x * powerseries t x
  where
    a@(F h') = fromRational h

-- ----------------------------------------------------------------------
-- ** Limited domain implementations
    
-- $ The following are implementations of various analytic functions
-- by power series. These implementations have limited domain, and do
-- not compensate for round-off errors.

-- | The Taylor series for sin /x/, centered at 0. This implementation
-- works for |/x/| ≤ 1.
sin_p :: (Precision e) => FixedPrec e -> FixedPrec e
sin_p x = x * powerseries (accs (\a n -> -a * (1 % (2*n*(2*n+1))))) (x^2)
  
-- | The Taylor series for cos /x/, centered at 0. This implementation
-- works for |/x/| ≤ 1.
cos_p :: (Precision e) => FixedPrec e -> FixedPrec e
cos_p x = powerseries (accs (\a n -> -a * (1 % (2*n*(2*n-1))))) (x^2)

-- | The Taylor series for [exp /x/], centered at 0. This
-- implementation works for |/x/| ≤ 1.
exp_p :: (Precision e) => FixedPrec e -> FixedPrec e
exp_p x = powerseries (accs (\a n -> a * (1 % n))) x

-- | The Taylor series for log /x/, centered at 1. This
-- implementation works for |/x/ − 1| ≤ 1/4.
log_p :: (Precision e) => FixedPrec e -> FixedPrec e
log_p x = (x-1) * powerseries [ 1 % ((-4)^n * (n+1)) | n <- [0..] ] (4*(x-1))

-- | The Taylor series for atan /x/, centered at 0. This
-- implementation works for |/x/| ≤ 0.44.
atan_p :: (Precision e) => FixedPrec e -> FixedPrec e
atan_p x = x * powerseries [ 1 % ((-5)^n * (2*n+1)) | n <- [0..]] (5*x*x)

-- | The Taylor series for atan /x/, centered at 0. This
-- implementation works for |/x/| ≤ 0.2, and is faster, in that range,
-- than 'atan_p'.
atan_p2 :: (Precision e) => FixedPrec e -> FixedPrec e
atan_p2 x = x * powerseries [ 1 % ((-25)^n * (2*n+1)) | n <- [0..]] (25*x*x)

-- | The Taylor series for atan /x/, centered at 0. This
-- implementation works for |/x/| ≤ 1/239, and is faster, in that
-- range, than 'atan_p2'.
atan_p3 :: (Precision e) => FixedPrec e -> FixedPrec e
atan_p3 x = x * powerseries [ 1 % ((-57121)^n * (2*n+1)) | n <- [0..]] (57121*x*x)

-- ----------------------------------------------------------------------
-- ** Raw versions of analytic functions
  
-- $ The following functions are \"raw\", in the sense that they do
-- not try to compensate for accumulated round-off errors. They must
-- all be wrapped in 'with_added_digits', or 'upcast' and 'downcast',
-- to produce more accurate versions.
--
-- Each function is defined on its natural domain.

-- | Raw implementation of the sine function.
sin_raw :: (Precision e) => FixedPrec e -> FixedPrec e
sin_raw x 
  | -1 <= x && x < 1 = sin_p x -- bypass slow domain reduction
  | m == 0    = sin_p x'
  | m == 1    = cos_p x'
  | m == 2    = -sin_p x'
  | otherwise = -cos_p x'
  where
    n = round (x / p2)
    m = n `mod` 4
    x' = x - n ..* p2
    p2 = pi /.. 2

-- | Raw implementation of the cosine function.
cos_raw :: (Precision e) => FixedPrec e -> FixedPrec e
cos_raw x
  | -1 <= x && x < 1 = cos_p x -- bypass slow domain reduction
  | m == 0    = cos_p x'
  | m == 1    = -sin_p x'
  | m == 2    = -cos_p x'
  | otherwise = sin_p x'
  where
    n = round (x / p2)
    m = n `mod` 4
    x' = x - n ..* p2
    p2 = pi /.. 2

-- | Raw implementation of the exponential function. Note: the loss of
-- precision is much more substantial than that of the other raw
-- functions in this section. This is due to the multiplication of
-- fixed-precision values by numbers much larger than 1.
exp_raw :: (Precision e) => FixedPrec e -> FixedPrec e
exp_raw x
  | -1 <= x && x <= 1  = exp_p x
  | otherwise = exp_raw (x/2) ^2

-- | Raw implementation of the natural logarithm.
log_raw :: (Precision e) => FixedPrec e -> FixedPrec e
log_raw x
  | x <= 0 = error "log: argument out of range"
  | 0.75 <= x && x <= 1.25 = log_p x
  | x > 3.5 = fromInteger n + log r
  | x > 1 = 0.5 + log (x / e2)
  | otherwise = - log (1 / x)
  where
    e2 = exp_p 0.5
    e = exp_p 1
    (n, r) = floorlog e x

-- | Raw implementation of the power function. This is subject to
-- similar loss of precision as the 'exp_raw' function.
power_raw :: (Precision e) => FixedPrec e -> FixedPrec e -> FixedPrec e
power_raw x y = exp_raw (log_raw x * y)

-- | Raw implementation of the 'logBase' function. This is subject to
-- similar loss of precision as the 'exp_raw' function.
logBase_raw :: (Precision e) => FixedPrec e -> FixedPrec e -> FixedPrec e
logBase_raw x y = log y / log x

-- | Raw implementation of the square root.
sqrt_raw :: (Precision e) => FixedPrec e -> FixedPrec e
sqrt_raw a@(F x) 
  | a >= 0  = F y 
  | otherwise = error "sqrt: argument out of range"
  where
    p = getprec a
    y = intsqrt (x * 10^p)

-- | Raw implementation of the inverse tangent.
atan_raw :: (Precision e) => FixedPrec e -> FixedPrec e
atan_raw x
  | -0.44 <= x && x <= 0.44 = atan_p x
  | x < 0     = -atan (-x)
  | x >= 2.27  = p2 - atan_p (1/x)
  | otherwise = p4 + atan_p ((x-1)/(x+1))
  where
    p2 = pi /.. 2
    p4 = pi /.. 4

-- | Raw implementation of π.
pi_raw :: (Precision e) => FixedPrec e
pi_raw = 16 ..* atan_p2 (1/5) - 4 ..* atan_p3 (1/239)
  
-- | Raw implementation of the inverse sine function.
asin_raw :: (Precision e) => FixedPrec e -> FixedPrec e
asin_raw x 
  | -0.7 <= x && x <= 0.7 = atan (x / cos)
  | x > 0 && x <= 1   = p2 - atan (cos / x)
  | x < 0 && x >= -1  = -p2 - atan (cos / x)
  | otherwise = error "asin: argument out of range"
  where
    cos = sqrt(1 - x^2)
    p2 = pi /.. 2

-- | Raw implementation of the inverse cosine function.
acos_raw :: (Precision e) => FixedPrec e -> FixedPrec e
acos_raw x
  | -0.7 <= x && x <= 0.7 = p2 - atan (x / sin)
  | x > 0 && x <= 1   = atan (sin / x)
  | x < 0 && x >= -1  = pi + atan (sin / x)
  | otherwise = error "acos: argument out of range"
  where
    sin = sqrt(1 - x^2)
    p2 = pi /.. 2

-- | Raw implementation of the hyperbolic sine.
sinh_raw :: (Precision e) => FixedPrec e -> FixedPrec e
sinh_raw x = (e - 1/e) /.. 2 where e = exp x

-- | Raw implementation of the hyperbolic cosine.
cosh_raw :: (Precision e) => FixedPrec e -> FixedPrec e
cosh_raw x = (e + 1/e) /.. 2 where e = exp x

-- | Raw implementation of the inverse hyperbolic tangent.
atanh_raw :: (Precision e) => FixedPrec e -> FixedPrec e
atanh_raw x = log ((1+x) / (1-x)) /.. 2

-- | Raw implementation of the inverse hyperbolic sine.
asinh_raw :: (Precision e) => FixedPrec e -> FixedPrec e
asinh_raw x = log (x + sqrt (x^2+1))

-- | Raw implementation of the inverse hyperbolic cosine.
acosh_raw :: (Precision e) => FixedPrec e -> FixedPrec e
acosh_raw x 
  | x >= 1 = log (x + sqrt (x^2-1))
  | otherwise = error "acosh: argument out of range"

-- ----------------------------------------------------------------------
-- Instance declarations

instance (Precision e) => Show (FixedPrec e) where
  show a@(F x) = sign ++ integral ++ "." ++ fractional where
    x' = abs x
    sign = if x < 0 then "-" else ""
    integral = show (dectruncR p x')
    fractional' = show $ x' `mod` (decshiftL p 1)
    fractional = pad_to_length p '0' fractional'
    p = getprec a
    pad_to_length p c l = replicate (p - length l) c ++ l

instance (Precision e) => Num (FixedPrec e) where
  F x + F y = F (x+y)
  a@(F x) * F y = F (decshiftR (getprec a) (x*y))
  F x - F y = F (x-y)
  negate (F x) = F (negate x)
  abs (F x) = F (abs x)
  signum (F x) = fromInteger (signum x)
  fromInteger x = y where
    y = F (decshiftL p x) where
    p = getprec y

instance (Precision e) => Fractional (FixedPrec e) where
  a@(F x) / F y = F ((10^p * x) `divi` y) where
    p = getprec a
  fromRational r = fromInteger num / fromInteger denom where
    num = numerator r
    denom = denominator r
                   
instance (Precision e) => Real (FixedPrec e) where            
  toRational a@(F x) = x % one where
    p = getprec a
    one = (decshiftL p 1)
                
instance (Precision e) => RealFrac (FixedPrec e) where
  properFraction a@(F x) = (fromInteger n, F y) where
    p = getprec a
    y = x `rem` one
    n = x `quot` one
    one = (decshiftL p 1)
    
instance (Precision e) => Floating (FixedPrec e) where
  pi = downcast pi_raw
  sin = downcast . sin_raw . upcast
  cos = downcast . cos_raw . upcast
  log = downcast . log_raw . upcast
  sqrt = downcast . sqrt_raw . upcast
  atan = downcast . atan_raw . upcast
  asin = downcast . asin_raw . upcast
  acos = downcast . acos_raw . upcast
  sinh = downcast . sinh_raw . upcast
  cosh = downcast . cosh_raw . upcast
  atanh = downcast . atanh_raw . upcast
  asinh = downcast . asinh_raw . upcast
  acosh = downcast . acosh_raw . upcast
  
  exp x
    | x <= 1  = exp_raw x
    | otherwise = with_added_digits d (cast . exp_raw) x
    where
      -- we need to add digits to the internal calculation, because
      -- exp_raw multiplies numbers much larger than 1.
      d = 1 + ceiling (x * 0.45)  

  x ** y
    | x <= 1  = power_raw x y
    | otherwise = with_added_digits d (cast . (power_raw (cast x))) y
    where
      -- we don't need a lot of precision in the logarithm here,
      -- because it is only to determine the number of digits
      d = 1 + ceiling (0.45 * y * cast (log_raw (cast x :: FixedPrec P10)))
 
  logBase x y
    | (x < 0.36 || x > 2.72) && lo < y && y < hi = downcast (logBase_raw (upcast x) (upcast y))
    | otherwise = with_added_digits d (cast . (logBase_raw (cast x))) y
    where
      dx = ceiling (-0.45 * log (abs (log_double x)))
      dy = ceiling (0.45 * log (abs (log_double y)))
      d = max dx (2*dx + dy)
      lo = 10000000000
      hi = 0.0000000001

instance Precision e => Random (FixedPrec e) where
  randomR (lo, hi) g = (x, g1) where
    n = getprec x  -- precision in decimal digits
    lo_n = floor (lo * 10^n)
    hi_n = floor (hi * 10^n)
    (x_n, g1) = randomR (lo_n, hi_n) g
    x = 0.1^n * fromInteger x_n
    
  random = randomR (0, 1)
