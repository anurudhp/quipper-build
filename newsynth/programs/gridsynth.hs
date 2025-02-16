{-# LANGUAGE BangPatterns #-}

-- | This module provides a command line interface to the
-- single-qubit approximate synthesis algorithm.

module Main where

import Quantum.Synthesis.SymReal
import Quantum.Synthesis.CliffordT
import Quantum.Synthesis.Ring
import Quantum.Synthesis.Matrix
import Quantum.Synthesis.LaTeX
import Quantum.Synthesis.GridSynth
import Quantum.Synthesis.GridProblems

import CommandLine

-- import other stuff
import Control.Monad
import Data.Time
import System.Console.GetOpt
import System.Environment    
import System.Exit
import System.IO
import System.Random
import Text.Printf

-- ----------------------------------------------------------------------
-- * Option processing

-- | A data type to hold values set by command line options.
data Options = Options {
  opt_digits :: Maybe Double,  -- ^ Requested precision in decimal digits (default: 10).
  opt_theta  :: Maybe SymReal, -- ^ The angle θ to approximate.
  opt_phase  :: Bool,          -- ^ Decompose up to a global phase?
  opt_effort :: Int,           -- ^ The amount of \"effort\" to spend on factoring.
  opt_hex    :: Bool,          -- ^ Output operator in hex coding? (default: ASCII).
  opt_stats  :: Bool,          -- ^ Output statistics?
  opt_latex  :: Bool,          -- ^ Use LaTeX format?
  opt_table  :: Bool,          -- ^ Generate the table of results for the paper?
  opt_count  :: Maybe Int,     -- ^ Repeat count for --table mode (default: 50).
  opt_rseed  :: Maybe StdGen   -- ^ An optional random seed.
} deriving Show

-- | The initial default options.
defaultOptions :: Options
defaultOptions = Options
  { opt_digits = Nothing,
    opt_theta  = Nothing,
    opt_phase  = False,
    opt_effort = 25,
    opt_hex    = False,
    opt_stats  = False,
    opt_latex  = False,
    opt_table  = False,
    opt_count  = Nothing,
    opt_rseed  = Nothing
  }

-- | The list of command line options, in the format required by 'getOpt'.
options :: [OptDescr (Options -> IO Options)]
options =
  [ Option ['h'] ["help"]    (NoArg help)              "print usage info and exit",
    Option ['d'] ["digits"]  (ReqArg digits "<n>")     "set precision in decimal digits (default: 10)",
    Option ['b'] ["bits"]    (ReqArg bits "<n>")       "set precision in bits",
    Option ['e'] ["epsilon"] (ReqArg epsilon "<n>")    "set precision as epsilon (default: 1e-10)",
    Option ['p'] ["phase"]   (NoArg phase)             "decompose up to a global phase (default: no)",
    Option ['f'] ["effort"]  (ReqArg effort "\"<n>\"") "how hard to try to factor (default: 25)",
    Option ['x'] ["hex"]     (NoArg hex)               "output hexadecimal coding (default: ASCII)",
    Option ['s'] ["stats"]   (NoArg stats)             "output statistics",
    Option ['l'] ["latex"]   (NoArg latex)             "use LaTeX output format",
    Option ['t'] ["table"]   (NoArg table)             "generate the table of results for the article",
    Option ['c'] ["count"]   (ReqArg count "<n>")      "repeat count for --table mode (default: 50)",
    Option ['r'] ["rseed"]   (ReqArg rseed "\"<s>\"")  "set optional random seed (default: random)"
  ]
    where
      help :: Options -> IO Options
      help o = do
        usage
        exitSuccess

      digits :: String -> Options -> IO Options
      digits string o =
        case parse_double string of
          Just n | n >= 0 -> return o { opt_digits = Just n }
          Just n -> optfail ("Number of digits must not be negative -- " ++ string ++ "\n")
          _ -> optfail ("Invalid digits -- " ++ string ++ "\n")

      bits :: String -> Options -> IO Options
      bits string o =
        case parse_double string of
          Just n | n >= 0 -> return o { opt_digits = Just (n * logBase 10 2) }
          Just n -> optfail ("Number of bits must not be negative -- " ++ string ++ "\n")
          _ -> optfail ("Invalid bits -- " ++ string ++ "\n")

      epsilon :: String -> Options -> IO Options
      epsilon string o =
        case parse_double string of
          Just eps | eps < 1 && eps > 0 -> return o { opt_digits = Just (-logBase 10 eps) }
          Just n -> optfail ("Epsilon must be between 0 and 1 -- " ++ string ++ "\n")
          _ -> optfail ("Invalid epsilon -- " ++ string ++ "\n")

      phase :: Options -> IO Options
      phase o = return o { opt_phase = True }

      effort :: String -> Options -> IO Options
      effort string o =
        case parse_int string of
          Just e | e > 0 -> return o { opt_effort = e }
          Just e -> optfail ("Effort must be positive -- " ++ string ++ "\n")
          _ -> optfail ("Invalid effort -- " ++ string ++ "\n")

      hex :: Options -> IO Options
      hex o = return o { opt_hex = True }

      stats :: Options -> IO Options
      stats o = return o { opt_stats = True }

      latex :: Options -> IO Options
      latex o = return o { opt_latex = True }

      table :: Options -> IO Options
      table o = return o { opt_table = True }

      count :: String -> Options -> IO Options
      count string o =
        case parse_int string of
          Just n | n >= 1 -> return o { opt_count = Just n }
          Just n -> optfail ("Invalid count, must be positive -- " ++ string ++ "\n")
          _ -> optfail ("Invalid count -- " ++ string ++ "\n")

      rseed :: String -> Options -> IO Options
      rseed string o =
        case reads string of
          [(g, "")] -> return o { opt_rseed = Just g }
          _ -> optfail ("Invalid random seed -- " ++ string ++ "\n")

-- | Process /argv/-style command line options into an 'Options' structure.
dopts :: [String] -> IO Options
dopts argv = do
  let (o, args, errs) = getOpt Permute options argv
  opts <- foldM (flip id) defaultOptions o
  when (errs /= []) $ do
    optfail (concat errs)
  case args of
    [] -> return opts
    [string] -> do
      case parse_SymReal string of
        Just theta -> return opts { opt_theta = Just theta }
        _ -> optfail ("Invalid theta -- " ++ string ++ "\n")
    h1:h2:[] -> optfail ("Too many non-option arguments -- " ++ h1 ++ ", " ++ h2 ++ "\n")
    h1:h2:_ -> optfail ("Too many non-option arguments -- " ++ h1 ++ ", " ++ h2 ++ "...\n")

-- | Print usage message to 'stdout'.
usage :: IO ()
usage = do
  putStr (usageInfo header options) 
    where header = 
            "Usage: gridsynth [OPTION...] <theta>\n"
            ++ "Arguments:\n"
            ++ " <theta>                   z-rotation angle. May be symbolic, e.g. pi/128\n"
            ++ "Options:"

-- ----------------------------------------------------------------------
-- * The main function

-- | Main function: read options, then execute the appropriate tasks.
main :: IO()
main = do
  -- Read options.
  argv <- getArgs
  options <- dopts argv
  case opt_table options of
    False -> main_default options
    True -> main_maketable options
    
-- ----------------------------------------------------------------------
-- ** Default main

-- | The default task for the main function: synthesize one angle, for
-- one given precision, possibly with outputting some statistics.
main_default :: Options -> IO()
main_default options = do  
  let digits = case opt_digits options of
        Nothing -> 10
        Just d -> d
  let prec = digits * logBase 2 10
  theta <- case opt_theta options of
        Nothing -> optfail "Missing argument: theta.\n"
        Just t -> return t
  case opt_count options of
        Nothing -> return ()
        Just c -> optfail "Option -c is only supported with --table.\n"
  let exponent = ceiling digits
  let l = opt_latex options
  let effort = opt_effort options
  let gridsynth_fun = case opt_phase options of
        False -> gridsynth_stats
        True -> gridsynth_phase_stats
  
  -- Set random seed.
  g <- case opt_rseed options of
    Nothing -> newStdGen
    Just g -> return g
  
  -- Payload.
  t0 <- getCurrentTime
  let (m,err,cinfo) = gridsynth_fun g prec theta effort
      gates = case opt_phase options of
        False -> to_gates m
        True -> strip_phases (to_gates m)
  if opt_hex options then
    printf "%x\n" (convert gates :: Integer)
    else if opt_latex options then
    putStrLn (if gates == [] then "I" else showlatex gates)
    else
    putStrLn (if gates == [] then "I" else convert gates)
  t1 <- getCurrentTime

  -- Print optional statistics
  let ct = length cinfo
  let tcount = length $ filter (==T) gates
  let tlower = last [ tcount | (u, tcount, status) <- cinfo, status /= Fail ]
  let secs = diffUTCTime t1 t0
  let err_d = case err of
        Nothing -> Nothing
        Just x -> Just (x * logBase 10 2)
  
  when (opt_stats options) $ do
    putStrLn ("Random seed: " ++ show g)
    putStrLn ("T-count: " ++ show tcount)
    putStrLn ("Lower bound on T-count: " ++ show tlower)
    putStrLn ("Theta: " ++ showf l theta)
    putStrLn ("Epsilon: " ++ showf_exp l 10 exponent (Just digits))
    putStrLn ("Matrix: " ++ showf l m)
    putStrLn ("Actual error: " ++ showf_exp l 10 exponent err_d)
    putStrLn ("Runtime: " ++ show secs)
    putStrLn ("Candidates tried: " ++ show ct ++ " ("
              ++ show (length [u | (u, tc, Fail) <- cinfo]) ++ " failed, "
              ++ show (length [u | (u, tc, Timeout) <- cinfo]) ++ " timed out, "
              ++ show (length [u | (u, tc, Success) <- cinfo]) ++ " succeeded)")
    putStrLn ("Time/candidate: " ++ show (secs / fromIntegral ct))

-- ----------------------------------------------------------------------
-- ** Generate output in LaTeX table format

-- | Run one instance of the algorithm, using the given theta, and
-- measuring various things including the running time.  Note: here,
-- the precision is expressed in /decimal/, not binary, digits.
-- 
-- The inputs are, respectively: a source of randomness, the angle θ,
-- the precision in decimal digits, an amount of effort to spend on
-- factoring, and a boolean flag determining whether we should
-- decompose up to a global phase. The outputs are, respectively: the
-- approximating operator /U/; the approximating circuit, log[sub 0.5]
-- of the actual approximation error (or 'Nothing' if the error is 0),
-- the number of candidates tried, the /T/-count of /U/, the computed
-- lower bound for the /T/-count, and the runtime in seconds.
one_run :: (RandomGen g, Show g) => g -> SymReal -> Double -> Int -> Bool -> IO (U2 DOmega, [Gate], Maybe Double, Int, Integer, Integer, Double)
one_run g theta prec_d effort phase = do
  let gridsynth_fun = case phase of
        False -> gridsynth_stats
        True -> gridsynth_phase_stats
  let !prec = prec_d * logBase 2 10
  let !exponent = floor prec_d
  putStrLn ("% Epsilon: " ++ show_exp 10 exponent (Just prec_d))
  putStrLn ("% Theta: " ++ show theta)
  putStrLn ("% Random seed: " ++ show g)
  t0 <- getCurrentTime
  let (op, err, cinfo) = gridsynth_fun g prec theta effort
      circ = synthesis_u2 op
      tcount = fromIntegral $ length $ filter (==T) circ
  putStrLn ("% T-count: " ++ show tcount)
  t1 <- getCurrentTime
  let secs = diffUTCTime t1 t0
      ct = length cinfo
      -- find the first candidate that *might* have succeeded - this gives
      -- a lower bound on the shorest possible T-count.
      tlower = last [ tcount | (u, tcount, status) <- cinfo, status /= Fail ]
      ((u, _), (t, _)) = fromOperator op
  let err_d = case err of
        Nothing -> Nothing
        Just x -> Just (x * logBase 10 2)
  putStrLn ("% Lower bound on T-count: " ++ show tlower)
  putStrLn ("% Circuit: " ++ if circ == [] then "I" else convert circ)
  putStrLn ("% u: " ++ showlatex u)
  putStrLn ("% t: " ++ showlatex t)
  putStrLn ("% Actual error: " ++ show_exp 10 exponent err_d)
  putStrLn ("% Runtime: " ++ show secs)
  putStrLn ("% Candidates tried: " ++ show ct ++ " ("
            ++ show (length [u | (u, tc, Fail) <- cinfo]) ++ " failed, "
            ++ show (length [u | (u, tc, Timeout) <- cinfo]) ++ " timed out, "
            ++ show (length [u | (u, tc, Success) <- cinfo]) ++ " succeeded)")
  putStrLn ("% Time/candidate: " ++ show (secs / fromIntegral ct))
  putStrLn ""
  hFlush stdout
  return (op, circ, err, ct, tcount, tlower, fromRational (toRational secs))

-- | Repeat the algorithm /n/ times with the same parameters but
-- random angles, to average things like running time. The inputs are,
-- respectively: a source of randomness, a repeat count, the precision
-- in decimal digits, an amount of effort to spend on factoring, and a
-- flag that determines whether to factor up to a global phase.
many_runs :: (RandomGen g, Show g) => g -> Int -> Double -> Int -> Bool -> IO ()
many_runs g n prec_d effort phase = do
  let gs = take n $ expand_seed g
  results <- sequence $ do
    g <- gs
    return $ do
      let (theta', g') = randomR (0, 2047) g
      let theta = fromInteger theta' * pi / 2048 :: SymReal
      one_run g' theta prec_d effort phase
  -- Output the LaTeX of one row of the table
  let (_,_,err,_,tcount,tlower,_) = head results
      total_time = sum [ t | (_,_,_,_,_,_,t) <- results ]
      total_candidates = sum [ ct | (_,_,_,ct,_,_,_) <- results ]
      avg_time = total_time / fromIntegral n
      avg_candidates = fromIntegral total_candidates / fromIntegral n :: Double
      time_per_candidate = total_time / fromIntegral total_candidates
      err_d = case err of
        Nothing -> Nothing
        Just x -> Just (x * logBase 10 2)
      exponent = floor prec_d
  putStrPad 30 (showlatex_exp 5 exponent (Just prec_d) ++ " &")
  putStrLn ("% Epsilon")
  putStrPad 30 (show tcount ++ " &")
  putStrLn ("% T-count")
  putStrPad 30 ("\\geq " ++ show tlower ++ " &")
  putStrLn ("% Lower bound on T-count")
  putStrPad 30 (showlatex_exp 5 exponent err_d ++ " &")
  putStrLn ("% Actual error")
  putStrPad 30 (printf "%0.4fs" avg_time ++ " &")
  putStrLn ("% Runtime, averaged over " ++ show n ++ " runs")
  putStrPad 30 (printf "%0.1f" avg_candidates ++ " &")
  putStrLn ("% Candidates tried, averaged over " ++ show n ++ " runs")
  putStrPad 30 (printf "%0.4fs" time_per_candidate ++ " \\\\")
  putStrLn ("% Time per candidate, averaged over " ++ show n ++ " runs")
  putStrLn ""
  putStrLn "% ----------------------------------------------------------------------"
  putStrLn ""
  hFlush stdout
  return ()

-- | Generate the table of \"Experimental Results\" used in the
-- article.
main_maketable :: Options -> IO ()
main_maketable options = do
  -- Read some parameters.
  let theta = case opt_theta options of
        Nothing -> pi/128
        Just t -> t
  let count = case opt_count options of
        Nothing -> 50
        Just c -> c
  let precisions = case opt_digits options of
        Nothing -> [10, 20, 30, 40, 50, 60, 70, 80, 90, 100, 200, 500, 1000]
        Just d -> [d]
  let effort = opt_effort options
  let phase = opt_phase options
  
  -- Set random seed.
  g <- case opt_rseed options of
    Nothing -> newStdGen
    Just g -> return g
  putStrLn ("% Initial random seed: " ++ show g)
  putStrLn ""
  
  -- Expand random seed.
  let gs = expand_seed g
  
  -- Payload.
  sequence_ $ do
    (prec_d, g) <- zip precisions gs
    return $ do
      let (g1, g2) = split g
      one_run g1 theta prec_d effort phase
      many_runs g2 count prec_d effort phase

-- ----------------------------------------------------------------------
-- * Miscellaneous

-- | Round a 'RealFrac' value to the given number of decimals.                
round_to :: (RealFrac r) => Integer -> r -> r               
round_to n x = fromInteger (round (x * 10^n)) / 10^n

-- | Show the number 10[sup -/x/] in the format 10^(-n) or
-- 1.23*10^(-n), with precision /d/ and exponent -/n/. A value of
-- 'Nothing' is treated as 0.
-- 
-- For example, display @0.316*10^(-13)@ instead of @10^(-13.5)@.
show_exp :: (Show r, RealFrac r, Floating r, PrintfArg r) => Integer -> Integer -> Maybe r -> String
show_exp d n x
  | y == 1    = "10^(" ++ show (-n) ++ ")"
  | otherwise = printf ("%." ++ show d ++ "f") y ++ "*10^(" ++ show (-n) ++ ")"
  where
    y = case x of
      Nothing -> 0
      Just x -> round_to d (10 ** (fromInteger n - x))
  
-- | Show the number 10[sup -/x/] in the format @10^{-n}@ or
-- @1.23\\cdot 10^{-n}@, with precision /d/ and exponent -/n/. A value
-- of 'Nothing' is treated as 0.
showlatex_exp :: (Show r, RealFrac r, Floating r, PrintfArg r) => Integer -> Integer -> Maybe r -> String
showlatex_exp d n x 
  | y == 1    = "10^{" ++ show (-n) ++ "}"
  | otherwise = printf ("%." ++ show d ++ "f") y ++ "\\cdot 10^{" ++ show (-n) ++ "}"
  where
    y = case x of
      Nothing -> 0
      Just x -> round_to d (10 ** (fromInteger n - x))

-- | Either 'show' or 'showlatex', depending on boolean flag.
showf :: (Show a, ShowLaTeX a) => Bool -> a -> String
showf True = showlatex
showf False = show

-- | Either 'show_exp' or 'showlatex_exp', depending on boolean flag.
showf_exp :: (Show r, RealFrac r, Floating r, PrintfArg r) => Bool -> Integer -> Integer -> Maybe r -> String
showf_exp True = showlatex_exp
showf_exp False = show_exp

-- | Expand a random seed /g/ into an infinite list of random seeds.
expand_seed :: (RandomGen g) => g -> [g]      
expand_seed g = g1 : expand_seed g2 where
  (g1,g2) = split g
  
-- | Output the given string, right-padded to /n/ characters using spaces.
putStrPad :: Int -> String -> IO()
putStrPad n s = putStr (s ++ replicate (n-l) ' ')
  where
    l = length s

-- | Strip global phase gates from a word.
strip_phases :: [Gate] -> [Gate]
strip_phases [] = []
strip_phases (W:xs) = strip_phases xs
strip_phases (x:xs) = x : strip_phases xs
