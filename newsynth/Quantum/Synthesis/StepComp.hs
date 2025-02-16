-- | This module provides /step computations/.  These are computations
-- that can be run, stopped, resumed, parallelized, and/or bounded in
-- runtime.

module Quantum.Synthesis.StepComp where

import Control.Applicative (Applicative(..))
import Control.Monad (liftM, ap)

-- ----------------------------------------------------------------------
-- * A monad for step computations

-- | A step computation can be run for a specified number of steps,
-- stopped, continued, and interleaved. Such a computation produces
-- \"ticks\" at user-defined intervals, which must be consumed by the
-- environment for the computation to continue.
data StepComp a = 
  Done a              -- ^ Terminate with a result.
  | Tick (StepComp a) -- ^ Produce a \"tick\", then resume the
                      -- computation.
    
instance Monad StepComp where
  return a = Done a
  Done a >>= g = g a
  Tick f >>= g = Tick (f >>= g)
  
instance Applicative StepComp where
  pure = return
  (<*>) = ap

instance Functor StepComp where
  fmap = liftM

instance Show a => Show (StepComp a) where
  show (Done a) = "Done(" ++ show a ++ ")"
  show (Tick c) = "Incomplete"

-- ----------------------------------------------------------------------
-- * Basic operations

-- | Issue a single tick.
tick :: StepComp ()
tick = Tick (Done ())

-- | Run the step computation for one step.
untick :: StepComp a -> StepComp a
untick (Done a) = (Done a)
untick (Tick c) = c

-- | Fast-forward a computation by /n/ steps. This is essentially
-- equivalent to doing /n/ 'untick' operations.
forward :: Int -> StepComp a -> StepComp a
forward 0 c = c
forward n (Done a) = Done a
forward n c = forward (n-1) (untick c)

-- | Check whether a step computation is completed.
is_done :: StepComp a -> Bool
is_done (Done a) = True
is_done (Tick c) = False

-- | Retrieve the result of a completed step computation (or 'Nothing'
-- if it is incomplete).
get_result :: StepComp a -> Maybe a
get_result (Done a) = Just a
get_result (Tick c) = Nothing

-- | Run a subsidiary computation for up to /n/ steps, translated into
-- an equal number of steps of the parent computation.
subtask :: Int -> StepComp a -> StepComp (StepComp a)
subtask n c | n <= 0 = Done c
subtask n (Done a) = Done (Done a)
subtask n (Tick c) = Tick (subtask (n-1) c)

-- | Run a subtask, speeding it up by a factor of /n/ ≥ 1. Every 1 tick of
-- the calling task corresponds to up to /n/ ticks of the subtask.
speedup :: Int -> StepComp a -> StepComp a
speedup n (Done a) = Done a
speedup n (Tick c) = do
  tick
  speedup n (forward (n-1) c)

-- | Run two step computations in parallel, until one branch
-- terminates.  Tick allocation is associative: each tick of the
-- parent function translates into one tick for each subcomputation.
-- Therefore, when running, e.g., three subcomputations in parallel,
-- they will each receive an approximately equal number of ticks.
parallel :: StepComp a -> StepComp b -> StepComp (Either (a, StepComp b) (StepComp a, b))
parallel (Done a) c = Done (Left (a, c))
parallel c (Done b) = Done (Right (c, b))
parallel (Tick c) (Tick c') = Tick (parallel c c')

-- | Wrap a step computation to return the number of steps, in
-- addition to the result.
with_counter :: StepComp a -> StepComp (a, Int)
with_counter c = aux 0 c where
  aux n (Done a) = return (a, n)
  aux n (Tick c) = do
    n `seq` tick
    aux (n+1) c    

-- ----------------------------------------------------------------------
-- ** Run functions

-- | Run a step computation until it finishes.
run :: StepComp a -> a
run (Done a) = a
run (Tick c) = run c

-- | Run a step computation until it finishes, and also return the
-- number of steps it took. 
run_with_steps :: StepComp a -> (a, Int)
run_with_steps = run . with_counter

-- | Run a step computation for at most /n/ steps.
run_bounded :: Int -> StepComp a -> Maybe a
run_bounded n = get_result . forward n

-- ----------------------------------------------------------------------
-- * Other operations

-- | Do nothing, forever.
diverge :: StepComp a
diverge = tick >> diverge

-- | Run two step computations in parallel. The first one to complete
-- becomes the result of the computation.
parallel_first :: StepComp a -> StepComp a -> StepComp a
parallel_first c1 c2 = do
  r <- parallel c1 c2
  case r of
    Left (a, _) -> return a
    Right (_, a) -> return a

-- | Run two step computations in parallel. If either computation
-- returns 'Nothing', return 'Nothing'. Otherwise, return the pair of
-- results.
parallel_maybe :: StepComp (Maybe a) -> StepComp (Maybe b) -> StepComp (Maybe (a,b))
parallel_maybe c1 c2 = do
  res <- parallel c1 c2
  case res of
    Left (Nothing, c2) -> return Nothing
    Right (c1, Nothing) -> return Nothing
    Left (Just a, c2) -> do
      b <- c2
      case b of
        Nothing -> return Nothing
        Just b -> return (Just (a,b))
    Right (c1, Just b) -> do
      a <- c1
      case a of
        Nothing -> return Nothing
        Just a -> return (Just (a,b))

-- | Run a list of step computations in parallel. If any computation
-- returns 'Nothing', return 'Nothing'. Otherwise, return the list of
-- results.
parallel_list_maybe :: [StepComp (Maybe a)] -> StepComp (Maybe [a])
parallel_list_maybe [] = return (Just [])
parallel_list_maybe (h:t) = do
  res <- parallel_maybe h c2
  return $ do
    (h',t') <- res
    return (h':t')
  where
    c2 = parallel_list_maybe t
  
