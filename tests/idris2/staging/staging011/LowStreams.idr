module LowStreams

import Language.Staged.Low
import Language.Staged.Low.C

-- Examples from "Closure-Free Functional Programming in a Two-Level Type
-- Theory" (Kovács, ICFP 2024), with Low as the closure free object language

--------------------------------------------------------------------------
-- Pull streams (section 4, without the generic sums of products).  A
-- stream is a state machine: an initial state and a step function, both
-- generating low code.  The state type is existential; it is a value type,
-- so it has a LowRep.  All the stream combinators run at compile time, and a
-- pipeline becomes a single first order loop: no closures, no lists.

data Step a s = Stop | Skip s | Yield a s

data Pull : Type -> Type where
  MkPull : {0 s : Type} -> LowRep s => Low s -> (Low s -> Gen (Step a (Low s))) -> Pull a

range : Low Int -> Low Int -> Pull (Low Int)
range lo hi = MkPull lo $ \s => MkGen $ \k =>
  [|| if ~s > ~hi then ~(k Stop) else ~(k (Yield s [|| ~s + 1 ||])) ||]

mapP : (a -> b) -> Pull a -> Pull b
mapP f (MkPull s0 step) = MkPull s0 $ \s => do
  st <- step s
  pure $ case st of
              Stop => Stop
              Skip s' => Skip s'
              Yield a s' => Yield (f a) s'

filterP : (Low a -> Low Bool) -> Pull (Low a) -> Pull (Low a)
filterP p (MkPull s0 step) = MkPull s0 $ \s => do
  st <- step s
  case st of
       Yield x s' => MkGen $ \k => [|| if ~(p x) then ~(k (Yield x s')) else ~(k (Skip s')) ||]
       _ => pure st

-- The consumer: a loop, a recursive low function of the accumulator and the
-- state
foldlP : LowRep b => (Low b -> a -> Low b) -> Low b -> Pull a -> Low b
foldlP f z (MkPull s0 step) = runGen $ do
  loop <- genRecNamed "loop" $ \loop =>
            [|| \acc, s => ~(unGen (step [|| s ||]) $ \st => case st of
                               Stop => [|| acc ||]
                               Skip s' => [|| ~loop acc ~s' ||]
                               Yield a s' => [|| ~loop ~(f [|| acc ||] a) ~s' ||]) ||]
  pure [|| ~loop ~z ~s0 ||]

sumP : Pull (Low Int) -> Low Int
sumP = foldlP (\acc, x => [|| ~acc + ~x ||]) [|| 0 ||]

-- The sum of the squares of the even numbers in 1 .. n
sumEvenSquares : Low (Int -> Int)
sumEvenSquares = [|| \n => ~(sumP (mapP (\x => [|| ~x * ~x ||])
                                (filterP (\x => [|| ~x `mod` 2 == 0 ||])
                                   (range [|| 1 ||] [|| n ||])))) ||]

--------------------------------------------------------------------------
-- Monads by binding time improvement (section 3.3): Maybe in the object
-- language, a Maybe monad transformer at the meta level.  The binds are
-- computed at compile time; only the case splits remain.

data MaybeM a = NothingM | JustM a

record MaybeT a where
  constructor MkMaybeT
  runMaybeT : Gen (MaybeM a)

Functor MaybeT where
  map f (MkMaybeT g) = MkMaybeT (map (\m => case m of { NothingM => NothingM; JustM a => JustM (f a) }) g)

Applicative MaybeT where
  pure a = MkMaybeT (pure (JustM a))
  mf <*> ma = MkMaybeT $ do
    NothingM <- runMaybeT mf
      | JustM f => runMaybeT (map f ma)
    pure NothingM

Monad MaybeT where
  MkMaybeT g >>= f = MkMaybeT (g >>= \m => case m of { NothingM => pure NothingM; JustM a => runMaybeT (f a) })

-- up: case split an object level Maybe; down: build one
up : LowRep a => Low (Maybe a) -> MaybeT (Low a)
up m = MkMaybeT $ MkGen $ \k => [|| case ~m of
                                       Nothing => ~(k NothingM)
                                       Just a => ~(k (JustM [|| a ||])) ||]

down : LowRep a => MaybeT (Low a) -> Low (Maybe a)
down (MkMaybeT (MkGen g)) = g (\r => case r of
                                          NothingM => [|| Nothing ||]
                                          JustM a => [|| Just ~a ||])

safeDiv : Low Int -> Low Int -> MaybeT (Low Int)
safeDiv x y = up [|| if ~y == 0 then Nothing else Just (~x `div` ~y) ||]

-- (a / b) / c + 1, failing on a division by zero
divDiv : Low (Int -> Int -> Int -> Maybe Int)
divDiv = [|| \a, b, c => ~(down $ do
                              q <- safeDiv [|| a ||] [|| b ||]
                              r <- safeDiv q [|| c ||]
                              pure [|| ~r + 1 ||]) ||]

--------------------------------------------------------------------------
-- Foreign C functions can be used in low code

%foreign "C:sqrt,libm 6"
c_sqrt : Double -> Double

hypot : Low (Double -> Double -> Double)
hypot = [|| \x, y => c_sqrt (x * x + y * y) ||]

main : IO ()
main = do
  putStrLn "---- sumEvenSquares"
  putStr ~(lowString (lowPretty (reflect sumEvenSquares)))
  putStr ~(lowString (toC "sum_even_squares" (reflect sumEvenSquares)))
  putStrLn "---- divDiv"
  putStr ~(lowString (lowPretty (reflect divDiv)))
  putStrLn "---- hypot"
  putStr ~(lowString (toC "hypot2" (reflect hypot)))
  putStrLn "---- run"
  printLn ((~sumEvenSquares) 10)
  printLn ((~divDiv) 100 5 2, (~divDiv) 100 0 2, (~divDiv) 100 5 0)
  printLn ((~hypot) 3 4)
