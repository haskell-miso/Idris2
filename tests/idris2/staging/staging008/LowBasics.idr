module LowBasics

import Language.Staged.Low

-- Closure free staging: the quotations have type (Low t), so the generated
-- code is first order and strict, and can be reflected (see staging009)

-- The "hello world" of staging, with Low instead of Code
power : Nat -> Low Int -> Low Int
power Z _ = [|| 1 ||]
power (S k) x = [|| ~x * ~(power k x) ||]

-- Low code spliced into ordinary code runs as ordinary code
cube : Int -> Int
cube x = ~(power 3 [|| x ||])

cubeLow : Low (Int -> Int)
cubeLow = [|| \x => ~(power 3 [|| x ||]) ||]

-- A loop: a recursive low function, made with genRec
sumSq : Low Int -> Low Int
sumSq n = runGen $ do
  go <- genRecNamed "go" $ \go => [|| \i, acc => if i > ~n then acc else ~go (i + 1) (acc + i * i) ||]
  pure [|| ~go 1 0 ||]

sumSquares : Int -> Int
sumSquares n = ~(sumSq [|| n ||])

-- Local functions, lets and literals
fac : Int -> Int
fac n = ~([|| let go : Int -> Int -> Int
                  go i acc = if i == 0 then acc else go (i - 1) (acc * i)
              in go n 1 ||])

-- Data types: a user defined type, Maybe, lists, tuples, Bool, Double
data Shape = Circle Double | Rect Double Double

area : Low Shape -> Low Double
area s = [|| case ~s of
               Circle r => 3.0 * r * r
               Rect w h => w * h ||]

areaOf : Shape -> Double
areaOf s = ~(area [|| s ||])

lenL : Low (List Int) -> Low Int
lenL xs = runGen $ do
  go <- genRecNamed {a = List Int -> Int -> Int} "go" $ \go =>
          [|| \l, acc => case l of
                           [] => acc
                           _ :: r => ~go r (acc + 1) ||]
  pure [|| ~go ~xs 0 ||]

len : List Int -> Int
len xs = ~(lenL [|| xs ||])

swap : (Int, Int) -> (Int, Int)
swap p = ~([|| case ~([|| p ||]) of (a, b) => (b, a) ||])

safeDiv : Int -> Int -> Maybe Int
safeDiv x y = ~([|| if y == 0 then Nothing else Just (x `div` y) ||])

-- A polymorphic generator: the type variable needs LowRep
twice : LowRep a => Low (a -> a) -> Low a -> Low a
twice f x = genLetNamed "y" x $ \y => [|| ~f (~f ~y) ||]

incTwice : Int -> Int
incTwice n = ~(twice [|| \k => k + 1 ||] [|| n ||])

classify : Int -> Maybe (Int, Int) -> String
classify n mp = ~([|| case mp of
                        Just (a, b) => if a > n then "big"
                                       else if b > n then "medium"
                                       else "small"
                        Nothing => "none" ||])

-- Strictness: low code is call by value
strict : Int -> Int
strict n = ~([|| let x = n * 2 in let y = x + 1 in y * y ||])

-- Compile time values turned into low code
constants : (Int, Double, Char, String, Bool)
constants = ~([|| (~(lowInt (2 + 3)), ~(lowDouble 2.5), ~(lowChar 'x'), ~(lowString "hi"), True) ||])

-- A higher order function with a known function argument is specialised
incAll : List Int -> List Int
incAll xs = ~([|| map (\x => x + 1) xs ||])

main : IO ()
main = do printLn (cube 3)
          putStr ~(lowString (lowPretty (reflect cubeLow)))
          printLn (sumSquares 10)
          printLn (fac 10)
          printLn (areaOf (Circle 2), areaOf (Rect 2 3))
          printLn (len [1, 2, 3, 4])
          printLn (swap (1, 2))
          printLn (safeDiv 7 2, safeDiv 1 0)
          printLn (incTwice 5)
          printLn (classify 5 (Just (10, 1)), classify 5 (Just (1, 10)), classify 5 (Just (1, 1)), classify 5 Nothing)
          printLn (strict 10)
          printLn constants
          printLn (incAll [1, 2, 3])
