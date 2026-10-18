module LowReflect

import Language.Staged.Low
import Language.Staged.Low.C
import Language.Staged.Low.JS

-- The sum of the squares of 1 .. n, as a loop
sumSq : Low (Int -> Int)
sumSq = [|| \n => ~(runGen $ do
              go <- genRecNamed "go" $ \go => [|| \i, acc => if i > n then acc else ~go (i + 1) (acc + i * i) ||]
              pure [|| ~go 1 0 ||]) ||]

-- A function on a user defined data type, with a local helper function that
-- captures a variable of the enclosing scope (lambda lifting in C)
data Shape = Circle Double | Rect Double Double

scaledArea : Low (Double -> Shape -> Double)
scaledArea = [|| \k, s => let scale : Double -> Double
                              scale x = x * k in
                          case s of
                            Circle r => scale (3.0 * r * r)
                            Rect w h => scale (w * h) ||]

-- Lists, Maybe, and a partial application (eta expanded by call saturation)
firstBig : Low (Int -> List Int -> Maybe Int)
firstBig = [|| \n, xs =>
                 let big : Int -> Bool
                     big = (<) n
                     go : List Int -> Maybe Int
                     go l = case l of
                              [] => Nothing
                              x :: r => if big x then Just x else go r
                 in go xs ||]

-- The reflected programs are also still runnable code
sumSquares : Int -> Int
sumSquares = ~sumSq

main : IO ()
main = do
  putStrLn "---- sumSq, reflected"
  putStr ~(lowString (lowPretty (reflect sumSq)))
  putStrLn "---- sumSq, C"
  putStr ~(lowString (toC "sumsq" (reflect sumSq)))
  putStrLn "---- sumSq, JavaScript"
  putStr ~(lowString (toJS "sumsq" (reflect sumSq)))
  putStrLn "---- scaledArea, reflected"
  putStr ~(lowString (lowPretty (reflect scaledArea)))
  putStrLn "---- scaledArea, C"
  putStr ~(lowString (toC "scaled_area" (reflect scaledArea)))
  putStrLn "---- firstBig, reflected"
  putStr ~(lowString (lowPretty (reflect firstBig)))
  putStrLn "---- firstBig, JavaScript"
  putStr ~(lowString (toJS "firstBig" (reflect firstBig)))
  putStrLn "---- firstBig, C"
  putStr ~(lowString (toC "first_big" (reflect firstBig)))
  putStrLn "---- run"
  printLn (sumSquares 10, (~scaledArea) 2 (Rect 3 4), (~firstBig) 5 [1, 7, 3, 9])
