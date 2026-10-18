module LowInfer

import Language.Staged.Low
import Language.Staged.Low.C

-- The examples of staging009 without quotations and splices: the type checker
-- inserts them

sumSq : Low (Int -> Int)
sumSq = \n => runGen $ do
          go <- genRecNamed "go" $ \go => \i, acc => if i > n then acc else go (i + 1) (acc + i * i)
          pure (go 1 0)

data Shape = Circle Double | Rect Double Double

scaledArea : Low (Double -> Shape -> Double)
scaledArea = \k, s => let scale : Double -> Double
                          scale x = x * k in
                      case s of
                        Circle r => scale (3.0 * r * r)
                        Rect w h => scale (w * h)

firstBig : Low (Int -> List Int -> Maybe Int)
firstBig = \n, xs =>
             let big : Int -> Bool
                 big = (<) n
                 go : List Int -> Maybe Int
                 go l = case l of
                          [] => Nothing
                          x :: r => if big x then Just x else go r
             in go xs

sumSquares : Int -> Int
sumSquares = sumSq

main : IO ()
main = do
  putStrLn "---- sumSq, reflected"
  putStr (lowString (lowPretty (reflect sumSq)))
  putStrLn "---- scaledArea, C"
  putStr (lowString (toC "scaled_area" (reflect scaledArea)))
  putStrLn "---- firstBig, reflected"
  putStr (lowString (lowPretty (reflect firstBig)))
  putStrLn "---- run"
  printLn (sumSquares 10, scaledArea 2 (Rect 3 4), firstBig 5 [1, 7, 3, 9])
