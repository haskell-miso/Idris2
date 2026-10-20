import Language.Staged.Low
import Language.Staged.Low.C

-- Not 'main', so its stage is inferred: meta level
gen : IO ()
gen = putStr (toC "unit" (reflect [|| () ||]))

main : IO ()
main = pure ()
