import Language.Staged.Low
import Language.Staged.Low.C

main : IO ()
main = putStr ~(lowString (toC "unit" (reflect [|| () ||])))
