import Language.Staged.Low
import Language.Staged.Low.C

-- main runs at run time, so it is object level code: the quotation (and the
-- meta program using it) needs a splice
main : IO ()
main = putStr (toC "unit" (reflect [|| () ||]))
