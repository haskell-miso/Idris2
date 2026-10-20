module Unified

-- One evaluator, used both as an interpreter (at run time, on Int) and as a
-- compiler (at compile time, on Low Int). The choice is made by the Num
-- implementation, so each use is at a single stage.

import Language.Staged.Low

data Arg = Var String | Lit Int
data Exp = Val String Arg | Add String Arg Arg | Mul String Arg Arg

Env : Type -> Type
Env rep = List (String, rep)

-- Arithmetic on code (the interpreter uses Num Int)
Num (Low Int) where
  a + b = [|| ~a + ~b ||]
  a * b = [|| ~a * ~b ||]
  fromInteger n = lowInt (fromInteger n)

envLookup : Num rep => Env rep -> String -> rep
envLookup env n = fromMaybe 0 (lookup n env)

envInsert : Env rep -> String -> rep -> Env rep
envInsert env n v = (n, v) :: env

procArg : Num rep => Arg -> Env rep -> rep
procArg (Var name) env = envLookup env name
procArg (Lit n) env = fromInteger (cast n)

procExp : Num rep => Exp -> Env rep -> Env rep
procExp (Val name arg) env = envInsert env name (procArg arg env)
procExp (Add name arg1 arg2) env = envInsert env name (procArg arg1 env + procArg arg2 env)
procExp (Mul name arg1 arg2) env = envInsert env name (procArg arg1 env * procArg arg2 env)

procProg : Num rep => List Exp -> Env rep -> Env rep
procProg es env = foldl (flip procExp) env es

-- x * 3 + 1
prog : List Exp
prog = [Val "y" (Lit 3), Mul "z" (Var "x") (Var "y"), Add "r" (Var "z") (Lit 1)]

-- The interpreter: runs a program (which can come from anywhere) at run time
interp : List Exp -> Int -> Int
interp p x = envLookup (procProg p [("x", x)]) "r"

-- The compiler: the same code, run at compile time on code
compile : List Exp -> Low (Int -> Int)
compile p = [|| \x => ~(envLookup (procProg p [("x", [|| x ||])]) "r") ||]

compiled : Int -> Int
compiled = ~(compile prog)

main : IO ()
main = do printLn (interp prog 5)
          printLn (compiled 5)
          putStr ~(lowString (lowPretty (reflect (compile prog))))
