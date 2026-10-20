import Data.List
import Language.Staged

OInt : Type
OInt = Code Int

data Arg = Var String | Num Int

Env : Type -> Type
Env a = List (String, a)

envLookup : Env OInt -> String -> OInt
envLookup env x = fromMaybe [|| 0 ||] (lookup x env)

-- A meta level Int where code is expected is quoted (cross-stage
-- persistence): 'n' is '[|| n ||]'
compArg : Arg -> Env OInt -> OInt
compArg (Var name) env = envLookup env name
compArg (Num n) env = n

-- Other data isn't primitive, so it still needs 'lift'
compFlag : Bool -> Code Bool
compFlag b = lift b

addArgs : Int -> Int
addArgs x = ~(compArg (Var "x") [("x", [|| x ||])]) + ~(compArg (Num 41) [])

main : IO ()
main = printLn (addArgs 1, ~(compFlag True))
