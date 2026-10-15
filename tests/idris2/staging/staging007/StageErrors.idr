module StageErrors

import Language.Staged

-- A meta level value which isn't a primitive can't be used in object code
-- directly (there's no cross stage persistence, except for literals)
bad1 : Nat -> Code Nat
bad1 n = [|| n ||]

-- Object level variables can't be used by meta level code
bad2 : Int -> Int
bad2 x = ~(if x == 0 then [|| 1 ||] else [|| 2 ||])

-- A splice is object level code
bad3 : Code Int
bad3 = [|| 1 ||] + ~[|| 2 ||]
