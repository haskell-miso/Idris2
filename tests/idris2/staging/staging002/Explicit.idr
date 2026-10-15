module Explicit

import Language.Staged

-- types computed at compile time
Vec : Nat -> Code Type -> Code Type
Vec Z a = [|| () ||]
Vec (S k) a = [|| (~a, ~(Vec k a)) ||]

-- inlined map over a static length vector
mapVec : (n : Nat) -> (Code a -> Code b) -> Code (~(Vec n [|| a ||])) -> Code (~(Vec n [|| b ||]))
mapVec Z f v = [|| () ||]
mapVec (S k) f v = [|| (~(f [|| fst ~v ||]), ~(mapVec k f [|| snd ~v ||])) ||]

incAll : ~(Vec 3 [|| Int ||]) -> ~(Vec 3 [|| Int ||])
incAll v = ~(mapVec 3 (\x => [|| ~x + 1 ||]) [|| v ||])

-- inlined map over lists, via foldr
mapList : (Code a -> Code b) -> Code (List a) -> Code (List b)
mapList f xs = [|| foldr (\y, ys => ~(f [|| y ||]) :: ys) [] ~xs ||]

doubleAll : List Int -> List Int
doubleAll xs = ~(mapList (\x => [|| ~x * 2 ||]) [|| xs ||])

-- let insertion
square : Code Int -> Gen (Code Int)
square x = do v <- gen x
              pure [|| ~v * ~v ||]

sq : Int -> Int
sq n = ~(runGen (square [|| n + 1 ||]))

-- lifting compile time values
table : List Int
table = ~(lift (map (\x => x * x) (the (List Int) [1, 2, 3, 4])))

main : IO ()
main = do printLn (incAll (1, 2, 3, ()))
          printLn (doubleAll [1, 2, 3])
          printLn (sq 4)
          printLn table
