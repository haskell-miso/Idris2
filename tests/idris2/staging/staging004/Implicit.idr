module Implicit

import Language.Staged

-- no quotations or splices anywhere: the elaborator infers them

power : Nat -> Code Int -> Code Int
power Z x = 1
power (S k) x = x * power k x

cube : Int -> Int
cube x = power 3 x

mapC : (Code a -> Code b) -> Code (List a) -> Code (List b)
mapC f xs = foldr (\y, ys => f y :: ys) [] xs

incAll : List Int -> List Int
incAll xs = mapC (\v => v + 1) xs

-- compile time types, used in an object level type
Vec : Nat -> Code Type -> Code Type
Vec Z a = ()
Vec (S k) a = (a, Vec k a)

total3 : Vec 3 Int -> Int
total3 (x, y, z, ()) = x + y + z

main : IO ()
main = do printLn (cube 5)
          printLn (incAll [1, 2, 3])
          printLn (total3 (1, 2, 3, ()))
