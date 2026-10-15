module Power

import Language.Staged

power : Nat -> Code Int -> Code Int
power Z x = [|| 1 ||]
power (S k) x = [|| ~x * ~(power k x) ||]

cube : Int -> Int
cube x = ~(power 3 [|| x ||])

main : IO ()
main = printLn (cube 5)
