module Mixed

import Language.Staged

-- a case inside a quotation, capturing meta level variables
safeDiv : Code Int -> Code Int -> Code Int
safeDiv x y = [|| case ~y of { 0 => 0; d => div ~x d } ||]

useDiv : Int -> Int -> Int
useDiv n m = ~(safeDiv [|| n + 1 ||] [|| m ||])

-- a recursive local function in a quotation, with the meta level function
-- inlined in its body (ICFP 2024, map)
mapC : (Code a -> Code b) -> Code (List a) -> Code (List b)
mapC f xs = [|| let go : List a -> List b
                    go [] = []
                    go (y :: ys) = ~(f [|| y ||]) :: go ys
                 in go ~xs ||]

incAll : List Int -> List Int
incAll xs = ~(mapC (\v => [|| ~v + 1 ||]) [|| xs ||])

-- the inlined function mentions an object variable from outside
addAll : Int -> List Int -> List Int
addAll n xs = ~(mapC (\v => [|| ~v + n ||]) [|| xs ||])

main : IO ()
main = do printLn (useDiv 9 2)
          printLn (useDiv 9 0)
          printLn (incAll [1, 2, 3])
          printLn (addAll 10 [1, 2, 3])
