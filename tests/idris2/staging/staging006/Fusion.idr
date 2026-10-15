||| foldr/build fusion by staging (Kovács, demo/examples/FoldrFusion.2ltt):
||| a fusible list is a meta level Church encoding of an object level list,
||| so pipelines of list functions compute to a single foldr.
module Fusion

import Language.Staged

FList : Type -> Type
FList a = (l : Type) -> (Code a -> Code l -> Code l) -> Code l -> Code l

fnil : FList a
fnil l c n = n

fcons : Code a -> FList a -> FList a
fcons x xs l c n = c x (xs l c n)

fmap : (Code a -> Code b) -> FList a -> FList b
fmap f xs l c n = xs l (\y, ys => c (f y) ys) n

ffilter : (Code a -> Code Bool) -> FList a -> FList a
ffilter p xs l c n = xs l (\y, ys => if p y then c y ys else ys) n

fappend : FList a -> FList a -> FList a
fappend xs ys l c n = xs l c (ys l c n)

fbind : FList a -> (Code a -> FList b) -> FList b
fbind xs f l c n = xs l (\y, ys => f y l c ys) n

up : Code (List a) -> FList a
up xs l c n = foldr c n xs

down : {a : Type} -> FList a -> Code (List a)
down xs = xs (List a) (\y, ys => y :: ys) []

f1 : List Int -> List Int
f1 xs = down (fmap (+ 1) (fmap (* 2) (up xs)))

f2 : List Int -> List Int
f2 xs = down (fappend (fmap (+ 1) (up xs)) (fmap (* 10) (up xs)))

f3 : List Int -> List Int
f3 xs = down (fbind (up xs) (\x => fbind (up xs) (\y => fcons (x + y) fnil)))

f4 : List Int -> List Int
f4 xs = down (ffilter (\x => x > 2) (up xs))

main : IO ()
main = do printLn (f1 [1, 2, 3])
          printLn (f2 [1, 2, 3])
          printLn (f3 [1, 2])
          printLn (f4 [1, 2, 3, 4])
