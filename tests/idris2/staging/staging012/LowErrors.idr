module LowErrors

import Language.Staged.Low

-- Low code is first order: a function is not a value
higher : Low ((Int -> Int) -> Int)
higher = [|| \g => g 1 ||]

-- Data can't contain functions
funList : Low Int -> Low (List (Int -> Int))
funList x = [|| [\y => y + ~x] ||]

-- Low code is monomorphic: which implementation is used must be known
poly : Num a => Low a -> Low a
poly x = [|| ~x + ~x ||]
