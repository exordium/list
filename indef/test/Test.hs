module Test where
import List.Int as Int
import Prelude

foob = apWith (+)
--barb = zipWith ((+) @Int)
a = (Cons 1 (Cons 2 (Cons 3 Nil)))
b = Int.foldl (+) 0 a
--deriving instance Show (List T)
