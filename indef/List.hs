module List (T,module List) where
import GHC.Magic (oneShot)
import Elt

data List = Nil | Cons {-# unpack #-} !T List

pure :: T -> List
{-# INLINE pure #-}
pure = (`Cons` Nil)

apWith :: (T -> T -> T) -> List -> List -> List
{-# INLINE apWith #-}
apWith f = go where
  Cons x xs `go` Cons y ys = Cons (f x y) (go xs ys)
  _ `go` _ = Nil

--ap_ :: List -> [b] -> [b]
--[># INLINE ap_ #<]
--ap_ xs ys  = [y | _ <- xs, y <- ys]

--bind :: (T -> [b]) -> List -> [b]
--{-# INLINE bind #-}
--bind f = go where go = \case {Nil -> []; Cons a as -> f a ++ go as}

foldr :: (T -> r -> r) -> r -> List -> r
{-# INLINE [0] foldr #-}
foldr k z = go where go = \case {Nil -> z; Cons y ys -> y `k` go ys}

build   :: (forall r. (T -> r -> r) -> r -> r) -> List
{-# inline [1] build #-}
build g = g Cons Nil

augment :: (forall r. (T -> r -> r) -> r -> r) -> List -> List
{-# inline [1] augment #-}
augment g xs = g Cons xs

{-# RULES
"fold/build" forall k z (g::forall r. (T -> r -> r) -> r -> r).
             foldr k z (build g) = g k z
"foldr/augment" forall k z xs (g :: forall r. (T -> r -> r) -> r -> r).
                foldr k z (augment g xs) = g k (foldr k z xs)
"foldr/id" foldr Cons Nil = \x -> x
"foldr/app" [1] forall ys. foldr Cons ys = \xs -> xs `append` ys
"foldr/single" forall k z x. foldr k z (Cons x Nil) = k x z
"foldr/nil" forall k z. foldr k z Nil = z
"foldr/cons/build" forall k z x (g :: forall r. (T -> r -> r) -> r -> r).
                   foldr k z (Cons x (build g)) = k x (g k z)
"augment/build" forall (g :: forall r. (T -> r -> r) -> r -> r)
                       (h :: forall r. (T -> r -> r) -> r -> r).
                       augment g (build h) = build (\c n -> g c (h c n))
"augment/nil" forall (g :: forall r. (T -> r -> r) -> r -> r).
                     augment g Nil = build g
"foldr/cons" forall k z x xs. foldr k z (Cons x xs) = k x (foldr k z xs)
#-}

mapEndo :: (T -> T) -> List -> List
{-# noinline [0] mapEndo #-}
mapEndo f = go where go = \case {Nil -> Nil; Cons x xs -> Cons (f x) (go xs)}

mapEndoFB :: (T -> r -> r) -> (T -> T) -> T -> r -> r
{-# inline [0] mapEndoFB #-}
mapEndoFB c f = \x ys -> c (f x) ys

{-# RULES
"map" [~1] forall f xs. mapEndo (f :: T->T) xs = build (\c n -> foldr (mapEndoFB c f) n xs)
"mapList" [1] forall f. foldr (mapEndoFB Cons f) Nil = mapEndo f
"mapFB" forall c f g. mapEndoFB (mapEndoFB c f) g = mapEndoFB c (\x -> f (g x))
"mapFB/id" forall c. mapEndoFB c (\x -> x) = c
  #-}

append :: List -> List -> List
append Nil     ys = ys
append (Cons x xs) ys = Cons x xs `append` ys

foldl' :: (r -> T -> r) -> r -> List -> r
{-# inline foldl' #-}
foldl' rtr r0 xs = foldr (\x rr -> oneShot (\r -> rr (rtr r x))) (\x->x) xs r0


foldl :: (r -> T -> r) -> r -> List -> r
{-# inline foldl #-}
foldl rtr r0 xs = foldr (\x rr -> oneShot (\(!r) -> rr (rtr r x))) (\x->x) xs r0
