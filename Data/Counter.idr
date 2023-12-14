module Data.Counter

import Data.SortedMap

%default total

export
data Counter a = MkCounter (SortedMap a Nat)

%name Counter c, d

export
lookup : a -> Counter a -> Nat
lookup x (MkCounter cs) = maybe 0 id $ lookup x cs

export
fromList : Ord a => List (a, Nat) -> Counter a
fromList cs = MkCounter $ fromList cs

export
toList : Counter a -> List (a, Nat)
toList (MkCounter cs) = toList cs

export
Show a => Show (Counter a) where
    show (MkCounter cs) = show cs

export
empty : Ord a => Counter a
empty = MkCounter empty

export
(<|>) : Counter a -> Counter a -> Counter a
(MkCounter cs) <|> (MkCounter ds) = MkCounter $ mergeWith (+) cs ds

export
scale : Nat -> Counter a -> Counter a
scale n (MkCounter cs) = MkCounter $ map (n *) cs

export
pure : Ord a => a -> Counter a
pure x = MkCounter $ singleton x 1

export
(>>=) : Ord b => Counter a -> (a -> Counter b) -> Counter b
(MkCounter cs) >>= f = foldr (\(x, n) => (<|>) $ scale n $ f x) empty $ SortedMap.toList cs
