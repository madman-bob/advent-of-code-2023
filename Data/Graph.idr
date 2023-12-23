module Data.Graph

import Data.SortedMap
import Data.SortedSet

%default total

export
record Graph a where
    constructor MkGraph
    {auto ord : Ord a}
    edges : SortedMap a (List (a, Nat))

%name Graph g

export
Show a => Show (Graph a) where
    show g = "MkGraph (\{show g.edges})"

%hint
export
graphOrd : Graph a => Ord a
graphOrd @{g} = g.ord

export
toEdges : Graph a -> List (a, a, Nat)
toEdges g = do
    (node, dests) <- SortedMap.toList g.edges
    map (node,) dests

add : k -> v -> SortedMap k (List v) -> SortedMap k (List v)
add x y xs = update (\ys => Just $ y :: maybe [] id ys) x xs

export
fromEdges : Ord a => List (a, a, Nat) -> Graph a
fromEdges xs = MkGraph $ foldr (\(x, y) => add x y) empty xs

export
minPath : Graph a ->
          (start : a) ->
          (end : a) ->
          Maybe Nat
minPath g start end = minPath' empty (singleton 0 [start]) 0
  where
    lookup : k -> SortedMap k (List v) -> List v
    lookup x xs = maybe [] id $ SortedMap.lookup x xs

    minPath' : SortedSet a ->
             SortedMap Nat (List a) ->
             Nat ->
             Maybe Nat
    minPath' closed open_ d = if null open_
        then Nothing
        else do
            let boundary = lookup d open_
            let False = elem end boundary
                | True => Just d
            let closed = union (SortedSet.fromList boundary) closed
            let neighbours = filter (\(node, _) => not $ contains node closed) $
                  SortedMap.toList $
                  foldr (mergeWith min) empty $
                  map (\node => SortedMap.fromList $ map (mapSnd (+ d)) $ lookup node g.edges) boundary
            let open_ = foldr (\(node, d) => add d node) open_ neighbours
            assert_total $ minPath' closed (delete d open_) (S d)
