module Data.Graph

import Libraries.Data.SortedMap

%default total

public export
record Graph w a where
    constructor MkGraph
    {auto ord : Ord a}
    edges : SortedMap a (List (a, w))

%name Graph g

export
Show w => Show a => Show (Graph w a) where
    show g = "MkGraph (\{show g.edges})"

export
Foldable (Graph w) where
    foldr f x g = foldr f x $ keys g.edges
    foldl f x g = foldl f x $ keys g.edges
    null g = null $ keys g.edges
    foldlM f x g = foldlM f x $ keys g.edges
    toList g = keys g.edges
    foldMap f g = foldMap f $ keys g.edges

export
toEdges : Graph w a -> List (a, a, w)
toEdges g = do
    (node, dests) <- SortedMap.toList g.edges
    map (node,) dests

add : k -> v -> SortedMap k (List v) -> SortedMap k (List v)
add x y xs = insert x (y :: maybe [] id (lookup x xs)) xs

export
fromEdges : Ord a => List (a, a, w) -> Graph w a
fromEdges xs = MkGraph $ foldr (\(x, y) => add x y) empty xs

export
covering
||| Terminates when there are no cycles of negative length
minPath : Ord w =>
          Num w =>
          Graph w a ->
          (start : a) ->
          (end : a) ->
          Maybe w
minPath g start end = minPath' empty (singleton 0 [start])
  where
    %hint
    ordA : Ord a
    ordA = g.ord

    lookup' : k -> SortedMap k (List v) -> List v
    lookup' x xs = maybe [] id $ lookup x xs

    minPath' : SortedMap a w ->
               SortedMap w (List a) ->
               Maybe w
    minPath' closed open_ = do
        let Just ((d, boundary), open_) = pop open_
            | Nothing => lookup end closed
        let neighbours = filter (\(node, e) => maybe True (e <) (lookup node closed)) $
              SortedMap.toList $
              foldr (mergeWith min) empty $
              map (\node => SortedMap.fromList $ map (mapSnd (+ d)) $ lookup' node g.edges) boundary
        let closed = mergeWith min (SortedMap.fromList neighbours) closed
        let open_ = foldr (\(node, d) => add d node) SortedMap.empty neighbours
        minPath' closed open_
