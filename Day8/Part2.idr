module Day8.Part2

import public Data.Fin
import Data.Fuel
import Data.Stream
import Deriving.Show

import public Day8.Common

%default total
%language ElabReflection

public export
record State doc where
    constructor MkState
    name : String
    offset : Fin (S doc.n)

%hint
export
showState : Show (State doc)
showState = %runElab derive

public export
Eq (State doc) where
    (==) = (==) `on` (\s => (s.name, s.offset))

export
nextZ : (doc : Doc) ->
        State doc ->
        Maybe (State doc, Nat)
nextZ doc start = do
    (zName, steps) <- nextZ'
        (limit $ length doc.instructions * length (keys doc.network))
        (drop (cast start.offset) $ cycle doc.instructions)
        start.name
        0
    pure (MkState zName $ restrict _ $ cast start.offset + cast steps, steps)
  where
    nextZ' : Fuel -> Stream Direction -> String -> Nat -> Maybe (String, Nat)
    nextZ' Dry (d :: ds) node n = Nothing
    nextZ' (More f) (d :: ds) node n = if isSuffixOf "Z" node && n /= 0
        then pure (node, n)
        else nextZ' f ds !(follow doc d node) (S n)

export
nextZs : (doc : Doc) -> String -> List (State doc, Nat)
nextZs doc name = do
    let s = MkState name 0
    cast $ nextZs' (limit 100) s [<(s, 0)]
  where
    nextZs' : Fuel -> State doc -> SnocList (State doc, Nat) -> SnocList (State doc, Nat)
    nextZs' Dry current past = past
    nextZs' (More f) current past = case nextZ doc current of
        Nothing => past
        Just (next, step) => if elem (next, step) past
            then past :< (next, step)
            else nextZs' f next $ past :< (next, step)
