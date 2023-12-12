module Day8.Part1

import Data.Fuel

import public Day8.Common

%default total

export
followDoc : Doc -> Maybe Nat
followDoc doc = followDoc'
    (limit $ length doc.instructions * (length $ keys doc.network))
    (cycle doc.instructions)
    "AAA"
    0
  where
    followDoc' : Fuel -> Stream Direction -> String -> Nat -> Maybe Nat
    followDoc' Dry (d :: ds) node n = Nothing
    followDoc' (More f) (d :: ds) node n = if node == "ZZZ"
       then pure n
       else followDoc' f ds !(follow doc d node) (S n)
