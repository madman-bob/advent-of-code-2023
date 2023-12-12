module Day8.Common

import public Data.Vect
import public Data.SortedMap
import Deriving.Show

%default total
%language ElabReflection

public export
cycle : Vect (S n) a -> Stream a
cycle (x :: xs) = x :: cycle' xs
  where
    cycle' : Vect m a -> Stream a
    cycle' [] = x :: cycle' xs
    cycle' (y :: ys) = y :: cycle' ys

public export
data Direction = L | R

public export
Eq Direction where
    (==) = (==) `on` (\case L => 0; R => 1)

%hint
export
showDirection : Show Direction
showDirection = %runElab derive

public export
record Doc where
    constructor MkDoc
    {n : Nat}
    instructions : Vect (S n) Direction
    network : SortedMap String (String, String)

export
Show Doc where
    show doc = "MkDoc \{show doc.instructions} (\{show doc.network})"

export
followDir : Direction -> (a, a) -> a
followDir L (x, _) = x
followDir R (_, y) = y

export
follow : Doc -> Direction -> String -> Maybe String
follow doc d source = map (followDir d) $ lookup source doc.network
