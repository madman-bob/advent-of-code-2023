module Day7.Common

import Deriving.Show

%default total
%language ElabReflection

public export
data Card = Ace | King | Queen | Jack | Ten | Nine | Eight | Seven | Six | Five | Four | Three | Two

%hint
export
showCard : Show Card
showCard = %runElab derive

public export
data HandType = FiveKind | FourKind | FullHouse | ThreeKind | TwoPair | OnePair | HighCard

%hint
export
showHandType : Show HandType
showHandType = %runElab derive

export
typeValue : HandType -> Nat
typeValue FiveKind = 6
typeValue FourKind = 5
typeValue FullHouse = 4
typeValue ThreeKind = 3
typeValue TwoPair = 2
typeValue OnePair = 1
typeValue HighCard = 0

export
Eq HandType where
    (==) = (==) `on` typeValue

export
Ord HandType where
    compare = compare `on` typeValue

public export
record Play where
    constructor MkPlay
    hand : List Card
    bid : Nat

%hint
export
showPlay : Show Play
showPlay = %runElab derive

export
rank : Ord Play => List Play -> List (Nat, Play)
rank ps = enum $ sort ps
  where
    enum : {default 1 n : Nat} -> List a -> List (Nat, a)
    enum [] = []
    enum (x :: xs) = (n, x) :: enum {n = S n} xs

export
totalWinnings : Ord Play => List Play -> Nat
totalWinnings ps = sum $ map (\(r, c) => r * c.bid) $ rank ps
