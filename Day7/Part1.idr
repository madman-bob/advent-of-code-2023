module Day7.Part1

import Data.List
import Data.SortedMap

import public Day7.Common

%default total

export
value : Card -> Nat
value Ace = 14
value King = 13
value Queen = 12
value Jack = 11
value Ten = 10
value Nine = 9
value Eight = 8
value Seven = 7
value Six = 6
value Five = 5
value Four = 4
value Three = 3
value Two = 2

export
Eq Card where
    (==) = (==) `on` value

export
Ord Card where
    compare = compare `on` value

export
handType : List Card -> HandType
handType cs = do
    let count : SortedMap Card Nat = foldr (\c => mergeWith (+) (singleton c 1)) empty cs
    case sort $ Prelude.toList count of
        [5] => FiveKind
        [1, 4] => FourKind
        [2, 3] => FullHouse
        [1, 1, 3] => ThreeKind
        [1, 2, 2] => TwoPair
        [1, 1, 1, 2] => OnePair
        _ => HighCard

export
Eq Play where
    p1 == p2 = p1.hand == p2.hand && p1.bid == p2.bid

export
[P1] Ord Play where
    compare = on compare $ \p => (handType p.hand, p.hand, p.bid)
