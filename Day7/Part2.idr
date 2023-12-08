module Day7.Part2

import Data.List
import Data.SortedMap

import public Day7.Common

%default total

export
value : Card -> Nat
value Ace = 13
value King = 12
value Queen = 11
value Jack = 1 -- <- Note change
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
    let jokers = maybe 0 id $ lookup Jack count
    let count = delete Jack count
    case addLast jokers $ sort $ Prelude.toList count of
        [5] => FiveKind
        [1, 4] => FourKind
        [2, 3] => FullHouse
        [1, 1, 3] => ThreeKind
        [1, 2, 2] => TwoPair
        [1, 1, 1, 2] => OnePair
        _ => HighCard
  where
    addLast : Nat -> List Nat -> List Nat
    addLast n [] = [n]
    addLast n [m] = [n + m]
    addLast n (m :: ms) = m :: addLast n ms

export
Eq Play where
    p1 == p2 = p1.hand == p2.hand && p1.bid == p2.bid

export
[P2] Ord Play where
    compare = on compare $ \p => (handType p.hand, p.hand, p.bid)
