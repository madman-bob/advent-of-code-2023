import Data.Vect
import System.File

import Data.String.Parser

implementation {n : Nat} -> Num a => Num (Vect n a) where
    (+) = zipWith (+)
    (*) = zipWith (*)
    fromInteger x = replicate n (fromInteger x)

implementation {n : Nat} -> Neg a => Neg (Vect n a) where
    negate = map negate
    (-) = zipWith (-)

combinations : (n : Nat) -> List a -> List (Vect n a)
combinations 0 xs = [[]]
combinations (S n) [] = []
combinations (S n) (x :: xs) = map (x ::) (combinations n xs) ++ combinations (S n) xs

record Rat where
    constructor MkRat
    num : Integer
    denom : Integer

Show Rat where
    show (MkRat n d) = if d == 1
        then show n
        else "\{show n}/\{show d}"

Num Rat where
    (MkRat an ad) + (MkRat bn bd) = MkRat (an * bd + bn * ad) (ad * bd)
    (MkRat an ad) * (MkRat bn bd) = MkRat (an * bn) (ad * bd)
    fromInteger n = MkRat n 1

Neg Rat where
    negate (MkRat n d) = (MkRat (-n) d)
    x - y = x + (negate y)

Fractional Rat where
    recip (MkRat n d) = MkRat d n
    x / y = x * (recip y)

Eq Rat where
    (MkRat an ad) == (MkRat bn bd) = an * bd == bn * ad

Ord Rat where
    compare (MkRat an ad) (MkRat bn bd) = do
        let (an, ad) = if ad >= 0 then (an, ad) else (-an, -ad)
        let (bn, bd) = if bd >= 0 then (bn, bd) else (-bn, -bd)
        compare (an * bd) (bn * ad)

record Range where
    constructor MkRange
    start : Rat
    end : Rat

rangeFromTo : Rat -> Rat -> Range
rangeFromTo = MkRange

in_ : Range -> Rat -> Bool
in_ r i = r.start <= i && i <= r.end

Coord2D : Type
Coord2D = Vect 2 Rat

Coord3D : Type
Coord3D = Vect 3 Rat

record Hailstone where
    constructor MkHailstone
    initPos : Coord3D
    velocity : Coord3D

record Line2D where
    constructor MkLine2D
    start : Coord2D
    dir : Coord2D

scale : Rat -> Coord2D -> Coord2D
scale s = map (s *)

Mat2D : Type
Mat2D = Vect 2 Coord2D

inv : Mat2D -> Mat2D
inv [[a, b], [c, d]] = do
    let det = a * d - b * c
    [[d / det, -c / det], [-b / det, a / det]]

mul : Mat2D -> Coord2D -> Coord2D
mul [[a, b], [c, d]] [x, y] = [a * x + b * y, c * x + d * y]

onLine : Coord2D -> Line2D -> Bool
onLine [x, y] (MkLine2D [sx, sy] [dx, dy]) = (x - sx) * dy == (y - sy) * dx

isParallel : Line2D -> Line2D -> Bool
isParallel (MkLine2D _ [adx, ady]) (MkLine2D _ [bdx, bdy]) = adx * bdy == bdx * ady

intersectBetween : Range -> Line2D -> Line2D -> Bool
intersectBetween r a b = do
    let False = isParallel a b
        | True => onLine b.start a
    let [s, t] = mul (inv [b.dir, -a.dir]) (a.start - b.start)
    let [x, y] = a.start + scale t a.dir
    t >= 0 && s >= 0 && in_ r x && in_ r y

part1 : Range -> List Hailstone -> Nat
part1 r hs = length $ filter (\[a, b] => intersectBetween r a b) $ combinations 2 $ map proj hs
  where
    proj' : Coord3D -> Coord2D
    proj' [x, y, z] = [x, y]

    proj : Hailstone -> Line2D
    proj h = MkLine2D (proj' h.initPos) (proj' h.velocity)

hailstone : Parser Hailstone
hailstone = [| MkHailstone (coord <* token "@") coord |]
  where
    rat : Parser Rat
    rat = map fromInteger integer

    coord : Parser Coord3D
    coord = do
        x <- rat
        token ","
        y <- rat
        token ","
        z <- lexeme rat
        pure [x, y, z]

hailstones : Parser (List Hailstone)
hailstones = many hailstone <* eos

main : IO ()
main = do
    let eg = """
    19, 13, 30 @ -2,  1, -2
    18, 19, 22 @ -1, -1, -2
    20, 25, 34 @ -2, -2, -4
    12, 31, 28 @ -1, -2, -1
    20, 19, 15 @  1, -5, -3
    """

    let Right (eg, _) = parse hailstones eg
        | Left err => putStrLn err

    Right input <- readFile "Day24/input"
            | Left err => printLn err

    let Right (input, _) = parse hailstones input
            | Left err => putStrLn err

    putStrLn "Part 1"
    printLn $ part1 [7..27] eg
    printLn $ part1 [200000000000000..400000000000000] input

    -- For part 2, see Day24.py
