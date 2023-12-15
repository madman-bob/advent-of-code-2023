import Data.List
import Data.String.Parser
import System.File

%default total

Image : Type
Image = List (List Bool)

namespace Part1
    export
    checkReflection : List Bool -> Nat -> Bool
    checkReflection xs n = all id $ zipWith (==) (reverse $ take n xs) (drop n xs)

    export
    hReflections : Image -> List Nat
    hReflections [] = []
    hReflections rs@(r :: _) = foldr (\r => filter (checkReflection r)) [1..minus (length r) 1] rs

    export
    vReflections : Image -> List Nat
    vReflections i = hReflections $ transpose i

    export
    summary : List Image -> Nat
    summary is = sum $ map (\i => sum (hReflections i) + 100 * sum (vReflections i)) is

namespace Part2
    export
    refDiffs : List Bool -> Nat -> Nat
    refDiffs xs n = sum $ zipWith (\x, y => if x /= y then 1 else 0) (reverse $ take n xs) (drop n xs)

    export
    hReflections' : Image -> List Nat
    hReflections' [] = []
    hReflections' rs@(r :: _) = map fst $ filter (\(n, e) => e == 1) $ foldr
        (\xs => flip (>>=) $ \(n, e) => do
            let e = e + refDiffs xs n
            if e <= 1 then pure (n, e) else [])
        (map (, 0) [1..minus (length r) 1])
        rs

    export
    vReflections' : Image -> List Nat
    vReflections' i = hReflections' $ transpose i

    export
    summary' : List Image -> Nat
    summary' is = sum $ map (\i => sum (hReflections' i) + 100 * sum (vReflections' i)) is

covering
image : Parser Image
image = some (some (
    (char '.' *> pure False) <|>
    (char '#' *> pure True)
  ) <* char '\n')

covering
images : Parser (List Image)
images = many (image <* optional (char '\n')) <* eos

covering
main : IO ()
main = do
    let eg = """
    #.##..##.
    ..#.##.#.
    ##......#
    ##......#
    ..#.##.#.
    ..##..##.
    #.#.##.#.

    #...##..#
    #....#..#
    ..##..###
    #####.##.
    #####.##.
    ..##..###
    #....#..#

    """

    let Right (eg, _) = parse images eg
        | Left err => putStrLn err

    Right input <- readFile "Day13/input"
        | Left err => printLn err

    let Right (input, _) = parse images input
        | Left err => putStrLn err

    putStrLn "Part 1"
    printLn $ map hReflections eg
    printLn $ map vReflections eg
    printLn $ summary eg
    printLn $ summary input

    putStrLn "Part 2"
    printLn $ map hReflections' eg
    printLn $ map vReflections' eg
    printLn $ summary' eg
    printLn $ summary' input
