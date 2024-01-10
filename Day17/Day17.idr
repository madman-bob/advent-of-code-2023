import Control.Monad.State
import Data.Fin
import Data.SortedMap
import System.File

import Data.Graph
import Data.String.Parse2D

%default total

record City where
    constructor MkCity
    blocks : SortedMap Coord Nat
    width : Nat
    height : Nat

Show City where
    show cty = "MkCity (\{show cty.blocks}) \{show cty.width} \{show cty.height}"

covering
findPath : City ->
           {default 1 minSteps : Nat} ->
           {default 3 maxSteps : Nat} ->
           Nat
findPath cty = do
    let w = cast cty.width
    let h = cast cty.height

    let dummyStart = Left False
    let dummyEnd = Left True

    let g = Graph.fromEdges {a = Either Bool (Coord, Bool)} $ (do
                let start = (0, 0)
                let end = (w - 1, h - 1)
                b <- [False, True]
                [
                    (dummyStart, Right (start, b), 1),
                    (Right (end, b), dummyEnd, 1)
                ]
            ) ++ (do
                cFrom <- [| ([0..w - 1], [0..h - 1]) |]
                b <- [False, True]
                d <- dirs b
                fst $ foldl
                    (\(es, cPrev, totalW), n => do
                        let c = move d cPrev
                        case lookup c cty.blocks of
                            Nothing => (es, c, totalW)
                            Just w => do
                                let totalW = w + totalW
                                if n >= minSteps
                                    then do
                                        let e = (Right (cFrom, b), Right (c, not b), totalW)
                                        (e :: es, c, totalW)
                                    else (es, c, totalW))
                    ([], cFrom, the Nat 0)
                    [1..maxSteps])

    minus (maybe 0 id $ minPath g dummyStart dummyEnd) 2
  where
    dirs : Bool -> List Direction
    dirs False = [N, S]
    dirs True = [E, W]

covering
city : Parse2D City
city = [| MkCity
    (map (SortedMap.fromList . concat) $ some $ some [| (coord, d) |] <* optional newline)
    width
    height
  |] <* eos
  where
    d : Parse2D Nat
    d = map cast digit <* step

||| Warning, takes a while
covering
main : IO ()
main = do
    let eg = """
    2413432311323
    3215453535623
    3255245654254
    3446585845452
    4546657867536
    1438598798454
    4457876987766
    3637877979653
    4654967986887
    4564679986453
    1224686865563
    2546548887735
    4322674655533
    """

    let Right (eg, _) = parse2d city eg
        | Left err => putStrLn err

    Right input <- readFile "Day17/input"
        | Left err => printLn err

    let Right (input, _) = parse2d city input
        | Left err => putStrLn err

    putStrLn "Part 1"
    printLn $ findPath eg
    printLn $ findPath input

    let eg2 = """
    111111111111
    999999999991
    999999999991
    999999999991
    999999999991
    """

    let Right (eg2, _) = parse2d city eg2
        | Left err => putStrLn err

    putStrLn "Part 2"
    printLn $ findPath {minSteps = 4} {maxSteps = 10} eg2
    printLn $ findPath {minSteps = 4} {maxSteps = 10} input
