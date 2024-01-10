import Data.List
import Data.Maybe
import Data.SnocList
import Libraries.Data.SortedMap
import System.File

import Data.Graph
import Data.String.Parse2D

%default total

maximum : List Nat -> Nat
maximum ns = foldr max 0 ns

record Trail where
    constructor MkTrail
    pathDirs : SortedMap Coord (Maybe Direction)
    start : Coord
    end : Coord

dirs : List Direction
dirs = [N, E, S, W]

trim : Num w => Graph w Coord -> Graph w Coord
trim g = do
    let g = foldr (\c, g => do
        let Just [(a, wa)] = SortedMap.lookup c g.edges
            | _ => g
        {edges $= adjust a $ filter ((/= c) . fst)} g
          ) g g
    foldr (\c, g => do
        let Just [(a, wa), (b, wb)] = SortedMap.lookup c g.edges
            | _ => g
        {edges $=
            (adjust b $ map $ \(c', w) => if c' == c then (a, w + wa) else (c', w)) .
            (adjust a $ map $ \(c', w) => if c' == c then (b, w + wb) else (c', w))
        } g
      ) g g

namespace Part1
    export
    covering
    ||| We assume no cycles in the trail
    longestPath : Trail -> Maybe Nat
    longestPath t = map (\n => cast (-n)) $ minPath asGraph t.start t.end
      where
        asGraph : Graph Integer Coord
        asGraph = trim $ fromEdges $ do
            (c, md) <- SortedMap.toList t.pathDirs
            guard $ c /= t.end
            c' <- map (flip move c) $ maybe dirs pure md
            guard $ isJust $ lookup c' t.pathDirs
            pure (c, c', -1)

namespace Part2
    export
    covering
    ||| We can no longer assume no cycles
    ||| Full solution is NP hard
    ||| So trim the graph, and brute force it
    longestPath' : Trail -> Nat
    longestPath' t = followPaths asGraph [([<t.start], 0)] 0
      where
        asGraph : Graph Nat Coord
        asGraph = trim $ fromEdges $ do
            (c, md) <- SortedMap.toList t.pathDirs
            guard $ c /= t.end
            c' <- map (flip move c) dirs
            guard $ isJust $ lookup c' t.pathDirs
            pure (c, c', the Nat 1)

        followPaths : Graph Nat Coord ->
                      List (SnocList Coord, Nat) ->
                      Nat ->
                      Nat
        followPaths g [] n = n
        followPaths g open_ n = do
            let neighbours = do
                (path@(_ :< c), len) <- open_
                    | _ => []
                (c', w) <- maybe [] id $ lookup c g.edges
                guard $ not $ elem c' path
                pure (path :< c', w + len)
            let (done, open_) = partition ((\case
                      ([<], _) => False
                      ((_ :< c'), _) => c' == t.end
                  )) neighbours
            let n = maximum $ n :: map snd done
            followPaths g open_ n

covering
trail : Parse2D Trail
trail = do
    background '#'
    path <- many $ lexeme '#' [| (
        coord,
        (object '.' Nothing) <|>
        (object '^' $ Just N) <|>
        (object '>' $ Just E) <|>
        (object 'v' $ Just S) <|>
        (object '<' $ Just W)
      ) |]
    eos

    let [start] = filter (\(x, y) => y == 0) $ map fst path
        | [] => fail "No start path"
        | _ => fail "Multiple start paths"
    maxY <- map (\y => cast y - 1) height
    let [end] = filter (\(x, y) => y == maxY) $ map fst path
        | [] => fail "No end path"
        | _ => fail "Multiple end paths"

    pure $ MkTrail (SortedMap.fromList path) start end

covering
main : IO ()
main = do
    let eg = """
    #.#####################
    #.......#########...###
    #######.#########.#.###
    ###.....#.>.>.###.#.###
    ###v#####.#v#.###.#.###
    ###.>...#.#.#.....#...#
    ###v###.#.#.#########.#
    ###...#.#.#.......#...#
    #####.#.#.#######.#.###
    #.....#.#.#.......#...#
    #.#####.#.#.#########v#
    #.#...#...#...###...>.#
    #.#.#v#######v###.###v#
    #...#.>.#...>.>.#.###.#
    #####v#.#.###v#.#.###.#
    #.....#...#...#.#.#...#
    #.#########.###.#.#.###
    #...###...#...#...#.###
    ###.###.#.###v#####v###
    #...#...#.#.>.>.#.>.###
    #.###.###.#.###.#.#v###
    #.....###...###...#...#
    #####################.#
    """

    let Right (eg, _) = parse2d trail eg
        | Left err => putStrLn err

    Right input <- readFile "Day23/input"
            | Left err => printLn err

    let Right (input, _) = parse2d trail input
            | Left err => putStrLn err

    putStrLn "Part 1"
    printLn $ longestPath eg
    printLn $ longestPath input

    putStrLn "Part 2"
    printLn $ longestPath' eg
    printLn $ longestPath' input
