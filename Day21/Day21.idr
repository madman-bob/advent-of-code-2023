import Control.Monad.State
import Data.Nat
import Data.SortedMap
import Data.SortedSet
import Deriving.Show
import System.File

import Data.String.Parse2D

%default total
%language ElabReflection

Cast Bool Nat where
    cast False = 0
    cast True = 1

minBy : (a -> a -> Ordering) -> a -> a -> a
minBy f x y = case f x y of
    LT => x
    EQ => x
    GT => y

maximum : List Nat -> Nat
maximum ns = foldr max 0 ns

minimumBy : (a -> Nat) -> List a -> Maybe a
minimumBy f ns = map Builtin.fst $ foldr
    (\x => \case
        Nothing => Just (x, f x)
        Just (y, fy) => do
            let fx = f x
            if fx < fy
                then Just (x, fx)
                else Just (y, fy))
    Nothing
    ns

0
Mem : (a -> b) -> Type -> Type
Mem f = State (SortedMap a b)

call : {f : a -> b} -> a -> Mem f b
call x = case lookup x !get of
    Nothing => do
        let y = f x
        modify $ insert x y
        pure y
    Just y => pure y

runMem : Ord a => Mem {a} f c -> c
runMem x = evalState empty x

record Garden where
    constructor MkGarden
    rocks : SortedSet Coord
    start : Coord
    height : Integer
    width : Integer

%hint
showGarden : Show Garden
showGarden = %runElab derive

dists : (g : Garden) ->
        {default g.start start : Coord} ->
        SortedMap Coord Nat
dists g = dists' 0 (singleton start) empty
  where
    inGarden : Coord -> Bool
    inGarden (x, y) =
        0 <= x && x < g.width &&
        0 <= y && y < g.height

    dists' : Nat ->
             SortedSet Coord ->
             SortedMap Coord Nat ->
             SortedMap Coord Nat
    dists' n open_ closed = if null open_
        then closed
        else do
            let closed = mergeWith min (SortedMap.fromList $ map (, n) $ SortedSet.toList open_) closed
            let open_ = SortedSet.fromList $ do
                c <- SortedSet.toList open_
                d <- [N, E, S, W]
                let cNew = move d c
                guard $ inGarden cNew
                guard $ isNothing $ lookup cNew closed
                guard $ not $ contains cNew g.rocks
                pure cNew
            assert_total $ dists' (S n) open_ closed

reachable : Garden ->
            Nat ->
            SortedSet Coord
reachable g n = do
    let ds = dists g
    let arity = mod n 2
    SortedSet.fromList $ map fst $ filter ((\k => k <= n && mod k 2 == arity) . snd) $ SortedMap.toList ds

record Coverage where
    constructor MkCoverage
    neighbours : List (Direction, Coord, Nat)
    dMax : Nat
    reachableMax : (Nat, Nat)
    ds : SortedMap Coord Nat

coverage : Garden -> (start : Coord) -> Coverage
coverage g start = do
    let ds = dists {start} g
    let dsList = SortedMap.toList ds

    -- Assumes each neighbour can be treated as though it only has one entrance point.
    -- This is false for the small example, but true for the input.
    let xMax = cast $ g.width - 1
    let yMax = cast $ g.height - 1
    let borderBy = \f => minimumBy snd $ filter (\(c, d) => f c) dsList
    let borderNorth = borderBy $ \(x, y) => y == 0
    let borderEast = borderBy $ \(x, y) => x == xMax
    let borderWest = borderBy $ \(x, y) => x == 0
    let borderSouth = borderBy $ \(x, y) => y == yMax

    let neighbours : List (Direction, Coord, Nat) =
        maybe [] (pure . (N,) . mapSnd S . mapFst (mapSnd $ const yMax)) borderNorth ++
        maybe [] (pure . (E,) . mapSnd S . mapFst (mapFst $ const 0)) borderEast ++
        maybe [] (pure . (W,) . mapSnd S . mapFst (mapFst $ const xMax)) borderWest ++
        maybe [] (pure . (S,) . mapSnd S . mapFst (mapSnd $ const 0)) borderSouth

    let dMax = maximum $ values ds
    let reachableMax' = \arity => foldr (\(c, d), n => (cast $ mod d 2 == arity) + n) (the Nat 0) dsList
    let reachableMax = (reachableMax' 0, reachableMax' 1)

    MkCoverage neighbours dMax reachableMax ds

reachable' : Garden -> Nat -> Nat
reachable' g n = sum $ values $ runMem {f = coverage g} $ do
    reachable'' (singleton (0, 0) (!(call {f = coverage g} g.start), n)) empty
  where
    reachable'' : SortedMap Coord (Coverage, Nat) ->
                  SortedMap Coord Nat ->
                  Mem (coverage g) (SortedMap Coord Nat)
    reachable'' open_ closed = if null open_
        then pure closed
        else do
            let closed = mergeLeft
                    (map (\(cvg, stepsRemaining) =>
                        if stepsRemaining >= cvg.dMax
                            then if mod stepsRemaining 2 == 0
                                then fst cvg.reachableMax
                                else snd cvg.reachableMax
                            else do
                                let arity = mod stepsRemaining 2
                                foldr (\(c, d), n => (cast $ mod d 2 == arity && d <= stepsRemaining) + n) 0 $ SortedMap.toList cvg.ds
                    ) open_) closed
            open_ <- foldlM
                (\open_, (cTile, cvg, stepsRemaining) => do
                    neighbours <- traverse (\(newTile, start, steps) => do
                            cvg <- call {f = coverage g} start
                            pure (newTile, cvg, minus stepsRemaining steps)
                        ) $
                        filter (\(newTile, _, d) => d <= stepsRemaining && isNothing (lookup newTile closed)) $
                        map (\(dir, start, steps) => (move dir cTile, start, steps)) cvg.neighbours
                    pure $ mergeWith (minBy $ compare `on` snd) (SortedMap.fromList neighbours) open_)
                empty
                (SortedMap.toList open_)
            assert_total $ reachable'' open_ closed

covering
garden : Parse2D Garden
garden = do
    background '.'
    objs <- many $ lexeme '.' [| (
        coord,
        object '#' False <|> object 'S' True
      ) |]
    eos
    let rocks = SortedSet.fromList $ map fst $ filter (not . snd) objs
    let [start] = map fst $ filter snd objs
        | [] => fail "No starting position"
        | _ => fail "Multiple starting positions"
    pure $ MkGarden rocks start (cast !height) (cast !width)

covering
main : IO ()
main = do
    let eg = """
    ...........
    .....###.#.
    .###.##..#.
    ..#.#...#..
    ....#.#....
    .##..S####.
    .##..#...#.
    .......##..
    .##.#.####.
    .##..##.##.
    ...........
    """

    let Right (eg, _) = parse2d garden eg
        | Left err => putStrLn err

    Right input <- readFile "Day21/input"
            | Left err => printLn err

    let Right (input, _) = parse2d garden input
            | Left err => putStrLn err

    putStrLn "Part 1"
    printLn $ length $ SortedSet.toList $ reachable eg 6
    printLn $ length $ SortedSet.toList $ reachable input 64

    putStrLn "Part 2"
    -- Stepping a garden width at a time, the solution is a quadratic
    -- Extrapolate the solution from the blow points
    printLn $ reachable' input 196
    printLn $ reachable' input 327
    printLn $ reachable' input 458
