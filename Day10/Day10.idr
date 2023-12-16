import Control.Monad.State
import Data.Fuel
import Data.SortedMap
import Data.SortedSet
import Data.String.Parser
import Deriving.Show
import System.File

import Data.String.Parse2D

%default total
%language ElabReflection

maximum : List Nat -> Nat
maximum ks = foldr max 0 ks

data Pipe = PV | PH | PL | PJ | P7 | PF | PS

Eq Pipe where
    (==) = on (==) $ \case PV => 0; PH => 1; PL => 2; PJ => 3; P7 => 4; PF => 5; PS => 6

%hint
showPipe : Show Pipe
showPipe = %runElab derive

dirs : Pipe -> List Direction
dirs PV = [N, S]
dirs PH = [E, W]
dirs PL = [N, E]
dirs PJ = [N, W]
dirs P7 = [S, W]
dirs PF = [E, S]
dirs PS = [N, E, S, W]

adjacent : Coord -> Pipe -> List (Coord, Direction)
adjacent c p = map (\d => (move d c, complement d)) $ dirs p

Landscape : Type
Landscape = SortedMap Coord Pipe

connected : Landscape -> Coord -> List (Coord, Direction)
connected l c = case lookup c l of
    Nothing => []
    Just p => filter (\(c', d) => elem d (maybe [] dirs $ lookup c' l)) $ adjacent c p

dists : Landscape -> SortedMap Coord Nat
dists l = dists' (limit $ length $ keys l) (map fst $ filter (\(c, p) => p == PS) $ SortedMap.toList l) 0 empty
  where
    dists' : Fuel -> List Coord -> Nat -> SortedMap Coord Nat -> SortedMap Coord Nat
    dists' Dry cs n ds = ds
    dists' (More f) [] n ds = ds
    dists' (More f) cs n ds = do
        let ds = mergeWith min (fromList $ map (, n) cs) ds
        let cs = filter (\c => isNothing $ lookup c ds) $ map fst $ cs >>= connected l
        dists' f cs (S n) ds

maxDist : Landscape -> Nat
maxDist l = maximum $ values $ dists l

startPipeType : Landscape -> Maybe (Coord, Pipe)
startPipeType l = do
    let [(c, PS)] = filter (\(c, p) => p == PS) $ SortedMap.toList l
        | _ => Nothing
    p <- case map snd $ connected l c of
        [S, N] => pure PV
        [W, E] => pure PH
        [S, W] => pure PL
        [S, E] => pure PJ
        [N, E] => pure P7
        [W, N] => pure PF
        _ => Nothing
    pure (c, p)

loop : Landscape -> Landscape
loop l = do
    let ds = dists l
    let l = SortedMap.fromList $
          filter (\(c, p) => isJust $ lookup c ds) $
          SortedMap.toList l
    case startPipeType l of
          Nothing => l
          Just (c, p) => insert c p l

enclosed : Landscape -> SortedSet Coord
enclosed l = do
    let maxX = cast $ maximum $ map (cast . fst) $ keys l
    let maxY = cast $ maximum $ map (cast . snd) $ keys l
    let bound : Coord = (maxX, maxY)
    let l : Landscape = loop l
    let hs : SortedSet Coord = SortedSet.fromList $
        map {a = (_, _)} fst $
        filter (\(c, p) => elem p [PH, PJ, P7]) $
        SortedMap.toList l
    fst $ foldr
        (\c, (res, curIn) => if contains c hs
            then (res, not curIn)
            else if curIn && not (isJust $ lookup c l)
                then (insert c res, curIn)
                else (res, curIn))
        (empty, False)
        [| ([0..maxX], [0..maxY]) |]

covering
landscape : Parse2D Landscape
landscape = background '.' *> (map fromList $ many (lexeme '.' [| (coord, pipe) |])) <* eos
  where
    pipe : Parse2D Pipe
    pipe =
        object '|' PV <|>
        object '-' PH <|>
        object 'L' PL <|>
        object 'J' PJ <|>
        object '7' P7 <|>
        object 'F' PF <|>
        object 'S' PS

covering
main : IO ()
main = do
    let eg1 = """
    .....
    .S-7.
    .|.|.
    .L-J.
    .....
    """

    let Right (eg1, _) = parse2d landscape eg1
        | Left err => putStrLn err

    let eg2 = """
    ..F7.
    .FJ|.
    SJ.L7
    |F--J
    LJ...
    """

    let Right (eg2, _) = parse2d landscape eg2
        | Left err => putStrLn err

    Right input <- readFile "Day10/input"
        | Left err => printLn err

    let Right (input, _) = parse2d landscape input
        | Left err => putStrLn err

    putStrLn "Part 1"
    printLn $ dists eg1
    printLn $ dists eg2
    printLn $ maxDist eg2
    printLn $ maxDist input

    let eg3 = """
    ...........
    .S-------7.
    .|F-----7|.
    .||.....||.
    .||.....||.
    .|L-7.F-J|.
    .|..|.|..|.
    .L--J.L--J.
    ...........
    """

    let Right (eg3, _) = parse2d landscape eg3
        | Left err => putStrLn err

    let eg4 = """
    FF7FSF7F7F7F7F7F---7
    L|LJ||||||||||||F--J
    FL-7LJLJ||||||LJL-77
    F--JF--7||LJLJ7F7FJ-
    L---JF-JLJ.||-FJLJJ7
    |F|F-JF---7F7-L7L|7|
    |FFJF7L7F-JF7|JL---7
    7-L-JL7||F7|L7F-7F7|
    L.L7LFJ|||||FJL7||LJ
    L7JLJL-JLJLJL--JLJ.L
    """

    let Right (eg4, _) = parse2d landscape eg4
        | Left err => putStrLn err

    putStrLn "Part 2"
    printLn $ enclosed eg3
    printLn $ enclosed eg4
    printLn $ length $ SortedSet.toList $ enclosed input
