import Data.Fuel
import Data.SortedSet
import Data.SortedMap
import Deriving.Show
import System.File

import Data.String.Parse2D

%default total
%language ElabReflection

maximum : Foldable f => f Nat -> Nat
maximum ns = foldr max 0 ns

data Mirror = MirrorF | MirrorB | SplitV | SplitH

%hint
showMirror : Show Mirror
showMirror = %runElab derive

record Contraption where
    constructor MkContraption
    mirrors : SortedMap Coord Mirror
    height : Nat

Show Contraption where
    show ctp = "MkContraption (\{show ctp.mirrors}) \{show ctp.height}"

deflect : Direction -> Mirror -> List Direction
deflect N MirrorF = pure E
deflect E MirrorF = pure N
deflect S MirrorF = pure W
deflect W MirrorF = pure S
deflect N MirrorB = pure W
deflect E MirrorB = pure S
deflect S MirrorB = pure E
deflect W MirrorB = pure N
deflect N SplitV = pure N
deflect E SplitV = pure N <|> pure S
deflect S SplitV = pure S
deflect W SplitV = pure N <|> pure S
deflect N SplitH = pure E <|> pure W
deflect E SplitH = pure E
deflect S SplitH = pure E <|> pure W
deflect W SplitH = pure W

inBounds : Contraption -> Coord -> Bool
inBounds ctp (x, y) = do
    let h = cast ctp.height
    x >= 0 && x < h && y >= 0 && y < h

step : Contraption -> Coord -> Direction -> List (Coord, Direction)
step ctp c d = do
    let c = move d c
    if inBounds ctp c
        then do
            d <- maybe (pure d) (deflect d) $ lookup c ctp.mirrors
            pure (c, d)
        else empty

beam : Contraption ->
       {default (-1, 0) start : Coord} ->
       {default E startDir : Direction} ->
       SortedSet Coord
beam ctp = delete start $ SortedSet.fromList $ map fst $ SortedSet.toList $
    beam' (limit $ 4 * ctp.height * ctp.height) (pure (start, startDir)) empty
  where
    beam' : Fuel -> List (Coord, Direction) -> SortedSet (Coord, Direction) -> SortedSet (Coord, Direction)
    beam' Dry curr prev = prev
    beam' (More f) [] prev = prev
    beam' (More f) curr prev = do
        let prev = union (SortedSet.fromList curr) prev
        let next = filter (not . flip contains prev) $ curr >>= (uncurry $ step ctp)
        beam' f next prev

maxBeam : Contraption -> Nat
maxBeam ctp = maximum $ map (\(start, startDir) => length $ SortedSet.toList $ beam ctp {start} {startDir}) starts
  where
    starts : List (Coord, Direction)
    starts = do
        let h = cast ctp.height
        [((x, -1), S) | x <- [0..h - 1]] ++
        [((x, h), N) | x <- [0..h - 1]] ++
        [((-1, y), E) | y <- [0..h - 1]] ++
        [((h, y), W) | y <- [0..h - 1]]

mirror : Parse2D Mirror
mirror =
    (object '/' MirrorF) <|>
    (object '\\' MirrorB) <|>
    (object '|' SplitV) <|>
    (object '-' SplitH)

covering
contraption : Parse2D Contraption
contraption = background '.' *> [| MkContraption
    (map fromList $ many $ lexeme '.' [| (coord, mirror) |])
    (map (cast . snd) coord)
  |] <* eos

covering
main : IO ()
main = do
    let eg = """
    .|...\\....
    |.-.\\.....
    .....|-...
    ........|.
    ..........
    .........\\
    ..../.\\\\..
    .-.-/..|..
    .|....-|.\\
    ..//.|....

    """

    putStrLn eg

    let Right (eg, _) = parse2d contraption eg
        | Left err => putStrLn err

    Right input <- readFile "Day16/input"
        | Left err => printLn err

    let Right (input, _) = parse2d contraption input
        | Left err => putStrLn err

    putStrLn "Part 1"
    printLn $ length $ SortedSet.toList $ beam eg
    printLn $ length $ SortedSet.toList $ beam input

    putStrLn "Part 2"
    printLn $ maxBeam eg
    printLn $ maxBeam input
