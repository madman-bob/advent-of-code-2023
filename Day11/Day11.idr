import Control.Monad.State
import Data.List
import Data.SortedMap
import Data.SortedSet
import Data.String.Parser
import System.File

%default total

combinations : List a -> List (a, a)
combinations [] = []
combinations (x :: xs) = map (x,) xs ++ combinations xs

Coord : Type
Coord = (Integer, Integer)

Image : Type
Image = SortedSet Coord

gCols : Image -> SortedSet Integer
gCols i = SortedSet.fromList $ map fst $ SortedSet.toList i

gRows : Image -> SortedSet Integer
gRows i = SortedSet.fromList $ map snd $ SortedSet.toList i

dists : Image ->
        {default 2 expansionFactor : Integer} ->
        List ((Coord, Coord), Integer)
dists i = do
    let cs = SortedSet.toList $ gCols i
    let rs = SortedSet.toList $ gRows i
    map {f = List} (\(c, d) => ((c, d), dist cs rs c d)) $ combinations $ SortedSet.toList i
  where
    countBetween : List Integer -> Integer -> Integer -> Nat
    countBetween ks i j = length $ takeWhile (< max i j) $ dropWhile (< min i j) ks

    dist : (cs : List Integer) -> (rs : List Integer) -> Coord -> Coord -> Integer
    dist cs rs (x1, y1) (x2, y2) =
          expansionFactor * (abs $ x2 - x1)
        + expansionFactor * (abs $ y2 - y1)
        - (expansionFactor - 1) * cast (countBetween rs y1 y2)
        - (expansionFactor - 1) * cast (countBetween cs x1 x2)

totalDists : Image -> {default 2 expansionFactor : Integer} -> Integer
totalDists i = sum $ map snd $ dists {expansionFactor} i

covering
image : ParseT (State Coord) Image
image = map fromList $ many (lexeme galaxy) <* lexeme eos
  where
    char : Char -> a -> ParseT (State Coord) a
    char c x = Parser.char c *> lift (modify $ mapFst (1 +)) *> pure x

    newline : ParseT (State Coord) ()
    newline = Parser.char '\n' *> lift (modify $ \(x, y) => (0, 1 + y))

    galaxy : ParseT (State Coord) Coord
    galaxy = char '#' !(lift get)

    ground : ParseT (State Coord) ()
    ground = char '.' ()

    lexeme : ParseT (State Coord) a -> ParseT (State Coord) a
    lexeme p = many (ground <|> newline) *> p

covering
main : IO ()
main = do
    let eg = """
    ...#......
    .......#..
    #.........
    ..........
    ......#...
    .#........
    .........#
    ..........
    .......#..
    #...#.....
    """

    let Right (eg, _) = evalState (0, 0) $ parseT image eg
        | Left err => putStrLn err

    Right input <- readFile "Day11/input"
        | Left err => printLn err

    let Right (input, _) = evalState (0, 0) $ parseT image input
        | Left err => putStrLn err

    putStrLn "Part 1"
    printLn $ totalDists eg
    printLn $ totalDists input

    putStrLn "Part 2"
    printLn $ totalDists {expansionFactor = 10} eg
    printLn $ totalDists {expansionFactor = 100} eg
    printLn $ totalDists {expansionFactor = 1_000_000} input
