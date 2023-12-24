import Data.Fin
import Deriving.Show
import System.File

import Data.String.Parse2D

%default total
%language ElabReflection

minimum : List Integer -> Integer
minimum xs = foldr min 1_000_000_000 xs

maximum : List Integer -> Integer
maximum xs = foldr max (-1_000_000_000) xs

record Instruction where
    constructor MkInstruction
    dir : Direction
    dist : Nat
    color : String

%hint
showInstruction : Show Instruction
showInstruction = %runElab derive

record VEdge where
    constructor MkVEdge
    top : Coord
    height : Nat

(.x) : VEdge -> Integer
ve.x = fst ve.top

(.topY) : VEdge -> Integer
ve.topY = snd ve.top

(.bottomY) : VEdge -> Integer
ve.bottomY = ve.topY + cast ve.height

%hint
showVEdge : Show VEdge
showVEdge = %runElab derive

vEdges : List Instruction -> List VEdge
vEdges is = snd $ foldl
    (\(c, es), i => (
        moveN i.dist i.dir c,
        case i.dir of
            N => MkVEdge (moveN i.dist i.dir c) i.dist :: es
            S => MkVEdge c i.dist :: es
            _ => es))
    ((0, 0), [])
    is

interior : List Instruction -> Nat
interior is = do
    let ves = sortBy (on compare (.x)) $ vEdges is
    let minX = minimum $ map (.x) ves
    let maxX = maximum $ map (.x) ves
    let minY = minimum $ map (.topY) ves
    let maxY = maximum $ map (.bottomY) ves
    sum $ map
        (\currY =>
            fst $
            foldl (\case
                (w, Outside) => \ve => if ve.topY == currY
                    then (w, TopEdge ve.x)
                    else if ve.bottomY == currY
                        then (w, BottomEdge ve.x)
                        else (w, Inside ve.x)
                (w, Inside startX) => \ve => if ve.topY == currY
                    then (w, BottomEdge startX)
                    else if ve.bottomY == currY
                        then (w, TopEdge startX)
                        else (S (cast $ ve.x - startX) + w, Outside)
                (w, TopEdge startX) => \ve => if ve.topY == currY
                    then (S (cast $ ve.x - startX) + w, Outside)
                    else (w, Inside startX)
                (w, BottomEdge startX) => \ve => if ve.bottomY == currY
                    then (S (cast $ ve.x - startX) + w, Outside)
                    else (w, Inside startX))
                (0, Outside) $
            filter (\ve => ve.topY <= currY && currY <= ve.bottomY) ves)
        [minY..maxY]
  where
    data Status = Outside | Inside Integer | TopEdge Integer | BottomEdge Integer

namespace Part1
    export
    covering
    instruction : Parser Instruction
    instruction = [| MkInstruction
        (lexeme $
            (char 'U' *> pure N) <|>
            (char 'R' *> pure E) <|>
            (char 'D' *> pure S) <|>
            (char 'L' *> pure W)
        )
        (lexeme natural)
        (lexeme $ parens $ char '#' *> map pack (many alphaNum))
      |]

    export
    covering
    instructions : Parser (List Instruction)
    instructions = many instruction <* eos

namespace Part2
    hexDigit : Parser (Fin 16)
    hexDigit =
        (char '0' *> pure 0) <|> (char '1' *> pure 1) <|> (char '2' *> pure 2) <|> (char '3' *> pure 3) <|>
        (char '4' *> pure 4) <|> (char '5' *> pure 5) <|> (char '6' *> pure 6) <|> (char '7' *> pure 7) <|>
        (char '8' *> pure 8) <|> (char '9' *> pure 9) <|> (char 'a' *> pure 10) <|> (char 'b' *> pure 11) <|>
        (char 'c' *> pure 12) <|> (char 'd' *> pure 13) <|> (char 'e' *> pure 14) <|> (char 'f' *> pure 15)

    covering
    hexadecimal : Parser Nat
    hexadecimal = map (foldl (\n, d => 16 * n + cast d) 0) $ many hexDigit

    export
    covering
    instruction' : Parser Instruction
    instruction' = do
        color <- lexeme [| (lexeme $ map pack $ many letter) ++ (map cast natural) |]
        lenDir <- lexeme $ parens $ char '#' *> hexadecimal
        let len = div lenDir 16
        let dir = case mod lenDir 16 of
              0 => E
              1 => S
              2 => W
              _ => N
        pure $ MkInstruction dir len color

    export
    covering
    instructions' : Parser (List Instruction)
    instructions' = many instruction' <* eos

covering
main : IO ()
main = do
    let eg = """
    R 6 (#70c710)
    D 5 (#0dc571)
    L 2 (#5713f0)
    D 2 (#d2c081)
    R 2 (#59c680)
    D 2 (#411b91)
    L 5 (#8ceee2)
    U 2 (#caa173)
    L 1 (#1b58a2)
    U 2 (#caa171)
    R 2 (#7807d2)
    U 3 (#a77fa3)
    L 2 (#015232)
    U 2 (#7a21e3)
    """

    let Right (eg1, _) = parse instructions eg
        | Left err => putStrLn err

    Right input <- readFile "Day18/input"
        | Left err => printLn err

    let Right (input1, _) = parse instructions input
        | Left err => putStrLn err

    putStrLn "Part 1"
    printLn $ interior eg1
    printLn $ interior input1

    let Right (eg2, _) = parse instructions' eg
        | Left err => putStrLn err

    let Right (input2, _) = parse instructions' input
        | Left err => putStrLn err

    putStrLn "Part 2"
    printLn $ interior eg2
    printLn $ interior input2
