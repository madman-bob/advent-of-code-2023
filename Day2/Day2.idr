import Data.List.Alternating
import Data.String.Parser
import System.File

record Handful where
    constructor MkHandful
    red : Nat
    green : Nat
    blue : Nat

redHandful : Nat -> Handful
redHandful n = MkHandful n 0 0

greenHandful : Nat -> Handful
greenHandful n = MkHandful 0 n 0

blueHandful : Nat -> Handful
blueHandful n = MkHandful 0 0 n

Show Handful where
    show (MkHandful red green blue) = "MkHandful \{show red} \{show green} \{show blue}"

Semigroup Handful where
    (MkHandful r1 g1 b1) <+> (MkHandful r2 g2 b2) = MkHandful (r1 + r2) (g1 + g2) (b1 + b2)

Monoid Handful where
    neutral = MkHandful 0 0 0

[OrSemigroup] Semigroup Handful where
    (MkHandful r1 g1 b1) <+> (MkHandful r2 g2 b2) = MkHandful (max r1 r2) (max g1 g2) (max b1 b2)

[OrMonoid] Monoid Handful using OrSemigroup where
    neutral = MkHandful 0 0 0

possibleHandful : (larger : Handful) -> (smaller : Handful) -> Bool
possibleHandful (MkHandful r1 g1 b1) (MkHandful r2 g2 b2) =
    (r2 <= r1) && (g2 <= g1) && (b2 <= b1)

power : Handful -> Nat
power (MkHandful r g b) = r * g * b

handful : Parser Handful
handful = concat <$> odds <$> alternating
    (do
        n <- natural
        ignore $ char ' '
        map ($ n) (
            (string "red" *> pure redHandful) <|>
            (string "green" *> pure greenHandful) <|>
            (string "blue" *> pure blueHandful)
          ))
    (string ", ")

record Game where
    constructor MkGame
    id : Nat
    handfuls : List Handful

Show Game where
    show (MkGame id handfuls) = "MkGame \{show id} \{show handfuls}"

game : Parser Game
game = do
    ignore $ string "Game "
    n <- natural
    ignore $ string ": "
    handfuls <- map odds $ alternating handful (string "; ")
    pure $ MkGame n handfuls

possibleGame : Handful -> Game -> Bool
possibleGame handful game = all (possibleHandful handful) game.handfuls

coverage : Game -> Handful
coverage game = concat @{OrMonoid} game.handfuls

games : Parser (List Game)
games = many (game <* char '\n') <* eos

main : IO ()
main = do
    let eg = """
    Game 1: 3 blue, 4 red; 1 red, 2 green, 6 blue; 2 green
    Game 2: 1 blue, 2 green; 3 green, 4 blue, 1 red; 1 green, 1 blue
    Game 3: 8 green, 6 blue, 20 red; 5 blue, 4 red, 13 green; 5 green, 1 red
    Game 4: 1 green, 3 red, 6 blue; 3 green, 6 red; 3 green, 15 blue, 14 red
    Game 5: 6 red, 1 blue, 3 green; 2 blue, 1 red, 2 green

    """

    let Right (eg, _) = parse games eg
        | Left _ => putStrLn "Parse error"

    Right input <- readFile "Day2/input"
        | Left err => printLn err

    let Right (input, _) = parse games input
        | Left _ => putStrLn "Parse error"

    putStrLn "Part 1"
    printLn $ map Game.id $ filter (possibleGame $ MkHandful 12 13 14) eg
    printLn $ sum $ map Game.id $ filter (possibleGame $ MkHandful 12 13 14) input

    putStrLn "Part2"
    printLn $ map (power . coverage) eg
    printLn $ sum $ map (power . coverage) eg
