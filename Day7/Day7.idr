module Day7.Day7

import Data.String.Parser
import System.File

import Day7.Part1
import Day7.Part2

card : Parser Card
card =
    (char 'A' *> pure Ace) <|>
    (char 'K' *> pure King) <|>
    (char 'Q' *> pure Queen) <|>
    (char 'J' *> pure Jack) <|>
    (char 'T' *> pure Ten) <|>
    (char '9' *> pure Nine) <|>
    (char '8' *> pure Eight) <|>
    (char '7' *> pure Seven) <|>
    (char '6' *> pure Six) <|>
    (char '5' *> pure Five) <|>
    (char '4' *> pure Four) <|>
    (char '3' *> pure Three) <|>
    (char '2' *> pure Two)

hand : Parser (List Card)
hand = lexeme (many card)

game : Parser (List Play)
game = many [| MkPlay hand (lexeme natural) |] <* eos

main : IO ()
main = do
    let eg = """
    32T3K 765
    T55J5 684
    KK677 28
    KTJJT 220
    QQQJA 483
    """

    let Right (eg, _) = parse game eg
        | Left err => putStrLn err

    Right input <- readFile "Day7/input"
        | Left err => printLn err

    let Right (input, _) = parse game input
        | Left err => putStrLn err

    putStrLn "Part 1"
    printLn $ rank @{P1} eg
    printLn $ totalWinnings @{P1} eg
    printLn $ totalWinnings @{P1} input

    putStrLn "Part 2"
    printLn $ rank @{P2} eg
    printLn $ totalWinnings @{P2} eg
    printLn $ totalWinnings @{P2} input
