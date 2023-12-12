module Day8.Day8

import Data.String
import Data.String.Parser
import System.File

import Day8.Part1
import Day8.Part2

instructions : Parser (List Direction)
instructions = lexeme $ many $
    (char 'L' *> pure L) <|>
    (char 'R' *> pure R)

network : Parser (SortedMap String (String, String))
network = map fromList $ many $ do
    source <- node <* lexeme (char '=')
    targets <- lexeme $ parens [| (node <* lexeme (char ','), node) |]
    pure (source, targets)
  where
    node : Parser String
    node = lexeme $ map pack $ many alphaNum

doc : Parser Doc
doc = do
    ins@(_ :: _) <- instructions
        | [] => fail "No instructions"
    nwk <- network
    eos
    pure $ MkDoc (fromList ins) nwk

main : IO ()
main = do
    let eg1 = """
    RL

    AAA = (BBB, CCC)
    BBB = (DDD, EEE)
    CCC = (ZZZ, GGG)
    DDD = (DDD, DDD)
    EEE = (EEE, EEE)
    GGG = (GGG, GGG)
    ZZZ = (ZZZ, ZZZ)
    """

    let Right (eg1, _) = parse doc eg1
        | Left err => putStrLn err

    let eg2 = """
    LLR

    AAA = (BBB, BBB)
    BBB = (AAA, ZZZ)
    ZZZ = (ZZZ, ZZZ)
    """

    let Right (eg2, _) = parse doc eg2
        | Left err => putStrLn err

    Right input <- readFile "Day8/input"
        | Left err => printLn err

    let Right (input, _) = parse doc input
        | Left err => putStrLn err

    putStrLn "Part 1"
    printLn $ followDoc eg1
    printLn $ followDoc eg2
    printLn $ followDoc input

    let eg3 = """
    LR

    11A = (11B, XXX)
    11B = (XXX, 11Z)
    11Z = (11B, XXX)
    22A = (22B, XXX)
    22B = (22C, 22C)
    22C = (22Z, 22Z)
    22Z = (22B, 22B)
    XXX = (XXX, XXX)
    """

    let Right (eg3, _) = parse doc eg3
        | Left err => putStrLn err

    putStrLn "Part 2"
    putStrLn "eg3:"
    traverse_ printLn $ map (nextZs eg3) $ filter (isSuffixOf "A") $ keys eg3.network
    putStrLn "input:"
    traverse_ printLn $ map (nextZs input) $ filter (isSuffixOf "A") $ keys input.network
