||| If we hold the button for n ms in a race of duration d ms, we travel a total
||| distance of n * (d - n) mm.
|||
||| For a previous record r, we want the number of values n for which
||| n * (d - n) > r.
|||
||| Rearrange to get n^2 - d*n + r < 0.
||| Apply quadratic formula to find n between (d +- sqrt (d^2 - 4*r)) / 2.

import Data.String.Parser
import Deriving.Show
import System.File

%language ElabReflection

record Race where
    constructor MkRace
    len : Nat
    rec : Nat

%hint
showRace : Show Race
showRace = %runElab derive

winMargin : Race -> Nat
winMargin r = do
    let residue = sqrt $ cast $ minus (r.len * r.len) (4 * r.rec)
    cast $ ceiling ((cast r.len + residue) / 2) - floor ((cast r.len - residue) / 2) - 1

races : Parser (List Race)
races = do
    lens <- token "Time:" *> many (lexeme natural)
    recs <- token "Distance:" *> many (lexeme natural)
    eos
    pure $ zipWith MkRace lens recs

race : Parser Race
race = [| MkRace (token "Time:" *> natural) (token "Distance:" *> natural) |] <* eos
  where
    natural : Parser Nat
    natural = map (cast . pack) $ many (lexeme (satisfy isDigit))

main : IO ()
main = do
    let eg = """
    Time:      7  15   30
    Distance:  9  40  200
    """

    let Right (eg1, _) = parse races eg
        | Left err => putStrLn err

    Right input <- readFile "Day6/input"
            | Left err => printLn err

    let Right (input1, _) = parse races input
        | Left err => putStrLn err

    putStrLn "Part 1"
    printLn $ map winMargin eg1
    printLn $ product $ map winMargin input1

    let Right (eg2, _) = parse race eg
        | Left err => putStrLn err

    let Right (input2, _) = parse race input
        | Left err => putStrLn err

    putStrLn "Part 2"
    printLn $ winMargin eg2
    printLn $ winMargin input2
