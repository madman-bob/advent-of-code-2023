import Control.Monad.State
import Data.List
import Data.SortedMap
import Data.String.Parser
import Deriving.Show
import System.File

%language ElabReflection

record Card where
    constructor MkCard
    cardId : Nat
    winningNums : List Nat
    haveNums : List Nat

%hint
showCard : Show Card
showCard = %runElab derive

matches : Card -> Nat
matches c = length $ intersect c.winningNums c.haveNums

points : Card -> Nat
points c = points' $ matches c
  where
    points' : Nat -> Nat
    points' 0 = 0
    points' 1 = 1
    points' (S n) = 2 * points' n

addCards : (cardId : Nat) -> (count : Nat) -> State (SortedMap Nat Nat) ()
addCards cardId count = modify $ mergeWith (+) (singleton cardId count)

addCardWinnings : (cardId : Nat) ->
                 (count : Nat) ->
                 (matches : Nat) ->
                 State (SortedMap Nat Nat) ()
addCardWinnings cardId count 0 = pure ()
addCardWinnings cardId count (S matches) = do
    addCards (S cardId) count
    addCardWinnings (S cardId) count matches

counts : List Card -> SortedMap Nat Nat
counts cs = execState empty $ for cs $ \c => do
    addCards c.cardId 1
    let count = maybe 0 id $ lookup c.cardId !get
    addCardWinnings c.cardId count $ matches c

card : Parser Card
card = [| MkCard
    (token "Card" *> natural <* token ":")
    (many (lexeme natural) <* token "|")
    (many (lexeme natural))
  |]

cards : Parser (List Card)
cards = many card <* eos

main : IO ()
main = do
    let eg = """
    Card 1: 41 48 83 86 17 | 83 86  6 31 17  9 48 53
    Card 2: 13 32 20 16 61 | 61 30 68 82 17 32 24 19
    Card 3:  1 21 53 59 44 | 69 82 63 72 16 21 14  1
    Card 4: 41 92 73 84 69 | 59 84 76 51 58  5 54 83
    Card 5: 87 83 26 28 32 | 88 30 70 12 93 22 82 36
    Card 6: 31 18 13 56 72 | 74 77 10 23 35 67 36 11

    """

    let Right (eg, _) = parse cards eg
        | Left err => putStrLn err

    Right input <- readFile "Day4/input"
        | Left err => printLn err

    let Right (input, _) = parse cards input
        | Left err => putStrLn err

    putStrLn "Part 1"
    printLn $ map points eg
    printLn $ sum $ map points input

    putStrLn "Part 2"
    printLn $ counts eg
    printLn $ sum $ values $ counts input
