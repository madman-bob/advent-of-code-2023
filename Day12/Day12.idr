import Data.List.Alternating
import Data.String.Parser
import Deriving.Show
import System.File

import Data.Counter

%default total
%language ElabReflection

data SpringStatus = Operational | Damaged | Unknown

%hint
showSpringStatus : Show SpringStatus
showSpringStatus = %runElab derive

Eq SpringStatus where
    (==) = on (==) $ \case Operational => 0; Damaged => 1; Unknown => 2

Ord SpringStatus where
    compare = on compare $ \case Operational => 0; Damaged => 1; Unknown => 2

record Row where
    constructor MkRow
    springStatuses : List SpringStatus
    damageGroups : List Nat

%hint
showRow : Show Row
showRow = %runElab derive

matches : Row -> Nat
matches r = do
    let c : Counter _ = foldl
          (\cs, s => do
              op <- operational s
              (n, gs) <- cs
              step op n gs
          )
          (pure (Nothing, r.damageGroups))
          r.springStatuses
    lookup (Nothing, []) c + lookup (Just 0, []) c
  where
    operational : SpringStatus -> Counter Bool
    operational Operational = pure True
    operational Damaged = pure False
    operational Unknown = pure False <|> pure True

    step : Bool -> Maybe Nat -> List Nat -> Counter (Maybe Nat, List Nat)
    step False Nothing [] = empty
    step False Nothing (n :: gs) = pure (Just $ minus n 1, gs)
    step False (Just 0) gs = empty
    step False (Just (S n)) gs = pure (Just n, gs)
    step True Nothing gs = pure (Nothing, gs)
    step True (Just 0) gs = pure (Nothing, gs)
    step True (Just (S n)) gs = empty

unfoldRow : Row -> Row
unfoldRow (MkRow ss gs) = MkRow
    (join $ intersperse [Unknown] $ replicate 5 ss)
    (join $ replicate 5 gs)

covering
row : Parser Row
row = [| MkRow (lexeme $ many springStatus) (lexeme $ map odds $ alternating natural $ char ',') |]
  where
    springStatus : Parser SpringStatus
    springStatus =
        (char '.' *> pure Operational) <|>
        (char '#' *> pure Damaged) <|>
        (char '?' *> pure Unknown)

covering
records : Parser (List Row)
records = many row <* eos

covering
main : IO ()
main = do
    let eg = """
    ???.### 1,1,3
    .??..??...?##. 1,1,3
    ?#?#?#?#?#?#?#? 1,3,1,6
    ????.#...#... 4,1,1
    ????.######..#####. 1,6,5
    ?###???????? 3,2,1
    """

    let Right (eg, _) = parse records eg
        | Left err => putStrLn err

    Right input <- readFile "Day12/input"
        | Left err => printLn err

    let Right (input, _) = parse records input
        | Left err => putStrLn err

    putStrLn "Part 1"
    printLn $ map matches eg
    printLn $ sum $ map matches input

    putStrLn "Part 2"
    printLn $ map (matches . unfoldRow) eg
    printLn $ sum $ map (matches . unfoldRow) input
