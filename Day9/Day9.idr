import Data.List
import Data.String.Parser
import Data.Vect
import Data.Zippable
import System.File

%default total

diffs : Vect (S n) Integer -> Vect n Integer
diffs ks = zipWith (-) (tail ks) (init ks)

extrapolate : Vect n Integer -> Integer
extrapolate [] = 0
extrapolate ks@(k :: _) = do
    let ds = diffs ks
    if all (== 0) ds
        then k
        else last ks + extrapolate ds

extrapolateBack : Vect n Integer -> Integer
extrapolateBack [] = 0
extrapolateBack ks@(k :: _) = do
    let ds = diffs ks
    if all (== 0) ds
        then k
        else k - extrapolateBack ds

covering
vals : Parser (List (List Integer))
vals = many (many (integer <* optional (char ' ')) <* char '\n') <* eos

covering
main : IO ()
main = do
    let eg = """
    0 3 6 9 12 15
    1 3 6 10 15 21
    10 13 16 21 30 45

    """

    let Right (eg, _) = parse vals eg
        | Left err => putStrLn err

    Right input <- readFile "Day9/input"
        | Left err => printLn err

    let Right (input, _) = parse vals input
        | Left err => putStrLn err

    putStrLn "Part 1"
    printLn $ map (\ks => extrapolate $ fromList ks) eg
    printLn $ sum $ map (\ks => extrapolate $ fromList ks) input

    putStrLn "Part 2"
    printLn $ map (\ks => extrapolateBack $ fromList ks) eg
    printLn $ sum $ map (\ks => extrapolateBack $ fromList ks) input
