import Data.Fin
import Data.List
import Data.List.Alternating
import Data.String
import Data.String.Parser

import System.File

namespace Part1
    export
    calibrationValue : Parser Nat
    calibrationValue = do
        xs <- evens <$> alternating (many letter) digit
        let n = maybe (the (Fin 10) 0) id (head' xs)
        let m = maybe (the (Fin 10) 0) id (last' xs)
        pure $ 10 * cast n + cast m

    export
    calibrationValues : Parser (List Nat)
    calibrationValues = many (calibrationValue <* char '\n') <* eos

    export
    calibrationTotal : Parser Nat
    calibrationTotal = sum <$> calibrationValues

namespace Part2
    export
    nonConsuming : Functor m => ParseT m a -> ParseT m a
    nonConsuming (P p) = P $ \s => flip map (p s) $ \case
        OK x _ => OK x s
        Fail i err => Fail i err

    export
    word : String -> a -> Parser a
    word str x = case strUncons str of
        Nothing => pure x
        Just (head, tail) => do
            ignore $ char head
            ignore $ nonConsuming $ string tail
            pure x

    export
    digitWord : Parser (Fin 10)
    digitWord =
        (word "one" 1) <|>
        (word "two" 2) <|>
        (word "three" 3) <|>
        (word "four" 4) <|>
        (word "five" 5) <|>
        (word "six" 6) <|>
        (word "seven" 7) <|>
        (word "eight" 8) <|>
        (word "nine" 9)

    export
    nextDigit : Parser (Fin 10)
    nextDigit = digitWord <|> digit <|> (letter *> nextDigit)

    export
    calibrationValue : {default Nothing firstVal : Maybe (Fin 10)} ->
                       {default 0 lastVal : Fin 10} ->
                       Parser Nat
    calibrationValue = (do
        n <- nextDigit
        calibrationValue {firstVal = Just $ maybe n id firstVal} {lastVal = n}
      ) <|> (do
        ignore $ many letter
        let n = maybe (the (Fin 10) 0) id firstVal
        let m = lastVal
        pure $ 10 * cast n + cast m
      )

    export
    calibrationValues : Parser (List Nat)
    calibrationValues = many (Part2.calibrationValue <* char '\n') <* eos

    export
    calibrationTotal : Parser Nat
    calibrationTotal = sum <$> Part2.calibrationValues

main : IO ()
main = do
    Right input <- readFile "Day1/input"
        | Left err => printLn err

    putStrLn "Part 1"
    printLn $ parse Part1.calibrationValues """
    1abc2
    pqr3stu8vwx
    a1b2c3d4e5f
    treb7uchet

    """
    printLn $ parse Part1.calibrationTotal input

    putStrLn "Part 2"
    printLn $ parse Part2.calibrationValues """
    two1nine
    eightwothree
    abcone2threexyz
    xtwone3four
    4nineeightseven2
    zoneight234
    7pqrstsixteen

    """
    printLn $ parse Part2.calibrationTotal input
