import Data.List1
import Data.SortedMap
import Data.String
import Data.String.Parser
import Deriving.Show
import System.File

%default total
%language ElabReflection

enum : Nat -> List a -> List (Nat, a)
enum n [] = []
enum n (x :: xs) = (n, x) :: enum (S n) xs

record Step where
    constructor MkStep
    label : String
    value : Maybe Nat

%hint
showStep : Show Step
showStep = %runElab derive

hash : String -> Nat
hash str = cast {from = Int} $ foldl (\v, c => mod (17 * (v + ord c)) 256) 0 $ unpack str

run : List Step -> SortedMap Nat (List (String, Nat))
run ss = foldl
    (\m, s => do
        let h = hash s.label
        let box = maybe [] id $ lookup h m
        let box = case s.value of
              Nothing => delete s.label box
              Just v => insert s.label v box
        SortedMap.insert h box m)
    empty
    ss
  where
    delete : String -> List (String, a) -> List (String, a)
    delete = deleteBy (\l, (l', _) => l == l')

    insert : String -> a -> List (String, a) -> List (String, a)
    insert l x [] = [(l, x)]
    insert l x ((l', y) :: xs) = if l == l'
        then (l, x) :: xs
        else (l', y) :: insert l x xs

power : SortedMap Nat (List (String, Nat)) -> Nat
power ls = sum $ map (\(h, box) => sum $ map (\(i, l, v) => (S h) * i * v) $ enum 1 box) $ SortedMap.toList ls

covering
step : Parser Step
step = [| MkStep
    (map pack $ some letter)
    ((char '-' *> pure Nothing) <|> (char '=' *> map Just natural))
  |]

covering
initSeq : Parser (List Step)
initSeq = many (step <* optional (char ',')) <* eos

covering
main : IO ()
main = do
    let eg = "rn=1,cm-,qp=3,cm=2,qp-,pc=4,ot=9,ab=5,pc-,pc=6,ot=7"

    let eg1 = split (== ',') eg

    Right input <- map (map trim) $ readFile "Day15/input"
        | Left err => printLn err

    let input1 = split (== ',') input

    putStrLn "Part 1"
    printLn $ map hash eg1
    printLn $ sum $ map hash input1

    let Right (eg2, _) = parse initSeq eg
        | Left err => putStrLn err

    let Right (input2, _) = parse initSeq input
        | Left err => putStrLn err

    putStrLn "Part 2"
    printLn $ run eg2
    printLn $ power $ run eg2
    printLn $ power $ run input2
