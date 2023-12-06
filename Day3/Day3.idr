import Control.Monad.State
import Data.String.Parser
import Deriving.Show
import System.File

%language ElabReflection

||| A potential part number
|||
||| A symbol touches the number when they are on adjacent/the same rows, and
||| start <= S pos && pos <= S end
record PPN where
    constructor MkPPN
    start : Nat
    end : Nat
    val : Nat

%hint
showPPN : Show PPN
showPPN = %runElab derive

||| A symbol
|||
||| For *s, we also store the values of adjacent numbers
record Sym where
    constructor MkSym
    pos : Nat
    adjNums : Maybe (SnocList Nat)

%hint
showSym : Show Sym
showSym = %runElab derive

ratios : List Sym -> List Nat
ratios ss = mapMaybe id $ flip map (mapMaybe adjNums ss) $ \case
    [<n, m] => Just $ n * m
    _ => Nothing

record S where
    constructor MkS
    partNums : SnocList Nat
    gearRatios : SnocList Nat
    prevLineNums : List PPN
    prevLineSyms : List Sym
    curLineNums : SnocList PPN
    curLineSyms : SnocList Sym
    col : Nat

%hint
showS : Show S
showS = %runElab derive

afterSym : PPN -> State S Bool
afterSym n = case curLineSyms !get of
    ss :< s => if n.start == S s.pos
        then do
            modify {curLineSyms := ss :< {adjNums $= map (:< n.val)} s}
            pure True
        else pure False
    [<] => pure False

belowSym : PPN -> State S Bool
belowSym n = do
    let syms = takeWhile (\s => n.start > S s.pos) (prevLineSyms !get)
    modify {prevLineSyms $= dropWhile $ \s => n.start > S s.pos}
    modify {gearRatios $= (<>< ratios syms)}
    case prevLineSyms !get of
        s :: ss => if s.pos <= S n.end
            then do
                modify {prevLineSyms := {adjNums $= map (:< n.val)} s :: ss}
                pure True
            else pure False
        [] => pure False

addNum : PPN -> State S ()
addNum n = do
    if !(afterSym n) || !(belowSym n)
       then modify {partNums $= (:< n.val)}
       else modify {curLineNums $= (:< n)}

afterNum : Sym -> State S (List Nat)
afterNum s = case curLineNums !get of
    ns :< n => if s.pos == S n.end
        then do
            modify {curLineNums := ns}
            modify {partNums $= (:< n.val)}
            pure [n.val]
        else
            pure []
    [<] => pure []

belowNums : Sym -> State S (List Nat)
belowNums s = do
    modify {prevLineNums $= dropWhile $ \m => s.pos > S m.end}
    nums <- map ((map val) . takeWhile (\m => m.start <= S s.pos) . prevLineNums) get
    modify {partNums $= (<>< nums)}
    modify {prevLineNums $= dropWhile $ \m => m.start <= S s.pos}
    pure nums

addSym : Sym -> State S ()
addSym s = do
    nums1 <- afterNum s
    nums2 <- belowNums s
    let s = {adjNums $= map (<>< (nums1 ++ nums2))} s
    modify {curLineSyms $= (:< s)}

withWidth : Parser a -> ParseT (State S) a
withWidth (P p) = P $ \s1 => do
    case runIdentity $ p s1 of
        f@(Fail _ _) => pure f
        ok@(OK _ s2) => do
            modify {col $= (+) $ cast $ s2.pos - s1.pos}
            pure ok

ppn : ParseT (State S) ()
ppn = do
    let start = col !(lift get)
    val <- withWidth natural
    let end = minus (col !(lift get)) 1
    lift $ addNum $ MkPPN start end val

space : ParseT (State S) ()
space = ignore $ withWidth $ char '.'

sym : ParseT (State S) ()
sym = do
    let n = col !(lift get)
    c <- withWidth $ satisfy (/= '\n')
    lift $ addSym $ MkSym n $ if c == '*'
        then Just [<]
        else Nothing

newline : ParseT (State S) ()
newline = do
    ignore $ char '\n'
    lift $ modify $ \s => MkS
        s.partNums
        (s.gearRatios <>< ratios s.prevLineSyms)
        (cast s.curLineNums)
        (cast s.curLineSyms)
        [<]
        [<]
        0

schematic : ParseT (State S) ()
schematic = many (many (ppn <|> space <|> sym) *> newline) *> eos

parseSchematic : String -> Either String (SnocList Nat, SnocList Nat)
parseSchematic str = do
  let (s, res) = runState (MkS [<] [<] [] [] [<] [<] 0) $ parseT schematic (str ++ "\n")
  map (const (s.partNums, s.gearRatios)) res

main : IO ()
main = do
    let eg = """
    467..114..
    ...*......
    ..35..633.
    ......#...
    617*......
    .....+.58.
    ..592.....
    ......755.
    ...$.*....
    .664.598..

    """

    Right input <- readFile "Day3/input"
        | Left err => printLn err

    printLn $ parseSchematic eg
    printLn $ map (\(nums, ratios) => (sum nums, sum ratios)) $ parseSchematic input
