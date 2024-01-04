import Data.SortedMap
import Data.String.Parser
import Deriving.Show
import System.File

import Data.Range

%default total
%language ElabReflection

data Category = X | M | A | S

%hint
showCategory : Show Category
showCategory = %runElab derive

public export
record Rule where
    constructor MkRule
    category : Category
    ord : Ordering
    threshold : Nat
    destination : Either Bool String

%hint
showRule : Show Rule
showRule = %runElab derive

record Workflow where
    constructor MkWorkflow
    name : String
    rules : List Rule
    finalDest : Either Bool String

%hint
showWorkflow : Show Workflow
showWorkflow = %runElab derive

namespace Part1
    public export
    record Part where
        constructor MkPart
        x : Nat
        m : Nat
        a : Nat
        s : Nat

    val : Category -> Part -> Nat
    val X = x
    val M = m
    val A = a
    val S = s

    export
    rating : Part -> Nat
    rating p = p.x + p.m + p.a + p.s

    %hint
    showPart : Show Part
    showPart = %runElab derive

    applyRule : Rule -> Part -> Maybe (Either Bool String)
    applyRule rl p = if compare (val rl.category p) rl.threshold == rl.ord
        then Just rl.destination
        else Nothing

    applyWorkflow : Workflow -> Part -> Either Bool String
    applyWorkflow w p =
        maybe w.finalDest id $
        foldl
            (\case
                Nothing => \rl => applyRule rl p
                Just d => const $ Just d)
            Nothing
            w.rules

    covering
    export
    applyInstructions : SortedMap String Workflow ->
                        {default "in" start : String} ->
                        Part ->
                        Bool
    applyInstructions ws p = do
        let Just w = lookup start ws
            | Nothing => False
        case applyWorkflow w p of
            Left accept => accept
            Right name => applyInstructions ws {start = name} p

namespace Part2
    export
    record PartRange where
        constructor MkPartRange
        xs : Range
        ms : Range
        as : Range
        ss : Range

    %hint
    export
    showPR : Show PartRange
    showPR = %runElab derive

    val : Category -> PartRange -> Range
    val X = xs
    val M = ms
    val A = as
    val S = ss

    setVal : Category -> Range -> PartRange -> PartRange
    setVal X r = {xs := r}
    setVal M r = {ms := r}
    setVal A r = {as := r}
    setVal S r = {ss := r}

    export
    size : PartRange -> Nat
    size pr = (S $ len pr.xs) * (S $ len pr.ms) * (S $ len pr.as) * (S $ len pr.ss)

    export
    fullRange : PartRange
    fullRange = MkPartRange [1..4000] [1..4000] [1..4000] [1..4000]

    rangeApplyRule : Rule -> PartRange -> List (PartRange, Maybe (Either Bool String))
    rangeApplyRule rl pr = do
        let acceptRange : Range = case rl.ord of
              LT => [1 .. minus rl.threshold 1]
              EQ => [rl.threshold .. rl.threshold]
              GT => [S rl.threshold .. 4000]
        let acceptPartRange : Maybe PartRange = map setVal' $ intersect val' acceptRange
        let failPartRange : List PartRange = map setVal' $ diff val' acceptRange
        maybe [] (pure . (, Just rl.destination)) acceptPartRange ++ map (, Nothing) failPartRange
      where
        val' : Range
        val' = val rl.category pr

        setVal' : Range -> PartRange
        setVal' r = setVal rl.category r pr

    rangeApplyWorkflow : Workflow -> PartRange -> List (PartRange, Either Bool String)
    rangeApplyWorkflow w prStart =
        map (map $ maybe w.finalDest id) $ foldl
            (\ds, r => case !ds of
                (pr, Nothing) => rangeApplyRule r pr
                (pr, Just d) => pure (pr, Just d))
            [(prStart, Nothing)]
            w.rules

    covering
    export
    rangeApplyInstructions : SortedMap String Workflow ->
                             {default "in" start : String} ->
                             PartRange ->
                             List PartRange
    rangeApplyInstructions ws prStart = do
        let Just w = lookup start ws
            | Nothing => []
        case !(rangeApplyWorkflow w prStart) of
            (pr, Left False) => []
            (pr, Left True) => pure pr
            (pr, Right name) => rangeApplyInstructions ws {start = name} pr

covering
destination : Parser (Either Bool String)
destination =
    (char 'R' *> pure (Left False)) <|> (char 'A' *> pure (Left True)) <|>
    (map (Right . pack) $ many letter)

covering
rule : Parser Rule
rule = [| MkRule
    ((char 'x' *> pure X) <|> (char 'm' *> pure M) <|> (char 'a' *> pure A) <|> (char 's' *> pure S))
    ((char '<' *> pure LT) <|> (char '>' *> pure GT))
    natural
    (char ':' *> destination)
  |]

covering
workflow : Parser Workflow
workflow = [| MkWorkflow
    (map pack $ many letter)
    (char '{' *> (many $ rule <* char ','))
    (destination <* char '}')
  |]

covering
workflows : Parser (SortedMap String Workflow)
workflows = map (\ws => SortedMap.fromList $ map (\w => (w.name, w)) ws) $ many $ lexeme workflow

covering
part : Parser Part
part = lexeme [| MkPart
    (string "{x=" *> natural)
    (string ",m=" *> natural)
    (string ",a=" *> natural)
    (string ",s=" *> natural <* char '}')
  |]

covering
instructions : Parser (SortedMap String Workflow, List Part)
instructions = [| (workflows, many part) |] <* eos

covering
main : IO ()
main = do
    let eg = """
    px{a<2006:qkq,m>2090:A,rfg}
    pv{a>1716:R,A}
    lnx{m>1548:A,A}
    rfg{s<537:gd,x>2440:R,A}
    qs{s>3448:A,lnx}
    qkq{x<1416:A,crn}
    crn{x>2662:A,R}
    in{s<1351:px,qqz}
    qqz{s>2770:qs,m<1801:hdj,R}
    gd{a>3333:R,R}
    hdj{m>838:A,pv}

    {x=787,m=2655,a=1222,s=2876}
    {x=1679,m=44,a=2067,s=496}
    {x=2036,m=264,a=79,s=2244}
    {x=2461,m=1339,a=466,s=291}
    {x=2127,m=1623,a=2188,s=1013}
    """

    let Right ((egWs, egParts), _) = parse instructions eg
        | Left err => putStrLn err

    Right input <- readFile "Day19/input"
        | Left err => printLn err

    let Right ((inputWs, inputParts), _) = parse instructions input
        | Left err => putStrLn err

    putStrLn "Part 1"
    printLn $ sum $ map rating $ filter (applyInstructions egWs) egParts
    printLn $ sum $ map rating $ filter (applyInstructions inputWs) inputParts

    putStrLn "Part 2"
    printLn $ sum $ map size $ rangeApplyInstructions egWs fullRange
    printLn $ sum $ map size $ rangeApplyInstructions inputWs fullRange
