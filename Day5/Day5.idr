import Data.Nat
import Data.String.Parser
import Deriving.Show
import System.File

import Data.Range

%language ElabReflection

export
range : Parser Range
range = [| MkRange (lexeme natural) (map (`minus` 1) $ lexeme natural) |]

record MapRange where
    constructor MkMapRange
    destStart : Nat
    sourceRange : Range

%hint
showMapRange : Show MapRange
showMapRange = %runElab derive

mapRange : Parser MapRange
mapRange = [| MkMapRange (lexeme natural) (lexeme range) |]

Map : Type
Map = List MapRange

map : Parser Map
map = do
    ignore $ many letter *> string "-to-" *> many letter *> token " map:"
    many mapRange

namespace Part1
    applyMapRange : MapRange -> Nat -> Maybe Nat
    applyMapRange mr n = if in_ mr.sourceRange n
        then Just $ minus (n + mr.destStart) mr.sourceRange.start
        else Nothing

    applyMap : Map -> Nat -> Nat
    applyMap [] n = n
    applyMap (mr :: mrs) n = maybe (applyMap mrs n) id $ applyMapRange mr n

    export
    record Almanac where
        constructor MkAlmanac
        seeds : List Nat
        seed2soil : Map
        soil2fert : Map
        fert2water : Map
        water2light : Map
        light2temp : Map
        temp2humid : Map
        humid2loc : Map

    %hint
    export
    showAlmanac : Show Almanac
    showAlmanac = %runElab derive

    export
    locs : Almanac -> List Nat
    locs al = do
        let soils = map (applyMap al.seed2soil) al.seeds
        let ferts = map (applyMap al.soil2fert) soils
        let waters = map (applyMap al.fert2water) ferts
        let lights = map (applyMap al.water2light) waters
        let temps = map (applyMap al.light2temp) lights
        let humids = map (applyMap al.temp2humid) temps
        map (applyMap al.humid2loc) humids

    export
    almanac : Parser Almanac
    almanac = [| MkAlmanac (token "seeds:" *> many (lexeme natural)) map map map map map map map |] <* eos

namespace Part2
    applyMapRange : MapRange -> Range -> (Maybe Range, List Range)
    applyMapRange mr r = (
        map {start $= \s => minus (s + mr.destStart) mr.sourceRange.start} $ intersect r mr.sourceRange,
        diff r mr.sourceRange
      )

    applyMap : Map -> Range -> List Range
    applyMap [] r = pure r
    applyMap (mr :: mrs) r = do
        let (shifted, unshifted) = applyMapRange mr r
        maybe [] pure shifted ++ (unshifted >>= applyMap mrs)

    export
    record Almanac where
        constructor MkAlmanac
        seeds : List Range
        seed2soil : Map
        soil2fert : Map
        fert2water : Map
        water2light : Map
        light2temp : Map
        temp2humid : Map
        humid2loc : Map

    export
    locs : Part2.Almanac -> List Range
    locs al = do
        let soils = al.seeds >>= applyMap al.seed2soil
        let ferts = soils >>= applyMap al.soil2fert
        let waters = ferts >>= applyMap al.fert2water
        let lights = waters >>= applyMap al.water2light
        let temps = lights >>= applyMap al.light2temp
        let humids = temps >>= applyMap al.temp2humid
        humids >>= applyMap al.humid2loc

    export
    almanac : Parser Part2.Almanac
    almanac = [| MkAlmanac (token "seeds:" *> many range) map map map map map map map |] <* eos

minimum : List Nat -> Nat
minimum = foldr min 1_000_000_000

main : IO ()
main = do
    Right eg <- readFile "Day5/eg"
        | Left err => printLn err

    let Right (eg1, _) = parse Part1.almanac eg
        | Left err => putStrLn err

    Right input <- readFile "Day5/input"
        | Left err => printLn err

    let Right (input1, _) = parse Part1.almanac input
        | Left err => putStrLn err

    putStrLn "Part 1"
    printLn $ locs eg1
    printLn $ minimum $ locs input1

    let Right (eg2, _) = parse Part2.almanac eg
        | Left err => putStrLn err

    let Right (input2, _) = parse Part2.almanac input
        | Left err => putStrLn err

    putStrLn "Part 2"
    printLn $ minimum $ map start $ locs eg2
    printLn $ minimum $ map start $ locs input2
