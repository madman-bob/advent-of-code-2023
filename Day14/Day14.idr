import Data.List1
import Data.Nat
import Data.SortedMap
import Data.String.Parse2D
import Deriving.Show
import System.File

%default total
%language ElabReflection

data Rock = RoundRock | CubeRock

Eq Rock where
    (==) = on (==) $ \case RoundRock => 0; CubeRock => 1

Ord Rock where
    compare = on compare $ \case RoundRock => 0; CubeRock => 1

%hint
showRock : Show Rock
showRock = %runElab derive

record Platform where
    constructor MkPlatform
    rocks : SortedMap Coord Rock
    height : Nat

Eq Platform where
    (==) = on (==) $ \p => (p.rocks, p.height)

Ord Platform where
    compare = on compare $ \p => (SortedMap.toList p.rocks, p.height)

Show Platform where
    show p = "MkPlatform (\{show p.rocks}) \{show p.height}"

load : Platform -> Nat
load p = foldl
    (\l => \case
        ((_, y), RoundRock) => l + minus p.height (cast y)
        (_, CubeRock) => l)
    0 $ SortedMap.toList p.rocks

tilt : Platform -> Platform
tilt p = {rocks := SortedMap.fromList $ concat $ map (snd . foldl
    (\(y', rs), ((x, y), r) => do
        let y = if r == CubeRock then y else y'
        (1 + y, ((x, y), r) :: rs))
    (0, [])) $
    groupBy (on (==) (fst . fst)) $ SortedMap.toList p.rocks} p

rotate : Platform -> Platform
rotate p = {rocks := SortedMap.fromList $
    map (\((x, y), r) => ((cast p.height - 1 - y, x), r)) $
    SortedMap.toList p.rocks} p

cycle : Platform -> Platform
cycle p =
    rotate $ tilt $
    rotate $ tilt $
    rotate $ tilt $
    rotate $ tilt p

covering
cycles : Nat ->
         Platform ->
         {default empty cache : SortedMap Platform Nat} ->
         Platform
cycles 0 p = p
cycles (S n) p = do
    let p' = cycle p
    case lookup p' cache of
        Nothing => do
            let cache = insert p' n cache
            cycles n p' {cache}
        Just m => do
            let n = assert_smaller n $ mod n (minus m n)
            cycles n p' {cache}

rock : Parse2D Rock
rock = object 'O' RoundRock <|> object '#' CubeRock

covering
platform : Parse2D Platform
platform = background '.' *> [| MkPlatform
    (map fromList $ some $ lexeme '.' [| (coord, rock) |])
    (map (cast . snd) coord)
  |] <* eos

covering
main : IO ()
main = do
    let eg = """
    O....#....
    O.OO#....#
    .....##...
    OO.#O....O
    .O.....O#.
    O.#..O.#.#
    ..O..#O..O
    .......O..
    #....###..
    #OO..#....

    """

    let Right (eg, _) = parse2d platform eg
        | Left err => putStrLn err

    Right input <- readFile "Day14/input"
        | Left err => printLn err

    let Right (input, _) = parse2d platform input
        | Left err => putStrLn err

    putStrLn "Part 1"
    printLn $ load $ tilt eg
    printLn $ load $ tilt input

    putStrLn "Part 2"
    --printLn $ load $ cycles 1_000_000_000 eg
    --printLn $ load $ cycles 1_000_000_000 input
