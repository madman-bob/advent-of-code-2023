import Control.Monad.State
import Data.SortedMap
import Data.SortedSet
import Data.String.Parser
import Deriving.Show
import System.File

import Data.Range

%default total
%language ElabReflection

maximum : Foldable f => f Nat -> Nat
maximum ns = foldr max 0 ns

covering
reachable : Ord a => SortedMap a (List a) -> List a -> SortedSet a
reachable g start = reachable' (SortedSet.fromList start) empty
  where
    reachable' : SortedSet a -> SortedSet a -> SortedSet a
    reachable' open_ closed = if null open_
        then closed
        else do
            let closed = union open_ closed
            let open_ = SortedSet.fromList $ SortedSet.toList open_ >>= (\x => maybe [] id $ lookup x g)
            reachable' open_ closed

record Brick where
    constructor MkBrick
    label : Nat
    xRange : Range
    yRange : Range
    zRange : Range

collide : Brick -> Brick -> Bool
collide b c = isJust (intersect b.xRange c.xRange) && isJust (intersect b.yRange c.yRange)

supports : List Brick -> List (Nat, Nat)
supports bs = do
    let bs = sortBy (compare `on` (start . zRange)) bs
    let dropped : SnocList (Brick, List Nat) = foldl
          (\ds, b => do
            let hits = filter (collide b) $ map fst ds
            let topHit = maximum $ map (end . zRange) hits
            let support = filter (\b => b.zRange.end == topHit) hits
            ds :< ({zRange.start := S topHit} b, cast (map label support))
          )
          [<]
          bs
    (b, support) <- toList dropped
    map (, b.label) support

disintegrable : List Brick -> Nat
disintegrable bs = do
    let sups = supports bs
    let supportCounts : SortedMap Nat Nat = foldr
          (\(c, d) => update (Just . S . maybe 0 id) d)
          SortedMap.empty
          sups
    let supporteds : SortedMap Nat (List Nat) = foldr
          (\(c, d) => update (Just . (d ::) . maybe [] id) c)
          SortedMap.empty
          sups
    length $ filter (\b => do
        let children = maybe [] id $ lookup b.label supporteds
        all (\l => maybe 0 id (lookup l supportCounts) /= 1) children
      ) bs

covering
falling : List Brick -> Nat
falling bs = do
    let bCount = length bs
    let sups = supports bs

    let lifted : SortedSet Nat = foldr (\(c, d) => insert d) SortedSet.empty sups
    let grounded = filter (\l => not $ contains l lifted) $ map label bs

    let supporteds : SortedMap Nat (List Nat) = foldr
          (\(c, d) => update (Just . (d ::) . maybe [] id) c)
          SortedMap.empty
          sups

    sum $ map (minus bCount) $ map (\b => length $ SortedSet.toList $ reachable (delete b.label supporteds) grounded) bs

%hint
showBrick : Show Brick
showBrick = %runElab derive

covering
brick : ParseT (State Nat) Brick
brick = do
    (xStart, yStart, zStart) <- coord
    ignore $ char '~'
    (xEnd, yEnd, zEnd) <- coord
    pure $ MkBrick !newLabel (rangeBetween xStart xEnd) (rangeBetween yStart yEnd) (rangeBetween zStart zEnd)
  where
    newLabel : ParseT (State Nat) Nat
    newLabel = lift $ do
        l <- get
        modify S
        pure l

    coord : Monad m => ParseT m (Nat, Nat, Nat)
    coord = [| (natural <* char ',', [| (natural <* char ',', natural) |]) |]

    rangeBetween : Nat -> Nat -> Range
    rangeBetween start end = [min start end..max start end]

covering
bricks : ParseT (State Nat) (List Brick)
bricks = many (lexeme brick) <* eos

covering
main : IO ()
main = do
    let eg = """
    1,0,1~1,2,1
    0,0,2~2,0,2
    0,2,3~2,2,3
    0,0,4~0,2,4
    2,0,5~2,2,5
    0,1,6~2,1,6
    1,1,8~1,1,9
    """

    let Right (eg, _) = evalState 0 $ parseT bricks eg
        | Left err => putStrLn err

    Right input <- readFile "Day22/input"
            | Left err => printLn err

    let Right (input, _) = evalState 0 $ parseT bricks input
            | Left err => putStrLn err

    putStrLn "Part 1"
    printLn $ disintegrable eg
    printLn $ disintegrable input

    putStrLn "Part 2"
    printLn $ falling eg
    printLn $ falling input
