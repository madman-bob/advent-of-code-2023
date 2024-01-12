import Data.List
import Data.Maybe
import Libraries.Data.SortedMap
import Data.SortedSet
import Data.String.Parser
import System.File

%default total

record Graph a where
    constructor MkGraph
    {auto ord : Ord a}
    edges : SortedMap a (List a)

%hint
gOrd : Graph a => Ord a
gOrd @{g} = g.ord

empty : Ord a => Graph a
empty = MkGraph empty

getEdges : Graph a -> a -> List a
getEdges g x = maybe [] id $ lookup x g.edges

addEdge : a -> a -> Graph a -> Graph a
addEdge x y = {edges $= add x y . add y x}
  where
    add : a -> a -> SortedMap a (List a) -> SortedMap a (List a)
    add x y es = insert x (y :: maybe [] id (lookup x es)) es

delEdge : a -> a -> Graph a -> Graph a
delEdge x y g = {edges $= del x y . del y x} g
  where
    del : a -> a -> SortedMap a (List a) -> SortedMap a (List a)
    del x y = adjust x (delete y)

fromEdges : Ord a => List (a, a) -> Graph a
fromEdges xs = foldr (uncurry addEdge) empty xs

findPath : Graph a -> a -> a -> Maybe (List a)
findPath g x y = do
    let f = flood (singleton x) empty
    assert_total $ readPath f y
  where
    flood : SortedSet a -> SortedMap a a -> SortedMap a a
    flood open_ closed = if null open_
        then closed
        else assert_total $ uncurry flood $ foldr
            (\x, s => foldr (\y, (open_, closed) => if isJust (lookup y closed)
                then (open_, closed)
                else (insert y open_, insert y x closed)) s $ getEdges g x)
            (empty, closed)
            open_

    covering
    readPath : SortedMap a a -> a -> {default [] acc : List a} -> Maybe (List a)
    readPath m z = if z == x
        then pure (z :: acc)
        else do
            w <- lookup z m
            readPath m w {acc = z :: acc}

delPath : List a -> Graph a -> Graph a
delPath [] g = g
delPath [x] g = g
delPath (x :: y :: xs) g = delPath (y :: xs) $ delEdge x y g

sameSide : Graph a -> a -> a -> Bool
sameSide g x y = if x == y
    then True
    else isJust $ do
        p1 <- findPath g x y
        let g = delPath p1 g
        p2 <- findPath g x y
        let g = delPath p2 g
        p3 <- findPath g x y
        let g = delPath p3 g
        findPath g x y

componentSizes : Graph a -> (Nat, Nat)
componentSizes g = do
    let Just ((x, _), _) = pop g.edges
        | Nothing => (0, 0)
    foldr (\y => if sameSide g x y then mapFst S else mapSnd S) (0, 0) $ keys g.edges

covering
diagram : Parser (Graph String)
diagram = map (fromEdges . concat) $ many $ do
    x <- word
    token ":"
    ys <- some (word <* optional (char ' '))
    ignore $ optional $ char '\n'
    pure $ map (x,) ys
  where
    word : Parser String
    word = map pack $ some letter

covering
main : IO ()
main = do
    let eg = """
    jqt: rhn xhk nvd
    rsh: frs pzl lsr
    xhk: hfx
    cmg: qnr nvd lhk bvb
    rhn: xhk bvb hfx
    bvb: xhk hfx
    pzl: lsr hfx nvd
    qnr: nvd
    ntq: jqt hfx bvb xhk
    nvd: lhk
    lsr: lhk
    rzs: qnr cmg lsr rsh
    frs: qnr lhk lsr
    """

    let Right (eg, _) = parse diagram eg
        | Left err => putStrLn err

    Right input <- readFile "Day25/input"
        | Left err => printLn err

    let Right (input, _) = parse diagram input
        | Left err => putStrLn err

    putStrLn "Part 1"
    let (n, m) = componentSizes eg
    printLn $ n * m
    let (n, m) = componentSizes input
    printLn $ n * m

    putStrLn "Part 2"
    putStrLn "Push the button!"
