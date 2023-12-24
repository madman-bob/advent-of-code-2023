module Data.String.Parse2D

import public Data.String.Parser
import Deriving.Show

%default total
%language ElabReflection

namespace Direction
    public export
    data Direction = N | E | S | W

    %hint
    public export
    showDirection : Show Direction
    showDirection = %runElab derive

    public export
    Eq Direction where
        (==) = on (==) $ \case N => 0; E => 1; S => 2; W => 3

    public export
    Ord Direction where
        compare = on compare $ \case N => 0; E => 1; S => 2; W => 3

    public export
    complement : Direction -> Direction
    complement N = S
    complement E = W
    complement S = N
    complement W = E

namespace Coord
    public export
    Coord : Type
    Coord = (Integer, Integer)

    public export
    move : Direction -> Coord -> Coord
    move N (x, y) = (x, y - 1)
    move E (x, y) = (x + 1, y)
    move S (x, y) = (x, y + 1)
    move W (x, y) = (x - 1, y)

    public export
    moveN : Nat -> Direction -> Coord -> Coord
    moveN n N (x, y) = (x, y - cast n)
    moveN n E (x, y) = (x + cast n, y)
    moveN n S (x, y) = (x, y + cast n)
    moveN n W (x, y) = (x - cast n, y)

public export
Parse2D : Type -> Type
Parse2D = ParseT (State (Coord, Nat))

export
coord : Parse2D Coord
coord = map fst $ lift get

export
height : Parse2D Nat
height = map (\case
    (0, y) => cast y
    (x, y) => S (cast y)) coord

export
width : Parse2D Nat
width = map (\((x, y), w) => max (cast x) w) $ lift get

export
step : Parse2D ()
step = lift $ modify $ mapFst $ mapFst (1 +)

export
object : Char -> a -> Parse2D a
object c x = char c *> step *> pure x

export
newline : Parse2D ()
newline = char '\n' *>
    lift (modify $ \((x, y), w) => ((0, 1 + y), max (cast x) w))

export
covering
background : Char -> Parse2D ()
background c = ignore $ many b *> optional newline *> many (some b *> optional newline)
  where
    b : Parse2D ()
    b = object c ()

export
covering
lexeme : Char -> Parse2D a -> Parse2D a
lexeme c p = p <* background c

export
parse2d : Parse2D a -> String -> Either String (a, Int)
parse2d p str = evalState ((0, 0), 0) $ parseT p str
