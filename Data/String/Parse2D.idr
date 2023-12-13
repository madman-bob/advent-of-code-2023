module Data.String.Parse2D

import Data.String.Parser
import Deriving.Show

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
Parse2D : Type -> Type
Parse2D = ParseT (State Coord)

export
coord : Parse2D Coord
coord = lift get

export
object : Char -> a -> Parse2D a
object c x = char c *> lift (modify $ mapFst (1 +)) *> pure x

export
newline : Parse2D ()
newline = char '\n' *> lift (modify $ \(x, y) => (0, 1 + y))

export
background : Char -> Parse2D ()
background c = ignore $ many (object c () <|> newline)

export
lexeme : Char -> Parse2D a -> Parse2D a
lexeme c p = background c *> p

export
parse2d : Parse2D a -> String -> Either String (a, Int)
parse2d p str = evalState (0, 0) $ parseT p str
