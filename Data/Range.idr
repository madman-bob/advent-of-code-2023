module Data.Range

import Deriving.Show

%language ElabReflection

%hide Prelude.Range

public export
record Range where
    constructor MkRange
    start : Nat
    len : Nat

%name Range r, s

public export
rangeFromTo : Nat -> Nat -> Range
rangeFromTo start end = MkRange start (minus end start)

public export
end : Range -> Nat
end r = r.start + r.len

public export
(.end) : Range -> Nat
(.end) = end

public export
Show Range where
    show r = "[\{show r.start}..\{show r.end}]"

public export
before : Range -> Nat -> Bool
before r n = n < r.start

beforeTests : map (before [1..2]) [0, 1] = [True, False]
beforeTests = Refl

public export
after : Range -> Nat -> Bool
after r n = n > r.end

afterTests : map (after [1..2]) [2, 3] = [False, True]
afterTests = Refl

public export
in_ : Range -> Nat -> Bool
in_ r n = r.start <= n && n <= r.end

inTests : map (in_ [1..2]) [0, 1, 2, 3] = [False, True, True, False]
inTests = Refl

public export
intersect : Range -> Range -> Maybe Range
intersect r s = if r.end < s.start || r.start > s.end
    then Nothing
    else Just $ if r.start <= s.start
        then intersect' r s
        else intersect' s r
  where
    intersect' : Range -> Range -> Range
    intersect' r s = MkRange s.start (min s.len (minus r.end s.start))

intersectTests : (
    intersect [1..2] [3..4] = Nothing,
    intersect [1..3] [2..4] = Just [2..3],
    intersect [1..4] [2..3] = Just [2..3],
    intersect [2..3] [1..4] = Just [2..3],
    intersect [2..4] [1..3] = Just [2..3],
    intersect [3..4] [1..2] = Nothing
  )
intersectTests = (Refl, Refl, Refl, Refl, Refl, Refl)

public export
diff : Range -> Range -> List Range
diff r s = do
    let before = if r.start < s.start
          then [MkRange r.start (min r.len $ minus s.start (S r.start))]
          else []
    let after = if r.end > s.end
          then do
              let start = max r.start $ S s.end
              [MkRange start (minus r.end start)]
          else []
    before ++ after

diffTests : (
    diff [1..2] [5..6] = [[1..2]],
    diff [1..3] [2..4] = [[1..1]],
    diff [1..6] [3..4] = [[1..2], [5..6]],
    diff [2..3] [1..4] = [],
    diff [2..4] [1..3] = [[4..4]],
    diff [5..6] [1..2] = [[5..6]]
  )
diffTests = (Refl, Refl, Refl, Refl, Refl, Refl)
