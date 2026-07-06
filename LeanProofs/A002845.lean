import Std.Data.HashSet.Basic

/-!
# Initial values of OEIS A002845

OEIS A002845 counts the distinct values taken by `2^2^...^2`, with `n`
copies of `2` and all binary parenthesizations allowed.

Every such value is a power of two.  This module therefore works with exact
base-two logarithms: the leaf `2` has logarithm `1`, and combining two
subexpressions with logarithms `a` and `b` gives logarithm `a * 2^b`.

The logarithms quickly exceed ordinary big-integer scale, so the executable
certificate below represents nonnegative integers in hereditary sparse binary
form: a number is the finite set of positions of `1` bits, and those positions
are represented the same way.
-/

set_option maxRecDepth 100000

namespace LeanProofs

namespace A002845

/-- A hereditary sparse binary nonnegative integer.

`bits xs` represents `sum (x in xs), 2^x`, with the executable operations below
maintaining `xs` in increasing numeric order and without duplicates.
-/
inductive Sparse where
  | bits : List Sparse → Sparse
deriving Repr, Inhabited

namespace Sparse

/-- Structural equality for sparse-binary trees.  The arithmetic operations
maintain canonical bit lists, so structural equality is numeric equality for
the values produced here. -/
partial def beq : Sparse → Sparse → Bool
  | .bits xs, .bits ys => beqList xs ys
where
  beqList : List Sparse → List Sparse → Bool
    | [], [] => true
    | x :: xs, y :: ys => beq x y && beqList xs ys
    | _, _ => false

instance : BEq Sparse where
  beq := beq

/-- Structural hash matching `Sparse.beq`. -/
partial def hash : Sparse → UInt64
  | .bits xs => mixHash 17 (hashList xs)
where
  hashList : List Sparse → UInt64
    | [] => 19
    | x :: xs => mixHash (hash x) (hashList xs)

instance : Hashable Sparse where
  hash := hash

/-- Zero in hereditary sparse binary. -/
def zero : Sparse :=
  .bits []

/-- One in hereditary sparse binary. -/
def one : Sparse :=
  .bits [zero]

/-- Numeric comparison of canonical sparse-binary values. -/
partial def compare : Sparse → Sparse → Ordering
  | .bits xs, .bits ys => compareDescending xs.reverse ys.reverse
where
  /-- Compare bit-position lists written from high to low. -/
  compareDescending : List Sparse → List Sparse → Ordering
    | [], [] => .eq
    | [], _ :: _ => .lt
    | _ :: _, [] => .gt
    | x :: xs, y :: ys =>
        match compare x y with
        | .eq => compareDescending xs ys
        | order => order

/-- Add two hereditary sparse binary nonnegative integers. -/
partial def add : Sparse → Sparse → Sparse
  | .bits xs, .bits ys => .bits (ys.foldl (fun acc p => insertBit p acc) xs)
where
  /-- Insert one set bit into a canonical sparse-binary bit list, carrying on
  collision. -/
  insertBit (p : Sparse) : List Sparse → List Sparse
    | [] => [p]
    | q :: qs =>
        match compare p q with
        | .lt => p :: q :: qs
        | .eq => insertBit (add p one) qs
        | .gt => q :: insertBit p qs

/-- Insert one set bit into a canonical bit list. -/
def insertSingletonBit (p : Sparse) (xs : List Sparse) : List Sparse :=
  match add (.bits xs) (.bits [p]) with
  | .bits ys => ys

/-- Multiply by `2^b`, i.e. shift all bit positions upward by `b`. -/
partial def shift (x b : Sparse) : Sparse :=
  match x with
  | .bits xs =>
      .bits (xs.foldl (fun acc p => insertSingletonBit (add p b) acc) [])

end Sparse

/-- Remove duplicates from a list of sparse values. -/
def dedup (xs : List Sparse) : List Sparse :=
  (Std.HashSet.ofList xs).toList

/-- The exact logarithm-combine operation:
`log₂ ((2^a)^(2^b)) = a * 2^b`. -/
def combineLog (a b : Sparse) : Sparse :=
  Sparse.shift a b

/-- Raw values produced by one binary split of an expression of size `n`. -/
partial def splitValues (levels : Array (List Sparse)) (leftSize rightSize : Nat) :
    List Sparse :=
  let left := levels[leftSize - 1]!
  let right := levels[rightSize - 1]!
  List.flatten (List.map (fun a => List.map (fun b => combineLog a b) right) left)

/-- Compute all distinct logarithms for expressions of a given positive size,
assuming all smaller levels have already been computed. -/
partial def nextLevel (levels : Array (List Sparse)) : List Sparse :=
  let size := levels.size + 1
  if size = 1 then
    [Sparse.one]
  else
    let raw :=
      List.flatten (List.map (fun k =>
        splitValues levels (k + 1) (size - 1 - k)) (List.range (size - 1)))
    dedup raw

/-- Build the table of distinct logarithm lists through size `fuel`. -/
partial def buildLevels : Nat → Array (List Sparse) → Array (List Sparse)
  | 0, levels => levels
  | fuel + 1, levels =>
      buildLevels fuel (levels.push (nextLevel levels))

/-- The distinct base-two logarithms of the values counted by A002845. -/
def a002845LogValues (n : Nat) : List Sparse :=
  if n = 0 then
    []
  else
    (buildLevels n #[])[n - 1]!

/-- OEIS A002845, computed from exact hereditary sparse-binary logarithms. -/
def a002845 (n : Nat) : Nat :=
  (a002845LogValues n).length

/-- `A002845(1) = 1`. -/
theorem a002845_one : a002845 1 = 1 := by
  native_decide

/-- `A002845(2) = 1`. -/
theorem a002845_two : a002845 2 = 1 := by
  native_decide

/-- `A002845(3) = 1`. -/
theorem a002845_three : a002845 3 = 1 := by
  native_decide

/-- `A002845(4) = 2`. -/
theorem a002845_four : a002845 4 = 2 := by
  native_decide

/-- `A002845(5) = 4`. -/
theorem a002845_five : a002845 5 = 4 := by
  native_decide

/-- `A002845(6) = 8`. -/
theorem a002845_six : a002845 6 = 8 := by
  native_decide

/-- `A002845(7) = 17`. -/
theorem a002845_seven : a002845 7 = 17 := by
  native_decide

/-- `A002845(8) = 36`. -/
theorem a002845_eight : a002845 8 = 36 := by
  native_decide

/-- `A002845(9) = 78`. -/
theorem a002845_nine : a002845 9 = 78 := by
  native_decide

/-- `A002845(10) = 171`. -/
theorem a002845_ten : a002845 10 = 171 := by
  native_decide

/-- `A002845(11) = 379`. -/
theorem a002845_eleven : a002845 11 = 379 := by
  native_decide

/-- `A002845(12) = 851`. -/
theorem a002845_twelve : a002845 12 = 851 := by
  native_decide

/-- `A002845(13) = 1928`. -/
theorem a002845_thirteen : a002845 13 = 1928 := by
  native_decide

/-- `A002845(14) = 4396`. -/
theorem a002845_fourteen : a002845 14 = 4396 := by
  native_decide

/-- `A002845(15) = 10087`. -/
theorem a002845_fifteen : a002845 15 = 10087 := by
  native_decide

/-- `A002845(16) = 23273`. -/
theorem a002845_sixteen : a002845 16 = 23273 := by
  native_decide

/-- `A002845(17) = 53948`. -/
theorem a002845_seventeen : a002845 17 = 53948 := by
  native_decide

/-- `A002845(18) = 125608`. -/
theorem a002845_eighteen : a002845 18 = 125608 := by
  native_decide

end A002845

end LeanProofs
