import LeanProofs.PowTower
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.NAry
import Mathlib.SetTheory.Ordinal.Notation
import Std.Data.HashSet.Lemmas

/-!
# Initial values of OEIS A199812

OEIS A199812 counts the distinct ordinals represented by all binary
parenthesizations of `omega^omega^...^omega`.

The primary definition in this module is the shared lexical syntax
`PowTower.Expr`, interpreted by ordinary ordinal exponentiation, with the
single atom interpreted as the first infinite ordinal `omega`.

For computation, a second representation records the exponent `e` in the
principal ordinal power `omega^e`, using mathlib's verified `ONote` normal
forms below `epsilon_0`.  The theorem `a199812_eq_noteCount` proves that this
normal-form computation has exactly the same cardinality as the canonical
ordinal definition.
-/

set_option maxRecDepth 100000

namespace LeanProofs

namespace A199812

open Ordinal

namespace TowerExpr

open PowTower.Expr

instance : BEq ONote where
  beq a b := decide (a = b)

instance : LawfulBEq ONote where
  rfl := by
    intro a
    simp [BEq.beq]
  eq_of_beq := by
    intro a b h
    simpa [BEq.beq] using h

instance : EquivBEq ONote where
  symm := by
    intro a b h
    have hab : a = b := LawfulBEq.eq_of_beq h
    subst hab
    simp [BEq.beq]
  trans := by
    intro a b c hab hbc
    have hab' : a = b := LawfulBEq.eq_of_beq hab
    have hbc' : b = c := LawfulBEq.eq_of_beq hbc
    subst hab'
    subst hbc'
    simp [BEq.beq]
  rfl := by
    intro a
    simp [BEq.beq]

partial def onoteHash : ONote -> UInt64
  | 0 => 17
  | ONote.oadd e n a => mixHash (mixHash (onoteHash e) (hash (n : Nat))) (onoteHash a)

instance : Hashable ONote where
  hash := onoteHash

instance : LawfulHashable ONote where
  hash_eq := by
    intro a b h
    have hab : a = b := LawfulBEq.eq_of_beq h
    subst hab
    rfl

/-- Shared lexical interpretation for A199812: atom is `omega`, node is ordinal power. -/
noncomputable abbrev sharedEvalOrdinal : PowTower.Expr -> Ordinal.{0} :=
  PowTower.Expr.eval (ω : Ordinal.{0}) (fun a b : Ordinal.{0} => a ^ b)

/-- The shared canonical lexical value set for A199812. -/
noncomputable def canonicalOrdinalValueSet (n : Nat) : Set Ordinal.{0} :=
  PowTower.Expr.valueSet (ω : Ordinal.{0}) (fun a b : Ordinal.{0} => a ^ b) n

theorem canonicalOrdinalValueSet_eq_evalSet (n : Nat) :
    canonicalOrdinalValueSet n = PowTower.Expr.evalSet sharedEvalOrdinal n := by
  exact PowTower.Expr.valueSet_eq_evalSet
    (ω : Ordinal.{0}) (fun a b : Ordinal.{0} => a ^ b) n

/--
The canonical finite set of ordinal values for `n` copies of `omega`.

This finite view is proved equivalent to the shared lexical set and exists only
to connect the canonical definition to executable finite computations.
-/
noncomputable def ordinalValues (n : Nat) : Finset Ordinal.{0} := by
  classical
  exact PowTower.Expr.evalFinset sharedEvalOrdinal n

/-- OEIS A199812, from the shared lexical ordinal interpretation. -/
noncomputable def a199812 (n : Nat) : Nat :=
  PowTower.Expr.valueCard (ω : Ordinal.{0}) (fun a b : Ordinal.{0} => a ^ b) n

theorem a199812_eq_recursiveValueSet_ncard (n : Nat) :
    a199812 n =
      (PowTower.Expr.recursiveValueSet (ω : Ordinal.{0})
        (fun a b : Ordinal.{0} => a ^ b) n).ncard := by
  exact PowTower.Expr.valueCard_eq_recursiveValueSet_ncard
    (ω : Ordinal.{0}) (fun a b : Ordinal.{0} => a ^ b) n

theorem canonicalOrdinalValueSet_eq_ordinalValues (n : Nat) :
    canonicalOrdinalValueSet n = (ordinalValues n : Set Ordinal.{0}) := by
  classical
  rw [canonicalOrdinalValueSet_eq_evalSet]
  exact PowTower.Expr.evalSet_eq_evalFinset sharedEvalOrdinal n

theorem a199812_eq_ordinalValues_card (n : Nat) :
    a199812 n = (ordinalValues n).card := by
  simpa [a199812, ordinalValues, sharedEvalOrdinal] using
    (PowTower.Expr.valueCard_eq_evalFinset_card
      (ω : Ordinal.{0}) (fun a b : Ordinal.{0} => a ^ b) n)

/-- The principal ordinal power `omega^e`, represented as an `ONote`. -/
def principalPower (e : ONote) : ONote :=
  ONote.oadd e (1 : ℕ+) 0

/-- The exponent-combine operation forced by `(omega^a)^(omega^b) = omega^(a * omega^b)`. -/
def combineExponent (a b : ONote) : ONote :=
  a * principalPower b

/-- The `ONote` exponent `e` such that the shared expression evaluates to `omega^e`. -/
def exponentNote : PowTower.Expr -> ONote
  | atom => 1
  | pow a b => combineExponent (exponentNote a) (exponentNote b)

instance principalPower_nf (e : ONote) [ONote.NF e] : ONote.NF (principalPower e) := by
  dsimp [principalPower]
  infer_instance

/-- Every computed exponent note is in Cantor normal form. -/
theorem exponentNote_nf : ∀ e : PowTower.Expr, ONote.NF (exponentNote e)
  | atom => by
      simpa [exponentNote] using (inferInstance : ONote.NF (1 : ONote))
  | pow a b => by
      haveI := exponentNote_nf a
      haveI := exponentNote_nf b
      dsimp [exponentNote, combineExponent]
      infer_instance

theorem exponentNote_eq_sharedEval (e : PowTower.Expr) :
    exponentNote e = PowTower.Expr.eval (1 : ONote) combineExponent e := by
  induction e with
  | atom =>
      rfl
  | pow a b iha ihb =>
      simp [exponentNote, PowTower.Expr.eval, iha, ihb]

@[simp]
theorem repr_principalPower (e : ONote) [ONote.NF e] :
    ONote.repr (principalPower e) = (ω : Ordinal) ^ ONote.repr e := by
  simp [principalPower, ONote.repr]

theorem repr_combineExponent (a b : ONote) [ONote.NF a] [ONote.NF b] :
    ONote.repr (combineExponent a b) =
      ONote.repr a * (ω : Ordinal) ^ ONote.repr b := by
  haveI : ONote.NF (principalPower b) := principalPower_nf b
  simp [combineExponent, ONote.repr_mul]

/--
The normal-form exponent computation is sound for the canonical ordinal
interpretation.
-/
theorem sharedEvalOrdinal_eq_omega_opow_exponentNote (e : PowTower.Expr) :
    sharedEvalOrdinal e = (ω : Ordinal) ^ ONote.repr (exponentNote e) := by
  induction e with
  | atom =>
      simp [sharedEvalOrdinal, exponentNote, ONote.repr_one, Ordinal.opow_one]
  | pow a b iha ihb =>
      haveI := exponentNote_nf a
      haveI := exponentNote_nf b
      calc
        sharedEvalOrdinal (pow a b)
            = sharedEvalOrdinal a ^ sharedEvalOrdinal b := rfl
        _ = ((ω : Ordinal) ^ ONote.repr (exponentNote a)) ^
              ((ω : Ordinal) ^ ONote.repr (exponentNote b)) := by
                rw [iha, ihb]
        _ = (ω : Ordinal) ^
              (ONote.repr (exponentNote a) *
                ((ω : Ordinal) ^ ONote.repr (exponentNote b))) := by
                  rw [← Ordinal.opow_mul]
        _ = (ω : Ordinal) ^ ONote.repr (exponentNote (pow a b)) := by
                  simp [exponentNote, repr_combineExponent]

/-- The list of verified normal-form exponents for the same parenthesized expressions. -/
def exponentNoteList (n : Nat) : List ONote :=
  (PowTower.Expr.parenthesizations n).map exponentNote

/-- The finite set of verified normal-form exponents for the same parenthesized expressions. -/
def exponentNoteValues (n : Nat) : Finset ONote :=
  (exponentNoteList n).toFinset

/--
The normal-form exponent values are the shared lexical finite value set for the
normal-form exponent evaluator.
-/
theorem exponentNoteValues_eq_evalFinset (n : Nat) :
    exponentNoteValues n = PowTower.Expr.evalFinset exponentNote n := by
  simp [exponentNoteValues, exponentNoteList, PowTower.Expr.evalFinset]

theorem exponentNoteValues_eq_recursiveValueFinset (n : Nat) :
    exponentNoteValues n =
      PowTower.Expr.recursiveValueFinset (1 : ONote) combineExponent n := by
  rw [exponentNoteValues_eq_evalFinset]
  exact PowTower.Expr.evalFinset_eq_recursiveValueFinset_of_eval_eq
    exponentNote (1 : ONote) combineExponent exponentNote_eq_sharedEval n

/-- The direct normal-form count obtained from all lexical parenthesizations. -/
def exponentNoteCount (n : Nat) : Nat :=
  (exponentNoteValues n).card

/-- Interpret a normal-form exponent note as the principal ordinal power it denotes. -/
noncomputable def ordinalOfNote (o : ONote) : Ordinal.{0} :=
  (ω : Ordinal) ^ ONote.repr o

theorem ordinalValues_eq_exponentNoteValues_image (n : Nat) :
    ordinalValues n = (exponentNoteValues n).image ordinalOfNote := by
  classical
  rw [exponentNoteValues_eq_evalFinset]
  simpa [ordinalValues, ordinalOfNote] using
    (PowTower.Expr.evalFinset_eq_image_evalFinset_of_eval_eq
      sharedEvalOrdinal exponentNote ordinalOfNote
      sharedEvalOrdinal_eq_omega_opow_exponentNote n)

theorem exponentNoteValues_nf {n : Nat} {o : ONote} (ho : o ∈ exponentNoteValues n) :
    ONote.NF o := by
  rw [exponentNoteValues, exponentNoteList] at ho
  simp only [List.mem_toFinset, List.mem_map] at ho
  rcases ho with ⟨e, _he, rfl⟩
  exact exponentNote_nf e

theorem ordinalOfNote_injOn_exponentNoteValues (n : Nat) :
    Set.InjOn ordinalOfNote (exponentNoteValues n : Set ONote) := by
  intro a ha b hb h
  haveI : ONote.NF a := exponentNoteValues_nf ha
  haveI : ONote.NF b := exponentNoteValues_nf hb
  apply ONote.repr_inj.mp
  exact (Ordinal.opow_right_inj one_lt_omega0).mp h

/--
The executable normal-form count is equivalent to the canonical ordinal count.
-/
theorem a199812_eq_noteCount (n : Nat) : a199812 n = exponentNoteCount n := by
  classical
  rw [a199812_eq_ordinalValues_card, ordinalValues_eq_exponentNoteValues_image, exponentNoteCount]
  exact Finset.card_image_of_injOn (ordinalOfNote_injOn_exponentNoteValues n)

/-- The inner exponent `d` such that `exponentNote e = omega^d` as an `ONote`. -/
def degreeNote : PowTower.Expr -> ONote
  | atom => 0
  | pow a b => degreeNote a + principalPower (degreeNote b)

theorem degreeNote_nf : ∀ e : PowTower.Expr, ONote.NF (degreeNote e)
  | atom => by
      simpa [degreeNote] using (inferInstance : ONote.NF (0 : ONote))
  | pow a b => by
      haveI := degreeNote_nf a
      haveI := degreeNote_nf b
      dsimp [degreeNote]
      infer_instance

theorem degreeNote_eq_sharedEval (e : PowTower.Expr) :
    degreeNote e = PowTower.Expr.eval (0 : ONote)
      (fun a b : ONote => a + principalPower b) e := by
  induction e with
  | atom =>
      rfl
  | pow a b iha ihb =>
      simp [degreeNote, PowTower.Expr.eval, iha, ihb]

theorem combineExponent_principalPower (a b : ONote) [ONote.NF a] [ONote.NF b] :
    combineExponent (principalPower a) (principalPower b) =
      principalPower (a + principalPower b) := by
  haveI : ONote.NF (principalPower a) := principalPower_nf a
  haveI : ONote.NF (principalPower b) := principalPower_nf b
  haveI : ONote.NF (principalPower (principalPower b)) := principalPower_nf (principalPower b)
  have hleft : ONote.NF (combineExponent (principalPower a) (principalPower b)) := by
    dsimp [combineExponent]
    infer_instance
  have hright : ONote.NF (principalPower (a + principalPower b)) := by
    infer_instance
  haveI := hleft
  haveI := hright
  apply ONote.repr_inj.mp
  simp [combineExponent, principalPower, ONote.repr_mul, ONote.repr_add, Ordinal.opow_add]

/-- The exponent normal form is always a principal power of `degreeNote`. -/
theorem exponentNote_eq_principalPower_degreeNote (e : PowTower.Expr) :
    exponentNote e = principalPower (degreeNote e) := by
  induction e with
  | atom =>
      rfl
  | pow a b iha ihb =>
      rw [exponentNote, iha, ihb]
      haveI := degreeNote_nf a
      haveI := degreeNote_nf b
      rw [combineExponent_principalPower]
      rfl

/-- The list of verified inner exponents for the same parenthesized expressions. -/
def degreeNoteList (n : Nat) : List ONote :=
  (PowTower.Expr.parenthesizations n).map degreeNote

/-- The finite set of verified inner exponents for the same parenthesized expressions. -/
def degreeNoteValues (n : Nat) : Finset ONote :=
  (degreeNoteList n).toFinset

/--
The inner-exponent values are the shared lexical finite value set for the
inner-exponent evaluator.
-/
theorem degreeNoteValues_eq_evalFinset (n : Nat) :
    degreeNoteValues n = PowTower.Expr.evalFinset degreeNote n := by
  simp [degreeNoteValues, degreeNoteList, PowTower.Expr.evalFinset]

/-- Count the verified inner exponents. -/
def degreeNoteCount (n : Nat) : Nat :=
  (degreeNoteValues n).card

theorem exponentNoteValues_eq_degreeNoteValues_image (n : Nat) :
    exponentNoteValues n = (degreeNoteValues n).image principalPower := by
  ext o
  simp [exponentNoteValues, exponentNoteList, degreeNoteValues, degreeNoteList,
    exponentNote_eq_principalPower_degreeNote]

theorem degreeNoteValues_nf {n : Nat} {o : ONote} (ho : o ∈ degreeNoteValues n) :
    ONote.NF o := by
  rw [degreeNoteValues, degreeNoteList] at ho
  simp only [List.mem_toFinset, List.mem_map] at ho
  rcases ho with ⟨e, _he, rfl⟩
  exact degreeNote_nf e

theorem principalPower_injOn_degreeNoteValues (n : Nat) :
    Set.InjOn principalPower (degreeNoteValues n : Set ONote) := by
  intro a ha b hb h
  haveI : ONote.NF a := degreeNoteValues_nf ha
  haveI : ONote.NF b := degreeNoteValues_nf hb
  apply ONote.repr_inj.mp
  apply (Ordinal.opow_right_inj one_lt_omega0).mp
  simpa [repr_principalPower] using congrArg ONote.repr h

/-- Counting inner exponents is equivalent to the canonical ordinal count. -/
theorem a199812_eq_degreeNoteCount (n : Nat) : a199812 n = degreeNoteCount n := by
  rw [a199812_eq_noteCount, exponentNoteCount, degreeNoteCount,
    exponentNoteValues_eq_degreeNoteValues_image]
  exact Finset.card_image_of_injOn (principalPower_injOn_degreeNoteValues n)

/--
Dynamic normal-form computation of the exponent value set: the shared finite
split recurrence for the same canonical lexical syntax, with atom interpreted
as the exponent note `1` and power interpreted as `combineExponent`.
-/
def computedExponentValues (n : Nat) : Finset ONote :=
  PowTower.Expr.recursiveValueFinset (1 : ONote) combineExponent n

/-- The dynamic normal-form count corresponding to A199812. -/
def computedExponentCount (n : Nat) : Nat :=
  (computedExponentValues n).card

theorem computedExponentValues_eq_recursiveValueFinset (n : Nat) :
    computedExponentValues n =
      PowTower.Expr.recursiveValueFinset (1 : ONote) combineExponent n := rfl

theorem computedExponentCount_eq_recursiveValueFinset_card (n : Nat) :
    computedExponentCount n =
      (PowTower.Expr.recursiveValueFinset (1 : ONote) combineExponent n).card := rfl

/-- Degree-combine operation forced by `(omega^omega^a)^(omega^omega^b)`. -/
def combineDegree (a b : ONote) : ONote :=
  a + principalPower b

theorem degreeNote_eq_sharedCombineEval (e : PowTower.Expr) :
    degreeNote e = PowTower.Expr.eval (0 : ONote) combineDegree e := by
  induction e with
  | atom =>
      rfl
  | pow a b iha ihb =>
      simp [degreeNote, PowTower.Expr.eval, combineDegree, iha, ihb]

theorem degreeNoteValues_eq_recursiveValueFinset (n : Nat) :
    degreeNoteValues n =
      PowTower.Expr.recursiveValueFinset (0 : ONote) combineDegree n := by
  rw [degreeNoteValues_eq_evalFinset]
  exact PowTower.Expr.evalFinset_eq_recursiveValueFinset_of_eval_eq
    degreeNote (0 : ONote) combineDegree degreeNote_eq_sharedCombineEval n

/--
Dynamic computation of the inner exponent value set: the shared finite split
recurrence for the same canonical lexical syntax, with atom interpreted as the
degree note `0` and power interpreted as `combineDegree`.

All `exponentNote` values are principal powers, so counting the inner exponents
uses the simpler recurrence `a, b ↦ a + omega^b`.
-/
def computedDegreeValues (n : Nat) : Finset ONote :=
  PowTower.Expr.recursiveValueFinset (0 : ONote) combineDegree n

/-- The dynamic inner-exponent count corresponding to A199812. -/
def computedDegreeCount (n : Nat) : Nat :=
  (computedDegreeValues n).card

theorem computedDegreeValues_eq_recursiveValueFinset (n : Nat) :
    computedDegreeValues n =
      PowTower.Expr.recursiveValueFinset (0 : ONote) combineDegree n := rfl

theorem computedDegreeCount_eq_recursiveValueFinset_card (n : Nat) :
    computedDegreeCount n =
      (PowTower.Expr.recursiveValueFinset (0 : ONote) combineDegree n).card := rfl

/--
The degree recurrence computes exactly the inner exponents obtained from the
canonical lexical parenthesizations.
-/
theorem degreeNoteValues_eq_computedDegreeValues (n : Nat) :
    degreeNoteValues n = computedDegreeValues n :=
  degreeNoteValues_eq_recursiveValueFinset n

/-- The dynamic inner-exponent count is equivalent to the canonical ordinal count. -/
theorem a199812_eq_computedDegreeCount (n : Nat) : a199812 n = computedDegreeCount n := by
  rw [a199812_eq_degreeNoteCount, degreeNoteCount, computedDegreeCount,
    degreeNoteValues_eq_computedDegreeValues]

theorem a199812_eq_degreeRecursiveValueFinset_card (n : Nat) :
    a199812 n =
      (PowTower.Expr.recursiveValueFinset (0 : ONote) combineDegree n).card := by
  rw [a199812_eq_computedDegreeCount, computedDegreeCount_eq_recursiveValueFinset_card]

/--
The dynamic distinct-value recurrence computes exactly the normal-form
exponents obtained from the lexical parenthesizations.
-/
theorem exponentNoteValues_eq_computedExponentValues (n : Nat) :
    exponentNoteValues n = computedExponentValues n :=
  exponentNoteValues_eq_recursiveValueFinset n

/-- The dynamic normal-form count is equivalent to the canonical ordinal count. -/
theorem a199812_eq_computedCount (n : Nat) : a199812 n = computedExponentCount n := by
  rw [a199812_eq_noteCount, exponentNoteCount, computedExponentCount,
    exponentNoteValues_eq_computedExponentValues]

theorem a199812_eq_exponentRecursiveValueFinset_card (n : Nat) :
    a199812 n =
      (PowTower.Expr.recursiveValueFinset (1 : ONote) combineExponent n).card := by
  rw [a199812_eq_computedCount, computedExponentCount_eq_recursiveValueFinset_card]

/-- Memoized dynamic count corresponding to A199812, from the shared memo table. -/
def computedExponentCountMemo (n : Nat) : Nat :=
  (PowTower.Expr.recursiveValueFinsetMemo (1 : ONote) combineExponent n).card

theorem computedExponentCountMemo_eq (n : Nat) :
    computedExponentCountMemo n = computedExponentCount n := by
  rw [computedExponentCountMemo, PowTower.Expr.recursiveValueFinsetMemo_eq]
  rfl

/-- The memoized recurrence count is equivalent to the canonical ordinal count. -/
theorem a199812_eq_memoCount (n : Nat) : a199812 n = computedExponentCountMemo n := by
  rw [a199812_eq_computedCount, computedExponentCountMemo_eq]

/-- Memoized dynamic counts for sizes `1, ..., n`, computed from one shared table. -/
def computedExponentCountsMemoThrough (n : Nat) : List Nat :=
  PowTower.Expr.recursiveValueCountsMemoThrough (1 : ONote) combineExponent n

theorem a199812_eq_of_countsMemoThrough {N n value : Nat}
    (hpos : 0 < n) (hN : n ≤ N)
    (hcount : (computedExponentCountsMemoThrough N).getD (n - 1) 0 = value) :
    a199812 n = value := by
  rw [a199812_eq_exponentRecursiveValueFinset_card,
    PowTower.Expr.recursiveValueFinset_card_eq_countsMemoThrough_getD hpos hN]
  exact hcount

/--
Fast duplicate-free inner-exponent counts for sizes `1, ..., n`, computed from
one shared hash-set fast table.
-/
def fastDegreeCountsMemoThrough (n : Nat) : List Nat :=
  PowTower.Expr.fastCountsThrough (0 : ONote) combineDegree n

/-- One verified fast-table row certifies a canonical A199812 value. -/
theorem a199812_eq_of_fastDegreeCountsMemoThrough {N n value : Nat}
    (hpos : 0 < n) (hN : n ≤ N)
    (hcount : (fastDegreeCountsMemoThrough N).getD (n - 1) 0 = value) :
    a199812 n = value := by
  rw [a199812_eq_degreeRecursiveValueFinset_card,
    PowTower.Expr.recursiveValueFinset_card_eq_fastCountsThrough_getD hpos hN]
  exact hcount

/-- Shared fast executable certificate for `A199812(1)` through `A199812(13)`. -/
theorem fastDegreeCountsMemoThrough_thirteen :
    fastDegreeCountsMemoThrough 13 =
      [1, 1, 2, 5, 13, 32, 79, 193, 478, 1196, 3037, 7802, 20287] := by
  native_decide

/-- `A199812(1) = 1`. -/
theorem a199812_one : a199812 1 = 1 := by
  refine a199812_eq_of_fastDegreeCountsMemoThrough (N := 13) (n := 1) ?_ ?_ ?_
  · decide
  · decide
  · rw [fastDegreeCountsMemoThrough_thirteen]
    rfl

/-- `A199812(2) = 1`. -/
theorem a199812_two : a199812 2 = 1 := by
  refine a199812_eq_of_fastDegreeCountsMemoThrough (N := 13) (n := 2) ?_ ?_ ?_
  · decide
  · decide
  · rw [fastDegreeCountsMemoThrough_thirteen]
    rfl

/-- `A199812(3) = 2`. -/
theorem a199812_three : a199812 3 = 2 := by
  refine a199812_eq_of_fastDegreeCountsMemoThrough (N := 13) (n := 3) ?_ ?_ ?_
  · decide
  · decide
  · rw [fastDegreeCountsMemoThrough_thirteen]
    rfl

/-- `A199812(4) = 5`. -/
theorem a199812_four : a199812 4 = 5 := by
  refine a199812_eq_of_fastDegreeCountsMemoThrough (N := 13) (n := 4) ?_ ?_ ?_
  · decide
  · decide
  · rw [fastDegreeCountsMemoThrough_thirteen]
    rfl

/-- `A199812(5) = 13`. -/
theorem a199812_five : a199812 5 = 13 := by
  refine a199812_eq_of_fastDegreeCountsMemoThrough (N := 13) (n := 5) ?_ ?_ ?_
  · decide
  · decide
  · rw [fastDegreeCountsMemoThrough_thirteen]
    rfl

/-- `A199812(6) = 32`. -/
theorem a199812_six : a199812 6 = 32 := by
  refine a199812_eq_of_fastDegreeCountsMemoThrough (N := 13) (n := 6) ?_ ?_ ?_
  · decide
  · decide
  · rw [fastDegreeCountsMemoThrough_thirteen]
    rfl

/-- `A199812(7) = 79`. -/
theorem a199812_seven : a199812 7 = 79 := by
  refine a199812_eq_of_fastDegreeCountsMemoThrough (N := 13) (n := 7) ?_ ?_ ?_
  · decide
  · decide
  · rw [fastDegreeCountsMemoThrough_thirteen]
    rfl

/-- `A199812(8) = 193`. -/
theorem a199812_eight : a199812 8 = 193 := by
  refine a199812_eq_of_fastDegreeCountsMemoThrough (N := 13) (n := 8) ?_ ?_ ?_
  · decide
  · decide
  · rw [fastDegreeCountsMemoThrough_thirteen]
    rfl

/-- `A199812(9) = 478`. -/
theorem a199812_nine : a199812 9 = 478 := by
  refine a199812_eq_of_fastDegreeCountsMemoThrough (N := 13) (n := 9) ?_ ?_ ?_
  · decide
  · decide
  · rw [fastDegreeCountsMemoThrough_thirteen]
    rfl

/-- `A199812(10) = 1196`. -/
theorem a199812_ten : a199812 10 = 1196 := by
  refine a199812_eq_of_fastDegreeCountsMemoThrough (N := 13) (n := 10) ?_ ?_ ?_
  · decide
  · decide
  · rw [fastDegreeCountsMemoThrough_thirteen]
    rfl

/-- `A199812(11) = 3037`. -/
theorem a199812_eleven : a199812 11 = 3037 := by
  refine a199812_eq_of_fastDegreeCountsMemoThrough (N := 13) (n := 11) ?_ ?_ ?_
  · decide
  · decide
  · rw [fastDegreeCountsMemoThrough_thirteen]
    rfl

/-- `A199812(12) = 7802`. -/
theorem a199812_twelve : a199812 12 = 7802 := by
  refine a199812_eq_of_fastDegreeCountsMemoThrough (N := 13) (n := 12) ?_ ?_ ?_
  · decide
  · decide
  · rw [fastDegreeCountsMemoThrough_thirteen]
    rfl

/-- `A199812(13) = 20287`. -/
theorem a199812_thirteen : a199812 13 = 20287 := by
  refine a199812_eq_of_fastDegreeCountsMemoThrough (N := 13) (n := 13) ?_ ?_ ?_
  · decide
  · decide
  · rw [fastDegreeCountsMemoThrough_thirteen]
    rfl

end TowerExpr

export TowerExpr (a199812 a199812_eq_noteCount a199812_one a199812_two a199812_three
  a199812_four a199812_five a199812_six a199812_seven a199812_eight
  a199812_nine a199812_ten a199812_eleven a199812_twelve a199812_thirteen)

end A199812

end LeanProofs
