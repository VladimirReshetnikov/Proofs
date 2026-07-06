import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.NAry
import Mathlib.SetTheory.Ordinal.Notation

/-!
# Initial values of OEIS A199812

OEIS A199812 counts the distinct ordinals represented by all binary
parenthesizations of `omega^omega^...^omega`.

The primary definition in this module is deliberately lexical: first build the
binary parenthesization syntax, then interpret each syntax tree directly as an
ordinal expression using ordinary ordinal exponentiation, with the leaf
interpreted as the first infinite ordinal `omega`.

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

/-- Binary parenthesized expressions built from copies of `omega`. -/
inductive TowerExpr where
  | «𝜔»
  | pow (a b : TowerExpr)
deriving Repr, DecidableEq

namespace TowerExpr

open TowerExpr

/-- The number of leaves in a tower expression. -/
def size : TowerExpr -> Nat
  | «𝜔» => 1
  | pow a b => size a + size b

/-- All legal binary parenthesizations with exactly `n` copies of `omega`. -/
def parenthesizations : Nat -> List TowerExpr
  | 0 => []
  | 1 => [«𝜔»]
  | n + 2 =>
      (List.finRange (n + 1)).flatMap fun k =>
        (parenthesizations (k.1 + 1)).flatMap fun a =>
          (parenthesizations (n + 1 - k.1)).map fun b => pow a b
termination_by n => n
decreasing_by
  · exact Nat.lt_succ_of_le (Nat.sub_le _ _)
  · exact Nat.succ_lt_succ k.2

/-- Canonical ordinal interpretation of a parenthesized tower expression. -/
noncomputable def evalOrdinal : TowerExpr -> Ordinal.{0}
  | «𝜔» => (ω : Ordinal)
  | pow a b => evalOrdinal a ^ evalOrdinal b

/-- The principal ordinal power `omega^e`, represented as an `ONote`. -/
def principalPower (e : ONote) : ONote :=
  ONote.oadd e (1 : ℕ+) 0

/-- The exponent-combine operation forced by `(omega^a)^(omega^b) = omega^(a * omega^b)`. -/
def combineExponent (a b : ONote) : ONote :=
  a * principalPower b

/-- The `ONote` exponent `e` such that the expression evaluates to `omega^e`. -/
def exponentNote : TowerExpr -> ONote
  | «𝜔» => 1
  | pow a b => combineExponent (exponentNote a) (exponentNote b)

instance principalPower_nf (e : ONote) [ONote.NF e] : ONote.NF (principalPower e) := by
  dsimp [principalPower]
  infer_instance

/-- Every computed exponent note is in Cantor normal form. -/
theorem exponentNote_nf : ∀ e : TowerExpr, ONote.NF (exponentNote e)
  | «𝜔» => by
      simpa [exponentNote] using (inferInstance : ONote.NF (1 : ONote))
  | pow a b => by
      haveI := exponentNote_nf a
      haveI := exponentNote_nf b
      dsimp [exponentNote, combineExponent]
      infer_instance

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
theorem evalOrdinal_eq_omega_opow_exponentNote (e : TowerExpr) :
    evalOrdinal e = (ω : Ordinal) ^ ONote.repr (exponentNote e) := by
  induction e with
  | «𝜔» =>
      simp [evalOrdinal, exponentNote, ONote.repr_one, Ordinal.opow_one]
  | pow a b iha ihb =>
      haveI := exponentNote_nf a
      haveI := exponentNote_nf b
      calc
        evalOrdinal (pow a b)
            = ((ω : Ordinal) ^ ONote.repr (exponentNote a)) ^
                ((ω : Ordinal) ^ ONote.repr (exponentNote b)) := by
                  simp [evalOrdinal, iha, ihb]
        _ = (ω : Ordinal) ^
              (ONote.repr (exponentNote a) *
                ((ω : Ordinal) ^ ONote.repr (exponentNote b))) := by
                  rw [← Ordinal.opow_mul]
        _ = (ω : Ordinal) ^ ONote.repr (exponentNote (pow a b)) := by
                  simp [exponentNote, repr_combineExponent]

/--
The canonical finite set of ordinal values for `n` copies of `omega`.

This is the primary definition: it is obtained directly from the listed
parenthesized expressions and ordinal exponentiation.
-/
noncomputable def ordinalValues (n : Nat) : Finset Ordinal.{0} := by
  classical
  exact (parenthesizations n).toFinset.image evalOrdinal

/-- OEIS A199812, from the canonical ordinal interpretation. -/
noncomputable def a199812 (n : Nat) : Nat :=
  (ordinalValues n).card

/-- The list of verified normal-form exponents for the same parenthesized expressions. -/
def exponentNoteList (n : Nat) : List ONote :=
  (parenthesizations n).map exponentNote

/-- The finite set of verified normal-form exponents for the same parenthesized expressions. -/
def exponentNoteValues (n : Nat) : Finset ONote :=
  (exponentNoteList n).toFinset

/-- The direct normal-form count obtained from all lexical parenthesizations. -/
def exponentNoteCount (n : Nat) : Nat :=
  (exponentNoteValues n).card

/-- Interpret a normal-form exponent note as the principal ordinal power it denotes. -/
noncomputable def ordinalOfNote (o : ONote) : Ordinal.{0} :=
  (ω : Ordinal) ^ ONote.repr o

theorem ordinalValues_eq_exponentNoteValues_image (n : Nat) :
    ordinalValues n = (exponentNoteValues n).image ordinalOfNote := by
  classical
  ext o
  simp [ordinalValues, exponentNoteValues, exponentNoteList, ordinalOfNote,
    evalOrdinal_eq_omega_opow_exponentNote]

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
  rw [a199812, ordinalValues_eq_exponentNoteValues_image, exponentNoteCount]
  exact Finset.card_image_of_injOn (ordinalOfNote_injOn_exponentNoteValues n)

/-- Finite union over a list, used to keep the executable recurrence structurally simple. -/
def listBiUnion {α β : Type} [DecidableEq β] (xs : List α) (f : α -> Finset β) : Finset β :=
  xs.foldr (fun x acc => f x ∪ acc) ∅

@[simp]
theorem mem_listBiUnion {α β : Type} [DecidableEq β] {xs : List α}
    {f : α -> Finset β} {b : β} :
    b ∈ listBiUnion xs f ↔ ∃ x ∈ xs, b ∈ f x := by
  induction xs with
  | nil =>
      simp [listBiUnion]
  | cons x xs ih =>
      constructor
      · intro hb
        simp only [listBiUnion, List.foldr_cons, Finset.mem_union] at hb
        rcases hb with hb | hb
        · exact ⟨x, by simp, hb⟩
        · rcases ih.mp hb with ⟨y, hy, hfy⟩
          exact ⟨y, by simp [hy], hfy⟩
      · intro h
        rcases h with ⟨y, hy, hfy⟩
        simp only [listBiUnion, List.foldr_cons, Finset.mem_union]
        rw [List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact Or.inl hfy
        · exact Or.inr (ih.mpr ⟨y, hy, hfy⟩)

/--
Dynamic normal-form computation of the exponent value set.

This is the finite-set version of the OEIS program: the values of size `n` are
the union over binary splits of the pairwise exponent-combine operation applied
to the already distinct smaller value sets.
-/
def computedExponentValues : Nat -> Finset ONote
  | 0 => ∅
  | 1 => {1}
  | n + 2 =>
      listBiUnion (List.finRange (n + 1)) fun k =>
        Finset.image₂ combineExponent
          (computedExponentValues (k.1 + 1))
          (computedExponentValues (n + 1 - k.1))
termination_by n => n
decreasing_by
  · exact Nat.succ_lt_succ k.2
  · exact Nat.lt_succ_of_le (Nat.sub_le _ _)

/-- The dynamic normal-form count corresponding to A199812. -/
def computedExponentCount (n : Nat) : Nat :=
  (computedExponentValues n).card

/--
The dynamic distinct-value recurrence computes exactly the normal-form
exponents obtained from the lexical parenthesizations.
-/
theorem exponentNoteValues_eq_computedExponentValues (n : Nat) :
    exponentNoteValues n = computedExponentValues n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          ext o
          simp [exponentNoteValues, exponentNoteList, parenthesizations, computedExponentValues]
      | succ n =>
          cases n with
          | zero =>
              ext o
              simp [exponentNoteValues, exponentNoteList, parenthesizations, computedExponentValues,
                exponentNote]
          | succ n =>
              ext o
              constructor
              · intro ho
                simp only [exponentNoteValues, exponentNoteList, parenthesizations,
                  List.mem_toFinset, List.mem_map, List.mem_flatMap] at ho
                rcases ho with ⟨e, he, rfl⟩
                rcases he with ⟨k, hk, a, ha, b, hb, rfl⟩
                simp only [computedExponentValues, mem_listBiUnion, Finset.mem_image₂]
                refine ⟨k, hk, exponentNote a, ?_, exponentNote b, ?_, rfl⟩
                · have hklt : k.1 + 1 < n + 1 + 1 := by
                    exact Nat.succ_lt_succ k.2
                  rw [← ih (k.1 + 1) hklt]
                  simp only [exponentNoteValues, exponentNoteList, List.mem_toFinset,
                    List.mem_map]
                  exact ⟨a, ha, rfl⟩
                · have hklt : n + 1 - k.1 < n + 1 + 1 := by
                    exact Nat.lt_succ_of_le (Nat.sub_le _ _)
                  rw [← ih (n + 1 - k.1) hklt]
                  simp only [exponentNoteValues, exponentNoteList, List.mem_toFinset,
                    List.mem_map]
                  exact ⟨b, hb, rfl⟩
              · intro ho
                simp only [computedExponentValues, mem_listBiUnion, Finset.mem_image₂] at ho
                rcases ho with ⟨k, hk, aNote, haNote, bNote, hbNote, hcombine⟩
                simp only [exponentNoteValues, exponentNoteList, parenthesizations,
                  List.mem_toFinset, List.mem_map, List.mem_flatMap]
                have hklt₁ : k.1 + 1 < n + 1 + 1 := by
                  exact Nat.succ_lt_succ k.2
                have hklt₂ : n + 1 - k.1 < n + 1 + 1 := by
                  exact Nat.lt_succ_of_le (Nat.sub_le _ _)
                rw [← ih (k.1 + 1) hklt₁] at haNote
                rw [← ih (n + 1 - k.1) hklt₂] at hbNote
                simp only [exponentNoteValues, exponentNoteList, List.mem_toFinset,
                  List.mem_map] at haNote hbNote
                rcases haNote with ⟨a, ha, rfl⟩
                rcases hbNote with ⟨b, hb, rfl⟩
                exact ⟨TowerExpr.pow a b, ⟨k, hk, a, ha, b, hb, rfl⟩,
                  by simpa [exponentNote] using hcombine⟩

/-- The dynamic normal-form count is equivalent to the canonical ordinal count. -/
theorem a199812_eq_computedCount (n : Nat) : a199812 n = computedExponentCount n := by
  rw [a199812_eq_noteCount, exponentNoteCount, computedExponentCount,
    exponentNoteValues_eq_computedExponentValues]

/-- `A199812(1) = 1`. -/
theorem a199812_one : a199812 1 = 1 := by
  rw [a199812_eq_computedCount]
  native_decide

end TowerExpr

export TowerExpr (a199812 a199812_eq_noteCount a199812_one)

end A199812

end LeanProofs
