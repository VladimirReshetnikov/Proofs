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

theorem hashSet_toList_nodup (m : Std.HashSet ONote) : m.toList.Nodup := by
  have hpair := Std.HashSet.distinct_toList (m := m)
  exact hpair.imp (by
    intro a b hne heq
    subst heq
    simp [BEq.rfl] at hne)

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

/-- The direct normal-form count obtained from all lexical parenthesizations. -/
def exponentNoteCount (n : Nat) : Nat :=
  (exponentNoteValues n).card

/-- Interpret a normal-form exponent note as the principal ordinal power it denotes. -/
noncomputable def ordinalOfNote (o : ONote) : Ordinal.{0} :=
  (ω : Ordinal) ^ ONote.repr o

theorem ordinalValues_eq_exponentNoteValues_image (n : Nat) :
    ordinalValues n = (exponentNoteValues n).image ordinalOfNote := by
  classical
  simpa [ordinalValues, exponentNoteValues, exponentNoteList, ordinalOfNote,
    PowTower.Expr.evalFinset] using
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

/-- Pointwise congruence for finite unions over a list. -/
theorem listBiUnion_congr {α β : Type} [DecidableEq β] {xs : List α}
    {f g : α -> Finset β} (h : ∀ x ∈ xs, f x = g x) :
    listBiUnion xs f = listBiUnion xs g := by
  induction xs with
  | nil =>
      simp [listBiUnion]
  | cons x xs ih =>
      simp only [listBiUnion, List.foldr_cons]
      rw [h x (by simp)]
      have htail :
          List.foldr (fun x acc => f x ∪ acc) ∅ xs =
            List.foldr (fun x acc => g x ∪ acc) ∅ xs := by
        simpa [listBiUnion] using
          ih (by
            intro y hy
            exact h y (by simp [hy]))
      rw [htail]

/-- Degree-combine operation forced by `(omega^omega^a)^(omega^omega^b)`. -/
def combineDegree (a b : ONote) : ONote :=
  a + principalPower b

/--
Dynamic computation of the inner exponent value set.

All `exponentNote` values are principal powers, so counting the inner exponents
uses the simpler recurrence `a, b ↦ a + omega^b`.
-/
def computedDegreeValues : Nat -> Finset ONote
  | 0 => ∅
  | 1 => {0}
  | n + 2 =>
      listBiUnion (List.finRange (n + 1)) fun k =>
        Finset.image₂ combineDegree
          (computedDegreeValues (k.1 + 1))
          (computedDegreeValues (n + 1 - k.1))
termination_by n => n
decreasing_by
  · exact Nat.succ_lt_succ k.2
  · exact Nat.lt_succ_of_le (Nat.sub_le _ _)

/-- The dynamic inner-exponent count corresponding to A199812. -/
def computedDegreeCount (n : Nat) : Nat :=
  (computedDegreeValues n).card

/--
The degree recurrence computes exactly the inner exponents obtained from the
canonical lexical parenthesizations.
-/
theorem degreeNoteValues_eq_computedDegreeValues (n : Nat) :
    degreeNoteValues n = computedDegreeValues n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          ext o
          simp [degreeNoteValues, degreeNoteList, PowTower.Expr.parenthesizations,
            computedDegreeValues]
      | succ n =>
          cases n with
          | zero =>
              ext o
              simp [degreeNoteValues, degreeNoteList, PowTower.Expr.parenthesizations,
                computedDegreeValues, degreeNote]
          | succ n =>
              ext o
              constructor
              · intro ho
                simp only [degreeNoteValues, degreeNoteList, PowTower.Expr.parenthesizations,
                  List.mem_toFinset, List.mem_map, List.mem_flatMap] at ho
                rcases ho with ⟨e, he, rfl⟩
                rcases he with ⟨k, hk, a, ha, b, hb, rfl⟩
                simp only [computedDegreeValues, mem_listBiUnion, Finset.mem_image₂]
                refine ⟨k, hk, degreeNote a, ?_, degreeNote b, ?_, rfl⟩
                · have hklt : k.1 + 1 < n + 1 + 1 := by
                    exact Nat.succ_lt_succ k.2
                  rw [← ih (k.1 + 1) hklt]
                  simp only [degreeNoteValues, degreeNoteList, List.mem_toFinset, List.mem_map]
                  exact ⟨a, ha, rfl⟩
                · have hklt : n + 1 - k.1 < n + 1 + 1 := by
                    exact Nat.lt_succ_of_le (Nat.sub_le _ _)
                  rw [← ih (n + 1 - k.1) hklt]
                  simp only [degreeNoteValues, degreeNoteList, List.mem_toFinset, List.mem_map]
                  exact ⟨b, hb, rfl⟩
              · intro ho
                simp only [computedDegreeValues, mem_listBiUnion, Finset.mem_image₂] at ho
                rcases ho with ⟨k, hk, aNote, haNote, bNote, hbNote, hcombine⟩
                simp only [degreeNoteValues, degreeNoteList, PowTower.Expr.parenthesizations,
                  List.mem_toFinset, List.mem_map, List.mem_flatMap]
                have hklt₁ : k.1 + 1 < n + 1 + 1 := by
                  exact Nat.succ_lt_succ k.2
                have hklt₂ : n + 1 - k.1 < n + 1 + 1 := by
                  exact Nat.lt_succ_of_le (Nat.sub_le _ _)
                rw [← ih (k.1 + 1) hklt₁] at haNote
                rw [← ih (n + 1 - k.1) hklt₂] at hbNote
                simp only [degreeNoteValues, degreeNoteList, List.mem_toFinset, List.mem_map]
                  at haNote hbNote
                rcases haNote with ⟨a, ha, rfl⟩
                rcases hbNote with ⟨b, hb, rfl⟩
                exact ⟨PowTower.Expr.pow a b, ⟨k, hk, a, ha, b, hb, rfl⟩,
                  by simpa [degreeNote, combineDegree] using hcombine⟩

/-- The dynamic inner-exponent count is equivalent to the canonical ordinal count. -/
theorem a199812_eq_computedDegreeCount (n : Nat) : a199812 n = computedDegreeCount n := by
  rw [a199812_eq_degreeNoteCount, degreeNoteCount, computedDegreeCount,
    degreeNoteValues_eq_computedDegreeValues]

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
          simp [exponentNoteValues, exponentNoteList, PowTower.Expr.parenthesizations,
            computedExponentValues]
      | succ n =>
          cases n with
          | zero =>
              ext o
              simp [exponentNoteValues, exponentNoteList, PowTower.Expr.parenthesizations,
                computedExponentValues, exponentNote]
          | succ n =>
              ext o
              constructor
              · intro ho
                simp only [exponentNoteValues, exponentNoteList, PowTower.Expr.parenthesizations,
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
                simp only [exponentNoteValues, exponentNoteList, PowTower.Expr.parenthesizations,
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
                exact ⟨PowTower.Expr.pow a b, ⟨k, hk, a, ha, b, hb, rfl⟩,
                  by simpa [exponentNote] using hcombine⟩

/-- The dynamic normal-form count is equivalent to the canonical ordinal count. -/
theorem a199812_eq_computedCount (n : Nat) : a199812 n = computedExponentCount n := by
  rw [a199812_eq_noteCount, exponentNoteCount, computedExponentCount,
    exponentNoteValues_eq_computedExponentValues]

/--
Compute one recurrence row from an already-built table of smaller rows.

The table is only an executable optimization: the theorem
`computedExponentValuesFromTable_eq` below proves that it computes the same
finite set as `computedExponentValues` when the table entries are correct.
-/
def computedExponentValuesFromTable (levels : List (Finset ONote)) : Nat -> Finset ONote
  | 0 => ∅
  | 1 => {1}
  | n + 2 =>
      listBiUnion (List.finRange (n + 1)) fun k =>
        Finset.image₂ combineExponent
          (levels.getD (k.1 + 1) ∅)
          (levels.getD (n + 1 - k.1) ∅)

theorem computedExponentValuesFromTable_eq {levels : List (Finset ONote)} {n : Nat}
    (hlevels : ∀ i < n, levels.getD i ∅ = computedExponentValues i) :
    computedExponentValuesFromTable levels n = computedExponentValues n := by
  cases n with
  | zero =>
      simp [computedExponentValuesFromTable, computedExponentValues]
  | succ n =>
      cases n with
      | zero =>
          simp [computedExponentValuesFromTable, computedExponentValues]
      | succ n =>
          simp only [computedExponentValuesFromTable, computedExponentValues]
          apply listBiUnion_congr
          intro k hk
          rw [hlevels (k.1 + 1) (Nat.succ_lt_succ k.2)]
          rw [hlevels (n + 1 - k.1) (Nat.lt_succ_of_le (Nat.sub_le _ _))]

/-- Table of recurrence rows `0, ..., n - 1`, built once from left to right. -/
def computedExponentTable : Nat -> List (Finset ONote)
  | 0 => []
  | n + 1 =>
      let levels := computedExponentTable n
      levels ++ [computedExponentValuesFromTable levels n]

theorem computedExponentTable_length (n : Nat) :
    (computedExponentTable n).length = n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [computedExponentTable, ih]

theorem list_getD_eq_getElem {α : Type} (xs : List α) {i : Nat} (fallback : α)
    (hi : i < xs.length) :
    xs.getD i fallback = xs[i] := by
  simp [List.getD, List.getElem?_eq_getElem hi]

/-- The memo table agrees with the proved recurrence at every stored index. -/
theorem computedExponentTable_getD (n i : Nat) (hi : i < n) :
    (computedExponentTable n).getD i ∅ = computedExponentValues i := by
  induction n generalizing i with
  | zero =>
      exact (Nat.not_lt_zero i hi).elim
  | succ n ih =>
      have hle : i ≤ n := Nat.lt_succ_iff.mp hi
      rcases Nat.lt_or_eq_of_le hle with hlt | heq
      · have hiTable : i < (computedExponentTable n).length := by
          simpa [computedExponentTable_length] using hlt
        rw [computedExponentTable]
        rw [list_getD_eq_getElem
          (computedExponentTable n ++ [computedExponentValuesFromTable (computedExponentTable n) n])
          ∅ (by simpa [computedExponentTable_length] using hi)]
        rw [List.getElem_append_left hiTable]
        rw [← list_getD_eq_getElem (computedExponentTable n) ∅ hiTable]
        exact ih i hlt
      · subst i
        rw [computedExponentTable]
        rw [list_getD_eq_getElem
          (computedExponentTable n ++ [computedExponentValuesFromTable (computedExponentTable n) n])
          ∅ (by simp [computedExponentTable_length])]
        rw [List.getElem_append_right (by simp [computedExponentTable_length])]
        simp [computedExponentTable_length, computedExponentValuesFromTable_eq ih]

/-- Memoized recurrence value set, proved equal to `computedExponentValues`. -/
def computedExponentValuesMemo (n : Nat) : Finset ONote :=
  (computedExponentTable (n + 1)).getD n ∅

theorem computedExponentValuesMemo_eq (n : Nat) :
    computedExponentValuesMemo n = computedExponentValues n := by
  exact computedExponentTable_getD (n + 1) n (Nat.lt_succ_self n)

/-- Memoized dynamic count corresponding to A199812. -/
def computedExponentCountMemo (n : Nat) : Nat :=
  (computedExponentValuesMemo n).card

/-- Memoized dynamic counts for sizes `1, ..., n`, computed from one shared table. -/
def computedExponentCountsMemoThrough (n : Nat) : List Nat :=
  ((computedExponentTable (n + 1)).drop 1).map Finset.card

/-- Indexing the shared count table gives the corresponding memoized count. -/
theorem computedExponentCountsMemoThrough_getD {N i : Nat} (hi : i < N) :
    (computedExponentCountsMemoThrough N).getD i 0 = computedExponentCountMemo (i + 1) := by
  unfold computedExponentCountsMemoThrough
  have hiDrop :
      i < (List.drop 1 (computedExponentTable (N + 1))).length := by
    simp [computedExponentTable_length, hi]
  have hiCounts :
      i < (List.map Finset.card (List.drop 1 (computedExponentTable (N + 1)))).length := by
    simpa using hiDrop
  have hiTable : i + 1 < (computedExponentTable (N + 1)).length := by
    simpa [computedExponentTable_length, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using Nat.succ_lt_succ hi
  rw [list_getD_eq_getElem _ _ hiCounts]
  rw [List.getElem_map]
  rw [List.getElem_drop]
  have hiTable' : 1 + i < (computedExponentTable (N + 1)).length := by
    simpa [Nat.add_comm] using hiTable
  have hleft :
      (computedExponentTable (N + 1))[1 + i] = computedExponentValues (i + 1) := by
    rw [← list_getD_eq_getElem (computedExponentTable (N + 1)) ∅ hiTable']
    simpa [Nat.add_comm] using
      computedExponentTable_getD (N + 1) (i + 1) (Nat.succ_lt_succ hi)
  rw [hleft]
  unfold computedExponentCountMemo
  rw [computedExponentValuesMemo_eq]

theorem computedExponentCountMemo_eq_countsMemoThrough_getD {N n : Nat}
    (hpos : 0 < n) (hN : n ≤ N) :
    computedExponentCountMemo n = (computedExponentCountsMemoThrough N).getD (n - 1) 0 := by
  cases n with
  | zero =>
      exact (Nat.not_lt_zero _ hpos).elim
  | succ i =>
      have hi : i < N := Nat.succ_le_iff.mp hN
      simpa using (computedExponentCountsMemoThrough_getD (N := N) (i := i) hi).symm

/-- The memoized recurrence count is equivalent to the canonical ordinal count. -/
theorem a199812_eq_memoCount (n : Nat) : a199812 n = computedExponentCountMemo n := by
  rw [a199812_eq_computedCount, computedExponentCountMemo, computedExponentValuesMemo_eq,
    computedExponentCount]

theorem a199812_eq_of_countsMemoThrough {N n value : Nat}
    (hpos : 0 < n) (hN : n ≤ N)
    (hcount : (computedExponentCountsMemoThrough N).getD (n - 1) 0 = value) :
    a199812 n = value := by
  calc
    a199812 n = computedExponentCountMemo n := a199812_eq_memoCount n
    _ = (computedExponentCountsMemoThrough N).getD (n - 1) 0 :=
      computedExponentCountMemo_eq_countsMemoThrough_getD hpos hN
    _ = value := hcount

/-- Insert all degree values produced by one fixed left value into an accumulator. -/
def insertRightDegreeValues (a : ONote) (right : List ONote)
    (seen : Std.HashSet ONote) : Std.HashSet ONote :=
  right.foldl (fun seen b => seen.insert (combineDegree a b)) seen

theorem mem_insertRightDegreeValues {a : ONote} {right : List ONote}
    {seen : Std.HashSet ONote} {x : ONote} :
    x ∈ insertRightDegreeValues a right seen ↔
      x ∈ seen ∨ ∃ b ∈ right, combineDegree a b = x := by
  induction right generalizing seen with
  | nil =>
      simp [insertRightDegreeValues]
  | cons b bs ih =>
      rw [insertRightDegreeValues, List.foldl_cons]
      change x ∈ insertRightDegreeValues a bs (seen.insert (combineDegree a b)) ↔
        x ∈ seen ∨ ∃ b_1 ∈ b :: bs, combineDegree a b_1 = x
      rw [ih]
      rw [Std.HashSet.mem_insert]
      simp [beq_iff_eq]
      aesop

/-- Insert all degree values produced by one binary split into an accumulator. -/
def insertDegreeProducts (left right : List ONote)
    (seen : Std.HashSet ONote) : Std.HashSet ONote :=
  left.foldl (fun seen a => insertRightDegreeValues a right seen) seen

theorem mem_insertDegreeProducts {left right : List ONote}
    {seen : Std.HashSet ONote} {x : ONote} :
    x ∈ insertDegreeProducts left right seen ↔
      x ∈ seen ∨ ∃ a ∈ left, ∃ b ∈ right, combineDegree a b = x := by
  induction left generalizing seen with
  | nil =>
      simp [insertDegreeProducts]
  | cons a as ih =>
      rw [insertDegreeProducts, List.foldl_cons]
      change x ∈ insertDegreeProducts as right (insertRightDegreeValues a right seen) ↔
        x ∈ seen ∨ ∃ a_1 ∈ a :: as, ∃ b ∈ right, combineDegree a_1 b = x
      rw [ih]
      rw [mem_insertRightDegreeValues]
      simp
      aesop

theorem mem_foldDegreeProducts {ι : Type} {splits : List ι}
    {left right : ι -> List ONote} {seen : Std.HashSet ONote} {x : ONote} :
    x ∈ splits.foldl
        (fun seen k => insertDegreeProducts (left k) (right k) seen) seen ↔
      x ∈ seen ∨
        ∃ k ∈ splits, ∃ a ∈ left k, ∃ b ∈ right k, combineDegree a b = x := by
  induction splits generalizing seen with
  | nil =>
      simp
  | cons k ks ih =>
      rw [List.foldl_cons]
      rw [ih]
      rw [mem_insertDegreeProducts]
      simp
      aesop

/--
Fast row builder for the inner-exponent recurrence.

It returns a duplicate-free list, but `fastDegreeValuesFromTable_toFinset_eq`
below proves that its `toFinset` is exactly the proof-facing finite set.
-/
def fastDegreeValuesFromTable (levels : List (List ONote)) : Nat -> List ONote
  | 0 => []
  | 1 => [0]
  | n + 2 =>
      ((List.finRange (n + 1)).foldl
        (fun seen k =>
          insertDegreeProducts
            (levels.getD (k.1 + 1) [])
            (levels.getD (n + 1 - k.1) [])
            seen)
        (∅ : Std.HashSet ONote)).toList

theorem fastDegreeValuesFromTable_nodup (levels : List (List ONote)) (n : Nat) :
    (fastDegreeValuesFromTable levels n).Nodup := by
  cases n with
  | zero =>
      simp [fastDegreeValuesFromTable]
  | succ n =>
      cases n with
      | zero =>
          simp [fastDegreeValuesFromTable]
      | succ _ =>
          exact hashSet_toList_nodup _

theorem fastDegreeValuesFromTable_toFinset_eq {levels : List (List ONote)} {n : Nat}
    (hlevels : ∀ i < n, (levels.getD i []).toFinset = computedDegreeValues i) :
    (fastDegreeValuesFromTable levels n).toFinset = computedDegreeValues n := by
  cases n with
  | zero =>
      simp [fastDegreeValuesFromTable, computedDegreeValues]
  | succ n =>
      cases n with
      | zero =>
          simp [fastDegreeValuesFromTable, computedDegreeValues]
      | succ n =>
          ext x
          simp only [fastDegreeValuesFromTable, List.mem_toFinset]
          rw [Std.HashSet.mem_toList]
          rw [mem_foldDegreeProducts]
          simp only [Std.HashSet.not_mem_empty, false_or]
          simp only [computedDegreeValues, mem_listBiUnion, Finset.mem_image₂]
          constructor
          · rintro ⟨k, hk, a, ha, b, hb, hx⟩
            refine ⟨k, hk, a, ?_, b, ?_, hx⟩
            · have hklt : k.1 + 1 < n + 1 + 1 := Nat.succ_lt_succ k.2
              rw [← hlevels (k.1 + 1) hklt]
              exact List.mem_toFinset.mpr ha
            · have hklt : n + 1 - k.1 < n + 1 + 1 :=
                Nat.lt_succ_of_le (Nat.sub_le _ _)
              rw [← hlevels (n + 1 - k.1) hklt]
              exact List.mem_toFinset.mpr hb
          · rintro ⟨k, hk, a, ha, b, hb, hx⟩
            refine ⟨k, hk, a, ?_, b, ?_, hx⟩
            · have hklt : k.1 + 1 < n + 1 + 1 := Nat.succ_lt_succ k.2
              rw [← hlevels (k.1 + 1) hklt] at ha
              exact List.mem_toFinset.mp ha
            · have hklt : n + 1 - k.1 < n + 1 + 1 :=
                Nat.lt_succ_of_le (Nat.sub_le _ _)
              rw [← hlevels (n + 1 - k.1) hklt] at hb
              exact List.mem_toFinset.mp hb

/-- Fast duplicate-free table of inner-exponent rows `0, ..., n - 1`. -/
def fastDegreeTable : Nat -> List (List ONote)
  | 0 => []
  | n + 1 =>
      let levels := fastDegreeTable n
      levels ++ [fastDegreeValuesFromTable levels n]

theorem fastDegreeTable_length (n : Nat) :
    (fastDegreeTable n).length = n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [fastDegreeTable, ih]

theorem fastDegreeTable_getD_toFinset (n i : Nat) (hi : i < n) :
    ((fastDegreeTable n).getD i []).toFinset = computedDegreeValues i := by
  induction n generalizing i with
  | zero =>
      exact (Nat.not_lt_zero i hi).elim
  | succ n ih =>
      have hle : i ≤ n := Nat.lt_succ_iff.mp hi
      rcases Nat.lt_or_eq_of_le hle with hlt | heq
      · have hiTable : i < (fastDegreeTable n).length := by
          simpa [fastDegreeTable_length] using hlt
        rw [fastDegreeTable]
        rw [list_getD_eq_getElem
          (fastDegreeTable n ++ [fastDegreeValuesFromTable (fastDegreeTable n) n])
          [] (by simpa [fastDegreeTable_length] using hi)]
        rw [List.getElem_append_left hiTable]
        rw [← list_getD_eq_getElem (fastDegreeTable n) [] hiTable]
        exact ih i hlt
      · subst i
        rw [fastDegreeTable]
        rw [list_getD_eq_getElem
          (fastDegreeTable n ++ [fastDegreeValuesFromTable (fastDegreeTable n) n])
          [] (by simp [fastDegreeTable_length])]
        rw [List.getElem_append_right (by simp [fastDegreeTable_length])]
        simp [fastDegreeTable_length, fastDegreeValuesFromTable_toFinset_eq ih]

theorem fastDegreeTable_getD_nodup (n i : Nat) (hi : i < n) :
    ((fastDegreeTable n).getD i []).Nodup := by
  induction n generalizing i with
  | zero =>
      exact (Nat.not_lt_zero i hi).elim
  | succ n ih =>
      have hle : i ≤ n := Nat.lt_succ_iff.mp hi
      rcases Nat.lt_or_eq_of_le hle with hlt | heq
      · have hiTable : i < (fastDegreeTable n).length := by
          simpa [fastDegreeTable_length] using hlt
        rw [fastDegreeTable]
        rw [list_getD_eq_getElem
          (fastDegreeTable n ++ [fastDegreeValuesFromTable (fastDegreeTable n) n])
          [] (by simpa [fastDegreeTable_length] using hi)]
        rw [List.getElem_append_left hiTable]
        rw [← list_getD_eq_getElem (fastDegreeTable n) [] hiTable]
        exact ih i hlt
      · subst i
        rw [fastDegreeTable]
        rw [list_getD_eq_getElem
          (fastDegreeTable n ++ [fastDegreeValuesFromTable (fastDegreeTable n) n])
          [] (by simp [fastDegreeTable_length])]
        rw [List.getElem_append_right (by simp [fastDegreeTable_length])]
        simp [fastDegreeTable_length, fastDegreeValuesFromTable_nodup]

/-- Fast memoized inner-exponent row. -/
def fastDegreeValuesMemo (n : Nat) : List ONote :=
  (fastDegreeTable (n + 1)).getD n []

theorem fastDegreeValuesMemo_toFinset_eq (n : Nat) :
    (fastDegreeValuesMemo n).toFinset = computedDegreeValues n := by
  exact fastDegreeTable_getD_toFinset (n + 1) n (Nat.lt_succ_self n)

theorem fastDegreeValuesMemo_nodup (n : Nat) :
    (fastDegreeValuesMemo n).Nodup := by
  exact fastDegreeTable_getD_nodup (n + 1) n (Nat.lt_succ_self n)

/-- Fast memoized count corresponding to the proof-facing degree recurrence. -/
def fastDegreeCountMemo (n : Nat) : Nat :=
  (fastDegreeValuesMemo n).length

theorem computedDegreeCount_eq_fastDegreeCountMemo (n : Nat) :
    computedDegreeCount n = fastDegreeCountMemo n := by
  rw [computedDegreeCount, fastDegreeCountMemo]
  rw [← fastDegreeValuesMemo_toFinset_eq n]
  exact List.toFinset_card_of_nodup (fastDegreeValuesMemo_nodup n)

theorem a199812_eq_fastDegreeCountMemo (n : Nat) :
    a199812 n = fastDegreeCountMemo n := by
  rw [a199812_eq_computedDegreeCount, computedDegreeCount_eq_fastDegreeCountMemo]

/-- Fast memoized counts for sizes `1, ..., n`, computed from one shared table. -/
def fastDegreeCountsMemoThrough (n : Nat) : List Nat :=
  ((fastDegreeTable (n + 1)).drop 1).map List.length

theorem fastDegreeCountsMemoThrough_getD {N i : Nat} (hi : i < N) :
    (fastDegreeCountsMemoThrough N).getD i 0 = fastDegreeCountMemo (i + 1) := by
  unfold fastDegreeCountsMemoThrough
  have hiDrop : i < (List.drop 1 (fastDegreeTable (N + 1))).length := by
    simp [fastDegreeTable_length, hi]
  have hiCounts : i < (List.map List.length (List.drop 1 (fastDegreeTable (N + 1)))).length := by
    simpa using hiDrop
  have hiTable : i + 1 < (fastDegreeTable (N + 1)).length := by
    simpa [fastDegreeTable_length, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using Nat.succ_lt_succ hi
  rw [list_getD_eq_getElem _ _ hiCounts]
  rw [List.getElem_map]
  rw [List.getElem_drop]
  have hiTable' : 1 + i < (fastDegreeTable (N + 1)).length := by
    simpa [Nat.add_comm] using hiTable
  have hrowSet :
      ((fastDegreeTable (N + 1))[1 + i]).toFinset = computedDegreeValues (i + 1) := by
    rw [← list_getD_eq_getElem (fastDegreeTable (N + 1)) [] hiTable']
    simpa [Nat.add_comm] using
      fastDegreeTable_getD_toFinset (N + 1) (i + 1) (Nat.succ_lt_succ hi)
  have hrowNodup : ((fastDegreeTable (N + 1))[1 + i]).Nodup := by
    rw [← list_getD_eq_getElem (fastDegreeTable (N + 1)) [] hiTable']
    simpa [Nat.add_comm] using
      fastDegreeTable_getD_nodup (N + 1) (i + 1) (Nat.succ_lt_succ hi)
  calc
    ((fastDegreeTable (N + 1))[1 + i]).length =
        ((fastDegreeTable (N + 1))[1 + i]).toFinset.card := by
          exact (List.toFinset_card_of_nodup hrowNodup).symm
    _ = (computedDegreeValues (i + 1)).card := by rw [hrowSet]
    _ = computedDegreeCount (i + 1) := rfl
    _ = fastDegreeCountMemo (i + 1) := computedDegreeCount_eq_fastDegreeCountMemo (i + 1)

theorem fastDegreeCountMemo_eq_countsMemoThrough_getD {N n : Nat}
    (hpos : 0 < n) (hN : n ≤ N) :
    fastDegreeCountMemo n = (fastDegreeCountsMemoThrough N).getD (n - 1) 0 := by
  cases n with
  | zero =>
      exact (Nat.not_lt_zero _ hpos).elim
  | succ i =>
      have hi : i < N := Nat.succ_le_iff.mp hN
      simpa using (fastDegreeCountsMemoThrough_getD (N := N) (i := i) hi).symm

theorem a199812_eq_of_fastDegreeCountsMemoThrough {N n value : Nat}
    (hpos : 0 < n) (hN : n ≤ N)
    (hcount : (fastDegreeCountsMemoThrough N).getD (n - 1) 0 = value) :
    a199812 n = value := by
  calc
    a199812 n = fastDegreeCountMemo n := a199812_eq_fastDegreeCountMemo n
    _ = (fastDegreeCountsMemoThrough N).getD (n - 1) 0 :=
      fastDegreeCountMemo_eq_countsMemoThrough_getD hpos hN
    _ = value := hcount

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
