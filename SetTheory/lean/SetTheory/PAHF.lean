/-
  PAHF.lean

  Peano arithmetic and hereditary finite sets.

  This module starts the formalization of the classical bi-interpretability
  route:

  * interpret hereditary finite sets in arithmetic by Ackermann's bit coding;
  * interpret arithmetic in hereditary finite sets by the finite von Neumann
    ordinals;
  * prove the round trips by explicit isomorphisms.

  The first section below is intentionally modest and reusable: it builds the
  Ackermann membership relation on `Nat` and proves the finite-set axioms that
  only need bit arithmetic.  Later sections use these lemmas as the semantic
  core of the interpretation data.
-/
import SetTheory.Fol

namespace SetTheory

/-! ## Ackermann-coded hereditary finite sets -/

namespace AckermannHF

/-- `Mem x y` means: in Ackermann's coding, the set coded by `x` is an element
of the set coded by `y`.  Equivalently, the `x`-th binary digit of `y` is set. -/
def Mem (x y : Nat) : Prop := y.testBit x = true

/-- The empty set is coded by `0`. -/
def empty : Nat := 0

/-- Adjunction/insert: add the element coded by `x` to the set coded by `a`. -/
def adjoin (a x : Nat) : Nat := a ||| 2 ^ x

theorem mem_empty (x : Nat) : ¬ Mem x empty := by
  simp [Mem, empty, Nat.zero_testBit]

theorem mem_adjoin (x a b : Nat) : Mem x (adjoin a b) ↔ Mem x a ∨ x = b := by
  unfold Mem adjoin
  rw [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true]
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr ((of_decide_eq_true h).symm)
  · intro h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (decide_eq_true h.symm)

theorem ext {a b : Nat} (h : ∀ x, Mem x a ↔ Mem x b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro x
  have hx := h x
  cases ha : a.testBit x <;> cases hb : b.testBit x <;>
    simp [Mem, ha, hb] at hx ⊢

theorem two_pow_le_of_mem {x y : Nat} (h : Mem x y) : 2 ^ x ≤ y := by
  apply Nat.le_of_testBit
  intro i hi
  rw [Nat.testBit_two_pow] at hi
  have hix : x = i := of_decide_eq_true hi
  subst hix
  exact h

theorem mem_lt {x y : Nat} (h : Mem x y) : x < y :=
  Nat.lt_of_lt_of_le Nat.lt_two_pow_self (two_pow_le_of_mem h)

/-- Set induction for the Ackermann-coded HF membership relation. -/
theorem induction (P : Nat → Prop)
    (step : ∀ a, (∀ x, Mem x a → P x) → P a) :
    ∀ a, P a := by
  intro a
  exact Nat.strongRecOn a (fun a ih =>
    step a (fun x hx => ih x (mem_lt hx)))

/-- A compact semantic bundle for the usual adjunction presentation of HF. -/
structure AdjunctionModel (α : Type) where
  mem : α → α → Prop
  empty : α
  adjoin : α → α → α
  extensional :
    ∀ {a b}, (∀ x, mem x a ↔ mem x b) → a = b
  empty_spec :
    ∀ x, ¬ mem x empty
  adjoin_spec :
    ∀ x a b, mem x (adjoin a b) ↔ mem x a ∨ x = b
  set_induction :
    ∀ P : α → Prop, (∀ a, (∀ x, mem x a → P x) → P a) → ∀ a, P a

/-- The standard Ackermann-coded model of hereditary finite sets. -/
def standardModel : AdjunctionModel Nat where
  mem := Mem
  empty := empty
  adjoin := adjoin
  extensional := by
    intro a b h
    exact ext h
  empty_spec := mem_empty
  adjoin_spec := mem_adjoin
  set_induction := induction

/-! ## The finite von Neumann ordinals inside Ackermann HF -/

/-- Ackermann code of the finite von Neumann ordinal `n`.

This is deliberately just the recursive set-theoretic construction:
`0 = ∅` and `n+1 = n ∪ {n}`.  The fact that it is an embedding, and the
description of its members, are separate theorems below. -/
def ordinalCode : Nat → Nat
  | 0 => empty
  | n+1 => adjoin (ordinalCode n) (ordinalCode n)

theorem ordinalCode_zero : ordinalCode 0 = empty := rfl

theorem ordinalCode_succ (n : Nat) :
    ordinalCode (n+1) = adjoin (ordinalCode n) (ordinalCode n) := rfl

theorem mem_ordinalCode_succ (x n : Nat) :
    Mem x (ordinalCode (n+1)) ↔ Mem x (ordinalCode n) ∨ x = ordinalCode n := by
  rw [ordinalCode_succ, mem_adjoin]

theorem mem_ordinalCode_iff (x n : Nat) :
    Mem x (ordinalCode n) ↔ ∃ k, k < n ∧ x = ordinalCode k := by
  induction n with
  | zero =>
      constructor
      · intro h
        exact False.elim (mem_empty x h)
      · intro h
        rcases h with ⟨k, hk, _⟩
        omega
  | succ n ih =>
      rw [mem_ordinalCode_succ]
      constructor
      · intro h
        rcases h with h | h
        · rcases ih.mp h with ⟨k, hk, hx⟩
          exact ⟨k, by omega, hx⟩
        · exact ⟨n, by omega, h⟩
      · intro h
        rcases h with ⟨k, hk, hx⟩
        have hle : k ≤ n := Nat.lt_succ_iff.mp hk
        rcases Nat.lt_or_eq_of_le hle with hlt | heq
        · exact Or.inl (ih.mpr ⟨k, hlt, hx⟩)
        · exact Or.inr (by subst heq; exact hx)

theorem ordinalCode_mem_of_lt {k n : Nat} (h : k < n) :
    Mem (ordinalCode k) (ordinalCode n) :=
  (mem_ordinalCode_iff (ordinalCode k) n).mpr ⟨k, h, rfl⟩

theorem not_mem_self (a : Nat) : ¬ Mem a a := fun h =>
  Nat.lt_irrefl a (mem_lt h)

theorem ordinalCode_injective {m n : Nat}
    (h : ordinalCode m = ordinalCode n) : m = n := by
  rcases Nat.lt_trichotomy m n with hlt | heq | hgt
  · have hm : Mem (ordinalCode m) (ordinalCode n) := ordinalCode_mem_of_lt hlt
    rw [← h] at hm
    exact False.elim (not_mem_self (ordinalCode m) hm)
  · exact heq
  · have hn : Mem (ordinalCode n) (ordinalCode m) := ordinalCode_mem_of_lt hgt
    rw [h] at hn
    exact False.elim (not_mem_self (ordinalCode n) hn)

def IsOrdinalCode (a : Nat) : Prop := ∃ n, ordinalCode n = a

/-- The interpreted PA domain inside Ackermann HF: the finite von Neumann
ordinals, represented by their Ackermann codes. -/
def OrdinalHF : Type := {a : Nat // IsOrdinalCode a}

def ordinalOfNat (n : Nat) : OrdinalHF := ⟨ordinalCode n, ⟨n, rfl⟩⟩

noncomputable def natOfOrdinal (a : OrdinalHF) : Nat := a.property.choose

theorem ordinalOfNat_val (n : Nat) :
    (ordinalOfNat n).val = ordinalCode n := rfl

theorem natOfOrdinal_spec (a : OrdinalHF) :
    ordinalCode (natOfOrdinal a) = a.val :=
  a.property.choose_spec

theorem natOfOrdinal_ordinalOfNat (n : Nat) :
    natOfOrdinal (ordinalOfNat n) = n :=
  ordinalCode_injective (natOfOrdinal_spec (ordinalOfNat n))

theorem ordinalOfNat_natOfOrdinal (a : OrdinalHF) :
    ordinalOfNat (natOfOrdinal a) = a := by
  apply Subtype.ext
  exact natOfOrdinal_spec a

end AckermannHF

end SetTheory
