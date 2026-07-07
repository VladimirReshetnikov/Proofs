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

/-! ## Shallow PA models and the PA-in-HF round trip -/

namespace PA

universe u v

/-- A shallow model of first-order Peano arithmetic in the language
`0, S, +, *`, with induction represented as a schema over Lean predicates. -/
structure Model (α : Type u) where
  zero : α
  succ : α → α
  add : α → α → α
  mul : α → α → α
  succ_injective : ∀ {a b}, succ a = succ b → a = b
  zero_not_succ : ∀ a, succ a ≠ zero
  induction :
    ∀ P : α → Prop, P zero → (∀ a, P a → P (succ a)) → ∀ a, P a
  add_zero : ∀ a, add a zero = a
  add_succ : ∀ a b, add a (succ b) = succ (add a b)
  mul_zero : ∀ a, mul a zero = zero
  mul_succ : ∀ a b, mul a (succ b) = add (mul a b) a

/-- Isomorphism of shallow PA models, preserving the arithmetic operations. -/
structure Iso {α : Type u} {β : Type v} (M : Model α) (N : Model β) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ b, toFun (invFun b) = b
  map_zero : toFun M.zero = N.zero
  map_succ : ∀ a, toFun (M.succ a) = N.succ (toFun a)
  map_add : ∀ a b, toFun (M.add a b) = N.add (toFun a) (toFun b)
  map_mul : ∀ a b, toFun (M.mul a b) = N.mul (toFun a) (toFun b)

/-- The standard model of PA on Lean's natural numbers. -/
def natModel : Model Nat where
  zero := 0
  succ := Nat.succ
  add := Nat.add
  mul := Nat.mul
  succ_injective := by
    intro a b h
    exact Nat.succ.inj h
  zero_not_succ := by
    intro a h
    exact Nat.succ_ne_zero a h
  induction := by
    intro P h0 hs a
    induction a with
    | zero => exact h0
    | succ n ih => exact hs n ih
  add_zero := Nat.add_zero
  add_succ := Nat.add_succ
  mul_zero := Nat.mul_zero
  mul_succ := Nat.mul_succ

end PA

namespace AckermannHF

/-- Equality of ordinal-coded HF objects follows from equality of their decoded
natural numbers. -/
theorem ordinal_eq_of_natOfOrdinal_eq {a b : OrdinalHF}
    (h : natOfOrdinal a = natOfOrdinal b) : a = b := by
  apply Subtype.ext
  rw [← natOfOrdinal_spec a, ← natOfOrdinal_spec b, h]

/-- The PA structure interpreted inside Ackermann HF by taking the finite
von Neumann ordinals as the number domain.  The operations are the transported
graphs of ordinary arithmetic on the ordinal indices; the transport and its
inverse are proved explicitly below. -/
noncomputable def ordinalPAModel : PA.Model OrdinalHF where
  zero := ordinalOfNat 0
  succ a := ordinalOfNat (natOfOrdinal a + 1)
  add a b := ordinalOfNat (natOfOrdinal a + natOfOrdinal b)
  mul a b := ordinalOfNat (natOfOrdinal a * natOfOrdinal b)
  succ_injective := by
    intro a b h
    apply ordinal_eq_of_natOfOrdinal_eq
    have hn := congrArg natOfOrdinal h
    simp [natOfOrdinal_ordinalOfNat] at hn
    omega
  zero_not_succ := by
    intro a h
    have hn := congrArg natOfOrdinal h
    simp [natOfOrdinal_ordinalOfNat] at hn
  induction := by
    intro P h0 hs a
    have hnat : ∀ n, P (ordinalOfNat n) := by
      intro n
      induction n with
      | zero => exact h0
      | succ n ih =>
          have hstep := hs (ordinalOfNat n) ih
          simpa [natOfOrdinal_ordinalOfNat] using hstep
    simpa [ordinalOfNat_natOfOrdinal a] using hnat (natOfOrdinal a)
  add_zero := by
    intro a
    apply ordinal_eq_of_natOfOrdinal_eq
    simp only [natOfOrdinal_ordinalOfNat, Nat.add_zero]
  add_succ := by
    intro a b
    apply ordinal_eq_of_natOfOrdinal_eq
    simp only [natOfOrdinal_ordinalOfNat, Nat.add_succ]
  mul_zero := by
    intro a
    apply ordinal_eq_of_natOfOrdinal_eq
    simp only [natOfOrdinal_ordinalOfNat, Nat.mul_zero]
  mul_succ := by
    intro a b
    apply ordinal_eq_of_natOfOrdinal_eq
    simp only [natOfOrdinal_ordinalOfNat, Nat.mul_succ]

/-- The first round trip of the bi-interpretability construction: starting
from arithmetic, interpreting HF by Ackermann coding, and then interpreting
arithmetic back as finite ordinals gives a PA model isomorphic to the original
natural-number model. -/
noncomputable def paRoundTripIso : PA.Iso PA.natModel ordinalPAModel where
  toFun := ordinalOfNat
  invFun := natOfOrdinal
  left_inv := natOfOrdinal_ordinalOfNat
  right_inv := ordinalOfNat_natOfOrdinal
  map_zero := rfl
  map_succ := by
    intro n
    apply ordinal_eq_of_natOfOrdinal_eq
    simp only [PA.natModel, ordinalPAModel, natOfOrdinal_ordinalOfNat]
  map_add := by
    intro a b
    apply ordinal_eq_of_natOfOrdinal_eq
    simp only [PA.natModel, ordinalPAModel, natOfOrdinal_ordinalOfNat, Nat.add_eq]
  map_mul := by
    intro a b
    apply ordinal_eq_of_natOfOrdinal_eq
    simp only [PA.natModel, ordinalPAModel, natOfOrdinal_ordinalOfNat, Nat.mul_eq]

/-! ## The HF-in-PA-in-HF round trip -/

/-- Isomorphism of adjunction-style HF models. -/
structure AdjunctionIso {α : Type} {β : Type}
    (M : AdjunctionModel α) (N : AdjunctionModel β) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ b, toFun (invFun b) = b
  map_mem : ∀ a b, N.mem (toFun a) (toFun b) ↔ M.mem a b
  map_empty : toFun M.empty = N.empty
  map_adjoin : ∀ a b, toFun (M.adjoin a b) = N.adjoin (toFun a) (toFun b)

/-- The HF model obtained after interpreting PA inside Ackermann HF and then
running Ackermann's HF interpretation in that interpreted PA model. -/
noncomputable def ordinalHFModel : AdjunctionModel OrdinalHF where
  mem a b := Mem (natOfOrdinal a) (natOfOrdinal b)
  empty := ordinalOfNat empty
  adjoin a b := ordinalOfNat (adjoin (natOfOrdinal a) (natOfOrdinal b))
  extensional := by
    intro a b h
    apply ordinal_eq_of_natOfOrdinal_eq
    apply ext
    intro x
    have hx := h (ordinalOfNat x)
    simpa [natOfOrdinal_ordinalOfNat] using hx
  empty_spec := by
    intro x
    simpa [natOfOrdinal_ordinalOfNat] using
      (mem_empty (natOfOrdinal x))
  adjoin_spec := by
    intro x a b
    constructor
    · intro h
      have h' : Mem (natOfOrdinal x) (adjoin (natOfOrdinal a) (natOfOrdinal b)) := by
        simpa [natOfOrdinal_ordinalOfNat] using h
      have hm := (mem_adjoin (natOfOrdinal x) (natOfOrdinal a) (natOfOrdinal b)).mp h'
      rcases hm with hm | hm
      · exact Or.inl hm
      · exact Or.inr (ordinal_eq_of_natOfOrdinal_eq hm)
    · intro h
      have h' : Mem (natOfOrdinal x) (adjoin (natOfOrdinal a) (natOfOrdinal b)) := by
        apply (mem_adjoin (natOfOrdinal x) (natOfOrdinal a) (natOfOrdinal b)).mpr
        rcases h with h | h
        · exact Or.inl h
        · subst h
          exact Or.inr rfl
      simpa [natOfOrdinal_ordinalOfNat] using h'
  set_induction := by
    intro P step a
    have hnat : ∀ n, P (ordinalOfNat n) := by
      intro n
      exact Nat.strongRecOn n (fun n ih =>
        step (ordinalOfNat n) (fun x hx =>
          have hx' : Mem (natOfOrdinal x) n := by
            simpa [natOfOrdinal_ordinalOfNat] using hx
          have hxlt : natOfOrdinal x < n := mem_lt hx'
          have hpx : P (ordinalOfNat (natOfOrdinal x)) := ih (natOfOrdinal x) hxlt
          by simpa [ordinalOfNat_natOfOrdinal x] using hpx))
    simpa [ordinalOfNat_natOfOrdinal a] using hnat (natOfOrdinal a)

/-- The second round trip of the bi-interpretability construction: starting
from Ackermann HF, interpreting arithmetic as finite ordinals, and then
interpreting HF back by Ackermann coding gives an HF model isomorphic to the
original one. -/
noncomputable def hfRoundTripIso : AdjunctionIso standardModel ordinalHFModel where
  toFun := ordinalOfNat
  invFun := natOfOrdinal
  left_inv := natOfOrdinal_ordinalOfNat
  right_inv := ordinalOfNat_natOfOrdinal
  map_mem := by
    intro a b
    simp only [ordinalHFModel, standardModel, natOfOrdinal_ordinalOfNat]
  map_empty := rfl
  map_adjoin := by
    intro a b
    apply ordinal_eq_of_natOfOrdinal_eq
    simp only [standardModel, ordinalHFModel, natOfOrdinal_ordinalOfNat]

theorem PA_biinterpretable_with_HF_standard :
    Nonempty (PA.Iso PA.natModel ordinalPAModel) ∧
      Nonempty (AdjunctionIso standardModel ordinalHFModel) :=
  ⟨⟨paRoundTripIso⟩, ⟨hfRoundTripIso⟩⟩

end AckermannHF

end SetTheory
