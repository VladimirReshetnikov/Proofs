import NaturalDeduction.Calculus

/-!
# Gödel's finite-matrix collision formulas

The identifier `dugundji` retains a common later name for this family, but the
IPC construction formalized here is Gödel's 1932 formula.  `dugundji n` is the
disjunction of

`(pᵢ → pⱼ) ∧ (pⱼ → pᵢ)`

over all `0 ≤ i < j ≤ n`.  Thus it uses `n + 1` atoms.  The recursive
presentation below lists each unordered pair exactly once and is convenient
for kernel proofs about both derivability and Kripke forcing.
-/

namespace LeanProofs
namespace FiniteMatrixNoncharacterizability

open NaturalDeduction
open NaturalDeduction.Formula

/-- Uniform renaming of the atoms of a propositional formula. -/
def rename (r : α → β) : Formula α → Formula β
  | .atom a => .atom (r a)
  | .falsum => .falsum
  | p ⋏ q => rename r p ⋏ rename r q
  | p ⋎ q => rename r p ⋎ rename r q
  | p ⇒ q => rename r p ⇒ rename r q

@[simp] theorem rename_atom (r : α → β) (a : α) :
    rename r (.atom a) = .atom (r a) := rfl

@[simp] theorem rename_falsum (r : α → β) :
    rename r (.falsum : Formula α) = .falsum := rfl

@[simp] theorem rename_conj (r : α → β) (p q : Formula α) :
    rename r (p ⋏ q) = (rename r p ⋏ rename r q) := rfl

@[simp] theorem rename_disj (r : α → β) (p q : Formula α) :
    rename r (p ⋎ q) = (rename r p ⋎ rename r q) := rfl

@[simp] theorem rename_impl (r : α → β) (p q : Formula α) :
    rename r (p ⇒ q) = (rename r p ⇒ rename r q) := rfl

/-- Biconditional, expressed in the primitive connectives of the calculus. -/
def biconditional (p q : Formula α) : Formula α :=
  (p ⇒ q) ⋏ (q ⇒ p)

/-- The row comparing the new atom `pⱼ` with `p₀, …, pₖ₋₁`. -/
def pairRow (j : Nat) : Nat → Formula Nat
  | 0 => .falsum
  | k + 1 => biconditional (.atom k) (.atom j) ⋎ pairRow j k

/-- Gödel's collision formula on atoms `p₀, …, pₙ`.

The `n = 0` value is an empty disjunction, represented by falsity. -/
def dugundji : Nat → Formula Nat
  | 0 => .falsum
  | n + 1 => pairRow (n + 1) (n + 1) ⋎ dugundji n

theorem intuitionistic_identity (p : Formula α) :
    IntuitionisticallyDerives [] (p ⇒ p) := by
  apply Derives.impIntro
  exact Derives.assumption (by simp)

theorem intuitionistic_renamed_biconditional_of_eq (r : Nat → Nat) {i j : Nat}
    (h : r i = r j) :
    IntuitionisticallyDerives []
      (rename r (biconditional (.atom i) (.atom j))) := by
  simp only [biconditional, rename_conj, rename_impl, rename_atom]
  rw [h]
  exact Derives.andIntro
    (intuitionistic_identity (.atom (r j)))
    (intuitionistic_identity (.atom (r j)))

theorem intuitionistic_renamed_pairRow_of_eq (r : Nat → Nat) (j : Nat)
    {i k : Nat} (hi : i < k) (h : r i = r j) :
    IntuitionisticallyDerives [] (rename r (pairRow j k)) := by
  induction k with
  | zero => exact (Nat.not_lt_zero _ hi).elim
  | succ k ih =>
      simp only [pairRow, rename_disj]
      rcases Nat.lt_add_one_iff_lt_or_eq.mp hi with hik | rfl
      · exact Derives.orIntroRight (ih hik)
      · exact Derives.orIntroLeft
          (intuitionistic_renamed_biconditional_of_eq r h)

/-- Identifying any two of its atoms turns Gödel's formula into an IPC
theorem.  This is the atom-renaming step that lets theorem-level soundness—not
the stronger preservation of arbitrary sequents—drive the matrix argument. -/
theorem intuitionistic_renamed_dugundji_of_collision (r : Nat → Nat)
    {i j n : Nat} (hij : i < j) (hjn : j ≤ n) (h : r i = r j) :
    IntuitionisticallyDerives [] (rename r (dugundji n)) := by
  induction n with
  | zero => exact (Nat.not_lt_zero _ (Nat.lt_of_lt_of_le hij hjn)).elim
  | succ n ih =>
      simp only [dugundji, rename_disj]
      rcases Nat.lt_or_eq_of_le hjn with hjlt | rfl
      · exact Derives.orIntroRight (ih (Nat.lt_succ_iff.mp hjlt))
      · exact Derives.orIntroLeft
          (intuitionistic_renamed_pairRow_of_eq r (n + 1) hij h)

end FiniteMatrixNoncharacterizability
end LeanProofs
