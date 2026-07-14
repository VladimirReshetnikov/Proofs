import FiniteMatrixNoncharacterizability.Matrix
import FiniteMatrixNoncharacterizability.Kripke

/-!
# The familiar three-element Heyting chain

This module records the concrete example mentioned in the mathematical
explanation.  The chain is `⊥ < u < ⊤`; conjunction and disjunction are its
meet and join, implication is the Heyting implication, and only `⊤` is
designated.  It validates Gödel--Dummett prelinearity, although prelinearity is
not an IPC theorem.

We do not need, and do not assert here, the separate full soundness theorem for
this matrix.
-/

namespace LeanProofs
namespace FiniteMatrixNoncharacterizability

open NaturalDeduction
open NaturalDeduction.Formula

/-- The values `⊥ < u < ⊤` of the three-element Heyting chain. -/
inductive H3Value where
  | bottom
  | middle
  | top
  deriving DecidableEq, Repr

/-- Meet on the three-element chain. -/
def h3Conj : H3Value → H3Value → H3Value
  | .bottom, _ => .bottom
  | _, .bottom => .bottom
  | .middle, _ => .middle
  | _, .middle => .middle
  | .top, .top => .top

/-- Join on the three-element chain. -/
def h3Disj : H3Value → H3Value → H3Value
  | .top, _ => .top
  | _, .top => .top
  | .middle, _ => .middle
  | _, .middle => .middle
  | .bottom, .bottom => .bottom

/-- Heyting implication: `x ⇒ y = ⊤` when `x ≤ y`, and `y` otherwise. -/
def h3Impl : H3Value → H3Value → H3Value
  | .bottom, _ => .top
  | .middle, .bottom => .bottom
  | .middle, .middle => .top
  | .middle, .top => .top
  | .top, y => y

/-- The concrete `0 < u < 1` logical matrix, with only top designated. -/
def h3Matrix : LogicalMatrix H3Value where
  falsum := .bottom
  conj := h3Conj
  disj := h3Disj
  impl := h3Impl
  designated := fun x => x = .top

/-- Explicit evidence that the H3 carrier has three values. -/
def h3Encoding : FiniteEncoding H3Value 3 where
  encode
    | .bottom => 0
    | .middle => 1
    | .top => 2
  injective := by
    intro x y h
    cases x <;> cases y <;> simp_all

/-- Gödel--Dummett prelinearity for two distinguished atoms. -/
def prelinearityFormula : Formula Nat :=
  ((.atom 0 ⇒ .atom 1) ⋎ (.atom 1 ⇒ .atom 0))

/-- Exhausting the `3 × 3` assignments shows that H3 validates prelinearity. -/
theorem h3_validates_prelinearity : h3Matrix.Valid prelinearityFormula := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;>
    simp [LogicalMatrix.eval, prelinearityFormula,
      h3Matrix, h3Impl, h3Disj, h0, h1]

/-- The two-leaf branching Kripke model refutes prelinearity at its root. -/
theorem two_leaf_root_not_forces_prelinearity :
    ¬ (branchModel 2).Forces none prelinearityFormula := by
  intro h
  rcases h with h01 | h10
  · let w0 : Fin 2 := ⟨0, by omega⟩
    have h1 : (branchModel 2).Forces (some w0) (.atom 1) :=
      h01 (some w0) (by trivial) (by rfl)
    simp [w0, KripkeModel.Forces, branchModel, branchAtom] at h1
  · let w1 : Fin 2 := ⟨1, by omega⟩
    have h0 : (branchModel 2).Forces (some w1) (.atom 0) :=
      h10 (some w1) (by trivial) (by rfl)
    simp [w1, KripkeModel.Forces, branchModel, branchAtom] at h0

/-- Prelinearity is not derivable in intuitionistic propositional logic. -/
theorem prelinearity_not_intuitionistically_derivable :
    ¬ IntuitionisticallyDerives [] prelinearityFormula := by
  intro h
  have hforced := KripkeModel.intuitionistic_sound h (branchModel 2) none
    (by simp [KripkeModel.ForcesContext])
  exact two_leaf_root_not_forces_prelinearity hforced

/-- Thus H3 validates a formula that IPC does not prove. -/
theorem h3_validates_non_IPC_theorem :
    h3Matrix.Valid prelinearityFormula ∧
      ¬ IntuitionisticallyDerives [] prelinearityFormula :=
  ⟨h3_validates_prelinearity, prelinearity_not_intuitionistically_derivable⟩

end FiniteMatrixNoncharacterizability
end LeanProofs
