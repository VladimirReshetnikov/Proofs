import BoundedPAConsistency.Internal
import Foundation.FirstOrder.Bootstrapping.Syntax.Formula.Basic

/-!
# Structural induction on nonstandard formula codes in models of PA

Foundation's packaged `IsUFormula.induction1` is calibrated to predicates at
the first arithmetical-hierarchy level.  Fixed-level partial truth has a higher
(but externally fixed) complexity.  Full PA supplies the corresponding
induction instance, so `Internal.inductionInPeanoModel` can be specialized to
the formula-code fixed point.

The theorem below deliberately exposes the familiar eight syntax cases.  It
does not decode a model element into a Lean formula, and therefore applies to
nonstandard formula codes in nonstandard PA models.
-/

namespace LeanProofs.BoundedPAConsistency.ModelFormulaInduction

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.Internal

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable {L : Language} [L.Encodable] [L.LORDefinable]

local instance : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory hPA

/-- Structural induction for an invariant at any fixed positive hierarchy
level inside an arbitrary model of full PA. -/
theorem uformula_inductionInPeanoModel
    {Γ : SigmaPiDelta} {m : ℕ} {P : V → Prop}
    (hP : Γ-[m + 1]-Predicate P)
    (hrel : ∀ k r v, L.IsRel k r → IsUTermVec L k v → P (^rel k r v))
    (hnrel : ∀ k r v, L.IsRel k r → IsUTermVec L k v → P (^nrel k r v))
    (hverum : P ^⊤)
    (hfalsum : P ^⊥)
    (hand : ∀ p q, IsUFormula L p → IsUFormula L q →
      P p → P q → P (p ^⋏ q))
    (hor : ∀ p q, IsUFormula L p → IsUFormula L q →
      P p → P q → P (p ^⋎ q))
    (hall : ∀ p, IsUFormula L p → P p → P (^∀ p))
    (hexs : ∀ p, IsUFormula L p → P p → P (^∃ p)) :
    ∀ p, IsUFormula L p → P p := by
  apply inductionInPeanoModel
      (FormalizedFormula.construction (V := V) L) ![] hP
  intro C hC x hx
  rcases hx with
      (⟨k, r, v, hkr, hv, rfl⟩ |
       ⟨k, r, v, hkr, hv, rfl⟩ |
       ⟨n, rfl⟩ |
       ⟨n, rfl⟩ |
       ⟨p, q, hp, hq, rfl⟩ |
       ⟨p, q, hp, hq, rfl⟩ |
       ⟨p, hp, rfl⟩ |
       ⟨p, hp, rfl⟩)
  · exact hrel k r v hkr hv
  · exact hnrel k r v hkr hv
  · exact hverum
  · exact hfalsum
  · exact hand p q (hC p hp).1 (hC q hq).1
      (hC p hp).2 (hC q hq).2
  · exact hor p q (hC p hp).1 (hC q hq).1
      (hC p hp).2 (hC q hq).2
  · exact hall p (hC p hp).1 (hC p hp).2
  · exact hexs p (hC p hp).1 (hC p hp).2

end LeanProofs.BoundedPAConsistency.ModelFormulaInduction
