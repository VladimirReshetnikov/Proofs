import BoundedPAConsistency.ModelFormulaInduction

/-! Kernel audit for higher-level structural induction on formula codes. -/

namespace LeanProofs.BoundedPAConsistency.ModelFormulaInductionAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.ModelFormulaInduction

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable {L : Language} [L.Encodable] [L.LORDefinable]

local instance : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory hPA

#check uformula_inductionInPeanoModel

example {Γ : SigmaPiDelta} {m : ℕ} {P : V → Prop}
    (hP : Γ-[m + 1]-Predicate P)
    (hrel : ∀ k r v, L.IsRel k r → IsUTermVec L k v → P (^rel k r v))
    (hnrel : ∀ k r v, L.IsRel k r → IsUTermVec L k v → P (^nrel k r v))
    (hverum : P ^⊤) (hfalsum : P ^⊥)
    (hand : ∀ p q, IsUFormula L p → IsUFormula L q →
      P p → P q → P (p ^⋏ q))
    (hor : ∀ p q, IsUFormula L p → IsUFormula L q →
      P p → P q → P (p ^⋎ q))
    (hall : ∀ p, IsUFormula L p → P p → P (^∀ p))
    (hexs : ∀ p, IsUFormula L p → P p → P (^∃ p)) :
    ∀ p, IsUFormula L p → P p :=
  uformula_inductionInPeanoModel hP hrel hnrel hverum hfalsum
    hand hor hall hexs

#print axioms uformula_inductionInPeanoModel

end LeanProofs.BoundedPAConsistency.ModelFormulaInductionAudit
