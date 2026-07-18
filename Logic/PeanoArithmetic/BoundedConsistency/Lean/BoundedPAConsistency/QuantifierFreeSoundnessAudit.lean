import BoundedPAConsistency.QuantifierFreeSoundness

/-!
# Kernel audit for rank-zero restricted-derivation soundness

The theorem checked here ranges over arbitrary elements of an arbitrary model
of PA.  In particular, neither the derivation nor its formula occurrences are
assumed to be standard codes.  Theory axioms remain behind the explicit
`hAx` premise so that the eventual PA-specific discharge can be audited
separately.
-/

namespace LeanProofs.BoundedPAConsistency.QuantifierFreeSoundnessAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency
open LeanProofs.BoundedPAConsistency.CodedHierarchy
open LeanProofs.BoundedPAConsistency.QuantifierFreeTruth
open LeanProofs.BoundedPAConsistency.QuantifierFreeSoundness

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

#check QFSequentTrue
#check QFSequentTrue.definable
#check restrictedDerivation_qf_sound
#check restrictedConsistent_zero_of_qf_axioms

example (T : Theory ℒₒᵣ) [T.Δ₁]
    (hAx : ∀ p : V, p ∈ T.Δ₁Class →
      IsQuantifierFreeCode p → QFTrue 0 0 p)
    {d : V} (hd : RestrictedDerivation T 0 d) :
    QFSequentTrue (fstIdx d) :=
  restrictedDerivation_qf_sound T hAx hd

#print axioms QFSequentTrue.definable
#print axioms restrictedDerivation_qf_sound
#print axioms restrictedConsistent_zero_of_qf_axioms

end LeanProofs.BoundedPAConsistency.QuantifierFreeSoundnessAudit
