import BoundedPAConsistency.RestrictedDerivation

/-!
# Kernel audit for the all-occurrences coded derivation predicate

Unlike the phase-one host datatype, this checker is a Delta-one least fixed
point interpreted in an arbitrary model of arithmetic.  The audit checks its
represented interface and the two structural facts needed later by partial
truth soundness.
-/

namespace LeanProofs.BoundedPAConsistency.RestrictedDerivationAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* ISigma 1]
variable {L : Language} [L.Encodable] [L.LORDefinable]
variable (T : Theory L) [Theory.Δ₁ T]

example : HierarchySymbol.DefinableRel (V := V)
    HierarchySymbol.deltaOne (RestrictedDerivation T) := inferInstance

#check restricted_case_iff
#check allBounded_of_restricted
#check erase

#print axioms RestrictedDerivation.defined
#print axioms restricted_case_iff
#print axioms allBounded_of_restricted
#print axioms erase

end LeanProofs.BoundedPAConsistency.RestrictedDerivationAudit
