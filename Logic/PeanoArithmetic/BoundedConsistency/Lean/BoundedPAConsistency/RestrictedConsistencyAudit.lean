import BoundedPAConsistency.RestrictedConsistency

/-!
# Kernel audit for the internal restricted-consistency endpoint

The examples verify the advertised hierarchy classes in an arbitrary model;
the checks and axiom reports keep the nonstandard-code erasure boundary
visible without adding diagnostic output to the library module.
-/

namespace LeanProofs.BoundedPAConsistency.RestrictedConsistencyAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* ISigma 1]
variable {L : Language} [L.Encodable] [L.LORDefinable]
variable (T : Theory L) [Theory.Δ₁ T]

example : HierarchySymbol.DefinableRel₃ (V := V)
    HierarchySymbol.deltaOne (RestrictedProof T) := inferInstance

example : HierarchySymbol.DefinableRel (V := V)
    HierarchySymbol.sigmaOne (RestrictedProvable T) := inferInstance

example : HierarchySymbol.DefinablePred (V := V)
    HierarchySymbol.piOne (RestrictedConsistent T) := inferInstance

#check restrictedProofDef
#check restrictedProvableDef
#check restrictedConsistentDef
#check restrictedConsistencySentence
#check paRestrictedConsistencySentence
#check eval_restrictedConsistencySentence_iff
#check RestrictedProof.erase
#check RestrictedProvable.erase
#check bounded_formula_of_restrictedProof

#print axioms RestrictedProof.defined
#print axioms RestrictedProvable.defined
#print axioms RestrictedConsistent.defined
#print axioms eval_restrictedConsistencySentence_iff
#print axioms RestrictedProof.erase
#print axioms bounded_formula_of_restrictedProof

end LeanProofs.BoundedPAConsistency.RestrictedConsistencyAudit
