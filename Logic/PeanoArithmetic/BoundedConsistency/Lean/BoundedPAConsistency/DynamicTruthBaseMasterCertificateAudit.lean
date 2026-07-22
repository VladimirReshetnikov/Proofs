import BoundedPAConsistency.DynamicTruthBaseMasterCertificate

/-!
# Audit for the complete dynamic-truth base certificate

The checks below ensure that the packed derivation targets the concrete
six-field family sentence and that its value proves precisely the family code
at model zero.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthBaseMasterCertificateAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthCertificateFieldFamily
open LeanProofs.BoundedPAConsistency.DynamicTruthBaseMasterCertificate
open LeanProofs.BoundedPAConsistency.PrimitiveRecursiveTruthCertificate

#check paRestrictedConsistencyFormula_zero_eq_base
#check compiledDynamicTruthBaseCertificateProof
#check compiledDynamicTruthBaseCertificateProof_isPAProof
#check exists_compiledDynamicTruthBaseCertificateProof

#print axioms paRestrictedConsistencyFormula_zero_eq_base
#print axioms compiledDynamicTruthBaseCertificateProof
#print axioms compiledDynamicTruthBaseCertificateProof_isPAProof
#print axioms exists_compiledDynamicTruthBaseCertificateProof

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

noncomputable section

example : Peano.internalize V ⊢!
    ((compiledDynamicTruthCertificateFamily (V := V)).fields 0).sentence :=
  compiledDynamicTruthBaseCertificateProof (V := V)

example : ∃ d : V, Proof Peano d
    ((compiledDynamicTruthCertificateFamily (V := V)).code 0) :=
  exists_compiledDynamicTruthBaseCertificateProof (V := V)

end

end LeanProofs.BoundedPAConsistency.DynamicTruthBaseMasterCertificateAudit
