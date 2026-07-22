import BoundedPAConsistency.DynamicTruthMemberValidityTemplate

/-!
# Audit: compiled member-validity elimination

This audit exposes the fixed source derivation, exact translation, arbitrary
model-coded compiler endpoint, and nonstandard-orbit specialization.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthMemberValidityTemplateAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthOrbit
open LeanProofs.BoundedPAConsistency.DynamicTruthMemberValidityTemplate

#check apply₄
#check acceptedCertificateBody
#check acceptedCertificateAtRecord
#check memberValidityLocalLaw
#check memberValiditySentence
#check sourceProof
#check translate_apply₄
#check acceptedCertificateAtRecordFormula
#check memberValidityFormula
#check translate_acceptedCertificateAtRecord
#check translate_memberValiditySentence
#check compiledMemberValidityProof
#check compiledMemberValidityProof_isPAProof
#check orbitMemberValidityFormula
#check orbitMemberValidityProof
#check orbitMemberValidityProof_isPAProof

#print axioms sourceProof
#print axioms translate_acceptedCertificateAtRecord
#print axioms translate_memberValiditySentence
#print axioms compiledMemberValidityProof
#print axioms compiledMemberValidityProof_isPAProof
#print axioms orbitMemberValidityProof
#print axioms orbitMemberValidityProof_isPAProof

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-- The public endpoint supplies a represented PA proof for every ambient
model element, without a standardness assumption. -/
example (n : V) :
    Proof Peano (orbitMemberValidityProof n).val
      (orbitMemberValidityFormula n).val :=
  orbitMemberValidityProof_isPAProof n

/-- The orbit formula is definitionally specialized at the actual lower
truth predicate and the two consecutive model levels. -/
example (n : V) : orbitMemberValidityFormula n =
    memberValidityFormula (truthFormula n) (n + 1) (n + 1 + 1) := rfl

end LeanProofs.BoundedPAConsistency.DynamicTruthMemberValidityTemplateAudit
