import BoundedPAConsistency.DirectTruthCertificatePackage

/-! Kernel audit for direct existential truth-certificate packages. -/

namespace LeanProofs.BoundedPAConsistency.DirectTruthCertificatePackageAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.PrimitiveRecursiveTruthCertificate
open LeanProofs.BoundedPAConsistency.DirectTruthCertificatePackage
open LeanProofs.BoundedPAConsistency.UniformInternalProvability

#check DirectTruthCertificatePackage
#check directTruthCertificatePackage_definable
#check HasTypedTruthCertificateSuccessor
#check paRestrictedConsistencyProofSelectorIn_of_directTruthCertificates
#check paRestrictedConsistencyProofSelectorIn_of_directTypedTruthCertificates
#check paRestrictedConsistencyProofSelectorIn_of_directTypedTruthCertificates_and_fieldCodes

#print axioms directTruthCertificatePackage_definable
#print axioms paRestrictedConsistencyProofSelectorIn_of_directTruthCertificates
#print axioms paRestrictedConsistencyProofSelectorIn_of_directTypedTruthCertificates
#print axioms paRestrictedConsistencyProofSelectorIn_of_directTypedTruthCertificates_and_fieldCodes

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]
variable [V↓[ℒₒᵣ] ⊧* Peano]

/-- Public endpoint: no primitive-recursive proof-code function appears in
the assumptions. -/
example (family : PATruthCertificateFamily (V := V))
    (hcode : HierarchySymbol.sigmaOne.DefinableFunction₁ family.code)
    (hbase : Peano.internalize V ⊢! (family.fields 0).sentence)
    (hsucc : HasTypedTruthCertificateSuccessor family) :
    PARestrictedConsistencyProofSelectorIn V :=
  paRestrictedConsistencyProofSelectorIn_of_directTypedTruthCertificates
    family hcode hbase hsucc

end LeanProofs.BoundedPAConsistency.DirectTruthCertificatePackageAudit
