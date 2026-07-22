import BoundedPAConsistency.PrimitiveRecursiveTruthCertificate

/-!
# Kernel audit for represented primitive-recursive truth certificates

These checks expose the concrete bridge from Foundation's HFS computation
sequences to the already existing arbitrary-model proof selector.  In
particular, the package witness is the represented iterator's result and is
also required to be an actual PA proof code for the typed six-field master
certificate.
-/

namespace LeanProofs.BoundedPAConsistency.PrimitiveRecursiveTruthCertificateAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.PrimitiveRecursiveTruthCertificate
open LeanProofs.BoundedPAConsistency.UniformInternalProvability

#check paRestrictedConsistencyFormula
#check paRestrictedConsistencyFormula_val
#check PATruthCertificateFamily
#check PATruthCertificateFamily.fields
#check PATruthCertificateFamily.code
#check PATruthCertificateFamily.toTProof
#check PATruthCertificateFamily.exists_finalProof_of_masterProof
#check PrimitiveRecursivePackage
#check primitiveRecursivePackage_definable
#check RealizesTypedCertificateSuccessor
#check paRestrictedConsistencyProofSelectorIn_of_primitiveRecursivePackage
#check paRestrictedConsistencyProofSelectorIn_of_typedPrimitiveRecursivePackage

#print axioms paRestrictedConsistencyFormula_val
#print axioms PATruthCertificateFamily.exists_finalProof_of_masterProof
#print axioms primitiveRecursivePackage_definable
#print axioms paRestrictedConsistencyProofSelectorIn_of_primitiveRecursivePackage
#print axioms paRestrictedConsistencyProofSelectorIn_of_typedPrimitiveRecursivePackage

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]
variable [V↓[ℒₒᵣ] ⊧* Peano]

/-- The public theorem can be used directly with a genuinely represented
iterator and the typed successor compiler; no abstract package relation or
separate final-field extractor remains at the call site. -/
example {k : ℕ} {blueprint : PR.Blueprint k}
    (compiler : PR.Construction V blueprint) (parameters : Fin k → V)
    (family : PATruthCertificateFamily (V := V))
    (masterCodeDefinable :
      HierarchySymbol.sigmaOne.DefinableFunction₁ family.code)
    (baseCertificate :
      Proof Peano (compiler.zero parameters) (family.code 0))
    (successorRealization :
      RealizesTypedCertificateSuccessor compiler parameters family) :
    PARestrictedConsistencyProofSelectorIn V :=
  paRestrictedConsistencyProofSelectorIn_of_typedPrimitiveRecursivePackage
    compiler parameters family masterCodeDefinable baseCertificate
      successorRealization

end LeanProofs.BoundedPAConsistency.PrimitiveRecursiveTruthCertificateAudit
