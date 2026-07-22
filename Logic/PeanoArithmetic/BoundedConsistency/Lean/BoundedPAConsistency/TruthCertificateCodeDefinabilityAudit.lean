import BoundedPAConsistency.TruthCertificateCodeDefinability

/-!
# Kernel audit for truth-certificate code definability

The checks below keep the compositional graph theorem visible independently
of the bounded-consistency facade.  The example records its intended use:
five concrete field graphs discharge the exact `family.code` premise expected
by the primitive-recursive selector bridge.
-/

namespace LeanProofs.BoundedPAConsistency.TruthCertificateCodeDefinabilityAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.PrimitiveRecursiveTruthCertificate
open LeanProofs.BoundedPAConsistency.TruthCertificateCodeDefinability

#check assembleTruthCertificateCode
#check assembleTruthCertificateCode_definable
#check truthCertificateCompilerStateCode
#check truthCertificateCompilerStateCode_definable
#check paRestrictedConsistencyFormulaCode_definable
#check PATruthCertificateFamily.code_eq_assemble
#check PATruthCertificateFamily.code_definable_of_fields
#check paRestrictedConsistencyProofSelectorIn_of_primitiveRecursivePackage_and_fieldCodes
#check paRestrictedConsistencyProofSelectorIn_of_typedPrimitiveRecursivePackage_and_fieldCodes

#print axioms assembleTruthCertificateCode_definable
#print axioms truthCertificateCompilerStateCode_definable
#print axioms paRestrictedConsistencyFormulaCode_definable
#print axioms PATruthCertificateFamily.code_eq_assemble
#print axioms PATruthCertificateFamily.code_definable_of_fields
#print axioms paRestrictedConsistencyProofSelectorIn_of_primitiveRecursivePackage_and_fieldCodes
#print axioms paRestrictedConsistencyProofSelectorIn_of_typedPrimitiveRecursivePackage_and_fieldCodes

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-- A concrete family only has to expose the five dynamic code graphs; the
fixed bounded-consistency target is filled in by the theorem. -/
example (family : PATruthCertificateFamily (V := V))
    (hlocal : HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦ (family.localStep n).val))
    (hcross : HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦ (family.crossLevel n).val))
    (hshift : HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦ (family.shiftInvariant n).val))
    (hsubst : HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦ (family.substitutionInvariant n).val))
    (haxiom : HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦ (family.axiomSound n).val)) :
    HierarchySymbol.sigmaOne.DefinableFunction₁ family.code :=
  family.code_definable_of_fields hlocal hcross hshift hsubst haxiom

end LeanProofs.BoundedPAConsistency.TruthCertificateCodeDefinabilityAudit
