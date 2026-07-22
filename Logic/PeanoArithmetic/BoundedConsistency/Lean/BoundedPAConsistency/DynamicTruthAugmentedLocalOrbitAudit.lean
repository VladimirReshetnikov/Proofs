import BoundedPAConsistency.DynamicTruthAugmentedLocalOrbit

/-! Assumption and type audit for the four-law dynamic local field. -/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthAugmentedLocalOrbitAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LeanProofs.BoundedPAConsistency.DynamicTruthAugmentedLocalOrbit

#check baseQuantifierFreeIntroductionFormula
#check baseQuantifierFreeIntroductionProof
#check baseAugmentedLocalBundle
#check baseAugmentedLocalBundleProof
#check baseAugmentedLocalBundleProof_isPAProof
#check modelIndexedAugmentedLocalBundle
#check modelIndexedAugmentedLocalBundle_zero
#check modelIndexedAugmentedLocalBundle_succ
#check proveModelIndexedAugmentedLocalBundleSuccFrom
#check modelIndexedAugmentedLocalBundleCode
#check modelIndexedAugmentedLocalBundleCode_definable

#print axioms baseQuantifierFreeIntroductionProof
#print axioms baseAugmentedLocalBundleProof
#print axioms baseAugmentedLocalBundleProof_isPAProof
#print axioms modelIndexedAugmentedLocalBundle_succ
#print axioms proveModelIndexedAugmentedLocalBundleSuccFrom
#print axioms modelIndexedAugmentedLocalBundleCode_definable

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

example : HierarchySymbol.sigmaOne.DefinableFunction₁
    (modelIndexedAugmentedLocalBundleCode (V := V)) :=
  modelIndexedAugmentedLocalBundleCode_definable

end LeanProofs.BoundedPAConsistency.DynamicTruthAugmentedLocalOrbitAudit
