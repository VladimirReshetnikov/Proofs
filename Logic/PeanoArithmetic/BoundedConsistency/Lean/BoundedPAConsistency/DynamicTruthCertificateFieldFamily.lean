import BoundedPAConsistency.DynamicTruthAugmentedLocalOrbit
import BoundedPAConsistency.DynamicTruthCrossLevelOrbit
import BoundedPAConsistency.DynamicTruthShiftInvariantOrbit
import BoundedPAConsistency.DynamicTruthSubstitutionInvariantOrbit
import BoundedPAConsistency.DynamicTruthAxiomSoundnessOrbit
import BoundedPAConsistency.TruthCertificateCodeDefinability

/-!
# The assembled model-indexed dynamic truth certificate fields

The five independently developed field-code functions are assembled here into
one `PATruthCertificateFamily`.  Its final coordinate is not chosen here:
`PATruthCertificateFamily.fields` inserts the exact restricted-consistency
target by construction.

The local coordinate contains the three fixed-source certificate eliminators
and the independently compiled quantifier-free introduction anchor.  The
fourth law is essential for the valid-domain base cases of cross-level
structural induction.  This module establishes the concrete family shape and
its represented master-code graph; the remaining constructor-wise structural
derivations are supplied in later proof-producing layers.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthCertificateFieldFamily

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.PrimitiveRecursiveTruthCertificate
open LeanProofs.BoundedPAConsistency.DynamicTruthAugmentedLocalOrbit
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelOrbit
open LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantOrbit
open LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantOrbit
open LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessOrbit

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-- The five concrete, total model-indexed fields currently available for the
dynamic truth hierarchy.  The local coordinate includes the quantifier-free
introduction law as well as the three certificate eliminators; this anchor is
required by the cross-level structural argument. -/
noncomputable def compiledDynamicTruthCertificateFamily :
    PATruthCertificateFamily (V := V) where
  localStep := modelIndexedAugmentedLocalBundle
  crossLevel := modelIndexedCrossLevelFormula
  shiftInvariant := modelIndexedShiftInvariantFormula
  substitutionInvariant := modelIndexedSubstitutionInvariantFormula
  axiomSound := modelIndexedAxiomSoundnessFormula

@[simp] theorem compiledDynamicTruthCertificateFamily_localStep (n : V) :
    (compiledDynamicTruthCertificateFamily (V := V)).localStep n =
      modelIndexedAugmentedLocalBundle n := rfl

@[simp] theorem compiledDynamicTruthCertificateFamily_crossLevel (n : V) :
    (compiledDynamicTruthCertificateFamily (V := V)).crossLevel n =
      modelIndexedCrossLevelFormula n := rfl

@[simp] theorem compiledDynamicTruthCertificateFamily_shiftInvariant (n : V) :
    (compiledDynamicTruthCertificateFamily (V := V)).shiftInvariant n =
      modelIndexedShiftInvariantFormula n := rfl

@[simp] theorem compiledDynamicTruthCertificateFamily_substitutionInvariant
    (n : V) :
    (compiledDynamicTruthCertificateFamily (V := V)).substitutionInvariant n =
      modelIndexedSubstitutionInvariantFormula n := rfl

@[simp] theorem compiledDynamicTruthCertificateFamily_axiomSound (n : V) :
    (compiledDynamicTruthCertificateFamily (V := V)).axiomSound n =
      modelIndexedAxiomSoundnessFormula n := rfl

/-! ## Exact base and successor views -/

@[simp] theorem compiledDynamicTruthCertificateFamily_localStep_zero :
    (compiledDynamicTruthCertificateFamily (V := V)).localStep 0 =
      baseAugmentedLocalBundle := by
  simp

@[simp] theorem compiledDynamicTruthCertificateFamily_localStep_succ (n : V) :
    (compiledDynamicTruthCertificateFamily (V := V)).localStep (n + 1) =
      DynamicTruthQuantifierFreeAnchor.orbitCompiledLocalBundleWithQuantifierFreeIntroduction n := by
  simp

@[simp] theorem compiledDynamicTruthCertificateFamily_crossLevel_zero :
    (compiledDynamicTruthCertificateFamily (V := V)).crossLevel 0 =
      DynamicTruthCrossLevelFormula.baseCrossLevelFormula := by
  simp

@[simp] theorem compiledDynamicTruthCertificateFamily_crossLevel_succ (n : V) :
    (compiledDynamicTruthCertificateFamily (V := V)).crossLevel (n + 1) =
      DynamicTruthCrossLevelFormula.orbitSuccessorCrossLevelFormula n := by
  simp

@[simp] theorem compiledDynamicTruthCertificateFamily_shiftInvariant_zero :
    (compiledDynamicTruthCertificateFamily (V := V)).shiftInvariant 0 =
      DynamicTruthShiftInvariantFormula.baseShiftInvariantFormula := by
  simp

@[simp] theorem compiledDynamicTruthCertificateFamily_shiftInvariant_succ
    (n : V) :
    (compiledDynamicTruthCertificateFamily (V := V)).shiftInvariant (n + 1) =
      DynamicTruthShiftInvariantFormula.orbitSuccessorShiftInvariantFormula n := by
  simp

@[simp] theorem
    compiledDynamicTruthCertificateFamily_substitutionInvariant_zero :
    (compiledDynamicTruthCertificateFamily (V := V)).substitutionInvariant 0 =
      DynamicTruthSubstitutionInvariantFormula.baseSubstitutionInvariantFormula := by
  simp

@[simp] theorem
    compiledDynamicTruthCertificateFamily_substitutionInvariant_succ (n : V) :
    (compiledDynamicTruthCertificateFamily (V := V)).substitutionInvariant
        (n + 1) =
      DynamicTruthSubstitutionInvariantFormula.orbitSuccessorSubstitutionInvariantFormula n := by
  simp

@[simp] theorem compiledDynamicTruthCertificateFamily_axiomSound_zero :
    (compiledDynamicTruthCertificateFamily (V := V)).axiomSound 0 =
      DynamicTruthAxiomSoundnessFormula.baseAxiomSoundnessFormula := by
  simp

@[simp] theorem compiledDynamicTruthCertificateFamily_axiomSound_succ (n : V) :
    (compiledDynamicTruthCertificateFamily (V := V)).axiomSound (n + 1) =
      DynamicTruthAxiomSoundnessFormula.orbitSuccessorAxiomSoundnessFormula n := by
  simp

/-! ## Representability of the assembled master code -/

/-- The complete six-field certificate sentence, including the forced final
restricted-consistency coordinate, has one Sigma-one code graph. -/
theorem compiledDynamicTruthCertificateFamily_code_definable :
    HierarchySymbol.sigmaOne.DefinableFunction₁
      (compiledDynamicTruthCertificateFamily (V := V)).code := by
  apply LeanProofs.BoundedPAConsistency.TruthCertificateCodeDefinability.PATruthCertificateFamily.code_definable_of_fields
  · change HierarchySymbol.sigmaOne.DefinableFunction₁
      (modelIndexedAugmentedLocalBundleCode (V := V))
    exact modelIndexedAugmentedLocalBundleCode_definable
  · change HierarchySymbol.sigmaOne.DefinableFunction₁
      (modelIndexedCrossLevelFormulaCode (V := V))
    exact modelIndexedCrossLevelFormulaCode_definable
  · change HierarchySymbol.sigmaOne.DefinableFunction₁
      (modelIndexedShiftInvariantFormulaCode (V := V))
    exact modelIndexedShiftInvariantFormulaCode_definable
  · change HierarchySymbol.sigmaOne.DefinableFunction₁
      (modelIndexedSubstitutionInvariantFormulaCode (V := V))
    exact modelIndexedSubstitutionInvariantFormulaCode_definable
  · change HierarchySymbol.sigmaOne.DefinableFunction₁
      (modelIndexedAxiomSoundnessFormulaCode (V := V))
    exact modelIndexedAxiomSoundnessFormulaCode_definable

end LeanProofs.BoundedPAConsistency.DynamicTruthCertificateFieldFamily
