import BoundedPAConsistency.DynamicTruthSubstitutionInvariantFormula

/-!
# The model-indexed simultaneous-substitution invariance field

`DynamicTruthSubstitutionInvariantFormula` supplies both the genuine
level-zero field and the represented positive-successor field.  This module
splices those branches into a single function on an arbitrary model of
`I Sigma 1`, with the same indexing convention as the represented truth
orbit and the other dynamic certificate fields.

The positive branch uses the model predecessor `n - 1`.  Every nonzero
element of a model of Robinson arithmetic is a successor, so the displayed
successor equation remains exact at nonstandard indices.  Its final graph is
built from represented subtraction, the represented positive field, and a
definable zero test; it neither decodes model syntax nor performs external
recursion over a model element.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantOrbit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantFormula

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-! ## The zero/successor splice -/

/-- The complete simultaneous-substitution invariance field at a possibly
nonstandard model index. -/
noncomputable def modelIndexedSubstitutionInvariantFormula (n : V) :
    Bootstrapping.Formula V ℒₒᵣ :=
  if n = 0 then
    baseSubstitutionInvariantFormula
  else
    orbitSuccessorSubstitutionInvariantFormula (n - 1)

/-- The model-indexed field starts with the genuine base law. -/
@[simp] theorem modelIndexedSubstitutionInvariantFormula_zero :
    modelIndexedSubstitutionInvariantFormula (V := V) 0 =
      baseSubstitutionInvariantFormula := by
  simp [modelIndexedSubstitutionInvariantFormula]

/-- At every successor, including a nonstandard one, the splice selects the
positive field built from the preceding truth-orbit member. -/
@[simp] theorem modelIndexedSubstitutionInvariantFormula_succ (n : V) :
    modelIndexedSubstitutionInvariantFormula (n + 1) =
      orbitSuccessorSubstitutionInvariantFormula n := by
  simp [modelIndexedSubstitutionInvariantFormula]

/-! ## The represented raw-code function -/

/-- Raw code of the complete model-indexed simultaneous-substitution
invariance field. -/
noncomputable def modelIndexedSubstitutionInvariantFormulaCode (n : V) : V :=
  (modelIndexedSubstitutionInvariantFormula n).val

@[simp] theorem modelIndexedSubstitutionInvariantFormulaCode_zero :
    modelIndexedSubstitutionInvariantFormulaCode (V := V) 0 =
      (baseSubstitutionInvariantFormula (V := V)).val := by
  simp [modelIndexedSubstitutionInvariantFormulaCode]

@[simp] theorem modelIndexedSubstitutionInvariantFormulaCode_succ (n : V) :
    modelIndexedSubstitutionInvariantFormulaCode (n + 1) =
      (orbitSuccessorSubstitutionInvariantFormula n).val := by
  simp [modelIndexedSubstitutionInvariantFormulaCode]

/-- The raw code of the complete field has one Sigma-one graph in every
model of `I Sigma 1`. -/
theorem modelIndexedSubstitutionInvariantFormulaCode_definable :
    HierarchySymbol.sigmaOne.DefinableFunction₁
      (modelIndexedSubstitutionInvariantFormulaCode (V := V)) := by
  letI : HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦ (orbitSuccessorSubstitutionInvariantFormula n).val) :=
    orbitSuccessorSubstitutionInvariantFormulaCode_definable
  have hpositive : HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦
        (orbitSuccessorSubstitutionInvariantFormula (n - 1)).val) := by
    have hpred : HierarchySymbol.sigmaOne.DefinableFunction
        (fun v : Fin 1 → V ↦ v 0 - 1) := by
      definability
    simpa using
      (HierarchySymbol.DefinableFunction₁.comp
        (F := fun n : V ↦
          (orbitSuccessorSubstitutionInvariantFormula n).val)
        hpred)
  letI : HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦
        (orbitSuccessorSubstitutionInvariantFormula (n - 1)).val) := hpositive
  have hgraphFor (baseCode : V) (positiveCode : V → V)
      [HierarchySymbol.sigmaOne.DefinableFunction₁ positiveCode] :
      HierarchySymbol.sigmaOne.Definable
      (fun v : Fin 2 → V ↦
        (v 1 = 0 ∧
          v 0 = baseCode) ∨
        (v 1 ≠ 0 ∧
          v 0 = positiveCode (v 1))) := by
    definability
  have hgraph :=
    hgraphFor
      (baseSubstitutionInvariantFormula (V := V)).val
      (fun n : V ↦
        (orbitSuccessorSubstitutionInvariantFormula (n - 1)).val)
  apply hgraph.of_iff
  intro v
  by_cases hn : v 1 = 0
  · simp [modelIndexedSubstitutionInvariantFormulaCode,
      modelIndexedSubstitutionInvariantFormula, hn]
  · simp [modelIndexedSubstitutionInvariantFormulaCode,
      modelIndexedSubstitutionInvariantFormula, hn]

end LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantOrbit
