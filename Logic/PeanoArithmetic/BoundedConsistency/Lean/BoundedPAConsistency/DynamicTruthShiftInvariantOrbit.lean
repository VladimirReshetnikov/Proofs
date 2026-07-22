import BoundedPAConsistency.DynamicTruthShiftInvariantFormula

/-!
# The model-indexed shift-invariance field

`DynamicTruthShiftInvariantFormula` provides a genuine level-zero field and
the represented positive-successor field.  This module splices them into one
function on an arbitrary model of `I Sigma 1`, following the same indexing
convention as the represented truth orbit and the cross-level field.

The positive branch uses the model predecessor `n - 1`.  Since every
nonzero element of a model of Robinson arithmetic is a successor, the exact
successor equation holds at nonstandard indices as well.  The final graph
theorem is assembled from represented subtraction, the already represented
positive field, and a definable zero test; no external recursion or decoding
of model syntax is involved.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantOrbit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantFormula

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-! ## The zero/successor splice -/

/-- The complete shift-invariance field at a possibly nonstandard model
index. -/
noncomputable def modelIndexedShiftInvariantFormula (n : V) :
    Bootstrapping.Formula V ℒₒᵣ :=
  if n = 0 then
    baseShiftInvariantFormula
  else
    orbitSuccessorShiftInvariantFormula (n - 1)

/-- The model-indexed field starts with the genuine base law. -/
@[simp] theorem modelIndexedShiftInvariantFormula_zero :
    modelIndexedShiftInvariantFormula (V := V) 0 =
      baseShiftInvariantFormula := by
  simp [modelIndexedShiftInvariantFormula]

/-- At every successor, including a nonstandard one, the splice selects the
positive field built from the preceding truth-orbit member. -/
@[simp] theorem modelIndexedShiftInvariantFormula_succ (n : V) :
    modelIndexedShiftInvariantFormula (n + 1) =
      orbitSuccessorShiftInvariantFormula n := by
  simp [modelIndexedShiftInvariantFormula]

/-! ## The represented raw-code function -/

/-- Raw code of the complete model-indexed shift-invariance field. -/
noncomputable def modelIndexedShiftInvariantFormulaCode (n : V) : V :=
  (modelIndexedShiftInvariantFormula n).val

@[simp] theorem modelIndexedShiftInvariantFormulaCode_zero :
    modelIndexedShiftInvariantFormulaCode (V := V) 0 =
      (baseShiftInvariantFormula (V := V)).val := by
  simp [modelIndexedShiftInvariantFormulaCode]

@[simp] theorem modelIndexedShiftInvariantFormulaCode_succ (n : V) :
    modelIndexedShiftInvariantFormulaCode (n + 1) =
      (orbitSuccessorShiftInvariantFormula n).val := by
  simp [modelIndexedShiftInvariantFormulaCode]

/-- The raw code of the complete field has a single Sigma-one graph in every
model of `I Sigma 1`. -/
theorem modelIndexedShiftInvariantFormulaCode_definable :
    HierarchySymbol.sigmaOne.DefinableFunction₁
      (modelIndexedShiftInvariantFormulaCode (V := V)) := by
  letI : HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦ (orbitSuccessorShiftInvariantFormula n).val) :=
    orbitSuccessorShiftInvariantFormulaCode_definable
  have hpositive : HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦
        (orbitSuccessorShiftInvariantFormula (n - 1)).val) := by
    have hpred : HierarchySymbol.sigmaOne.DefinableFunction
        (fun v : Fin 1 → V ↦ v 0 - 1) := by
      definability
    simpa using
      (HierarchySymbol.DefinableFunction₁.comp
        (F := fun n : V ↦
          (orbitSuccessorShiftInvariantFormula n).val)
        hpred)
  letI : HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦
        (orbitSuccessorShiftInvariantFormula (n - 1)).val) := hpositive
  have hgraph : HierarchySymbol.sigmaOne.Definable
      (fun v : Fin 2 → V ↦
        (v 1 = 0 ∧
          v 0 = (baseShiftInvariantFormula (V := V)).val) ∨
        (v 1 ≠ 0 ∧
          v 0 =
            (orbitSuccessorShiftInvariantFormula (v 1 - 1)).val)) := by
    definability
  apply hgraph.of_iff
  intro v
  by_cases hn : v 1 = 0
  · simp [modelIndexedShiftInvariantFormulaCode,
      modelIndexedShiftInvariantFormula, hn]
  · simp [modelIndexedShiftInvariantFormulaCode,
      modelIndexedShiftInvariantFormula, hn]

end LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantOrbit
