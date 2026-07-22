import BoundedPAConsistency.DynamicTruthCrossLevelFormula

/-!
# The model-indexed cross-level field

`DynamicTruthCrossLevelFormula` supplies the two pieces needed by a truth
certificate: a fixed base field comparing level-one truth with
quantifier-free truth, and a represented positive-successor field.  This
module joins those pieces into one function on the natural numbers of an
arbitrary model of `I Sigma 1`.

The splice is deliberately performed at the typed-formula level.  At zero it
selects `baseCrossLevelFormula`; away from zero, the model predecessor
`n - 1` is fed to `orbitSuccessorCrossLevelFormula`.  Robinson arithmetic,
and hence `I Sigma 1`, proves that every nonzero element is a successor, so
this definition covers nonstandard indices just as it covers standard ones.

The final theorem proves that the raw formula-code function has a single
Sigma-one graph.  Its proof uses only represented subtraction, the existing
Sigma-one graph of the positive field, and a bounded zero/nonzero case split;
it does not decode formula codes or recurse externally over `Nat`.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelOrbit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelFormula

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-! ## The zero/successor splice -/

/-- The complete cross-level field at an arbitrary model index.

The subtraction is truncated, but it is evaluated only in the nonzero
branch.  Thus index zero names the genuine quantifier-free base field, while
every index `n + 1` names the positive field constructed from orbit member
`n`. -/
noncomputable def modelIndexedCrossLevelFormula (n : V) :
    Bootstrapping.Formula V ℒₒᵣ :=
  if n = 0 then
    baseCrossLevelFormula
  else
    orbitSuccessorCrossLevelFormula (n - 1)

/-- The splice has exactly the required base value. -/
@[simp] theorem modelIndexedCrossLevelFormula_zero :
    modelIndexedCrossLevelFormula (V := V) 0 =
      baseCrossLevelFormula := by
  simp [modelIndexedCrossLevelFormula]

/-- The splice has exactly the required positive-successor value, including
when `n` is nonstandard. -/
@[simp] theorem modelIndexedCrossLevelFormula_succ (n : V) :
    modelIndexedCrossLevelFormula (n + 1) =
      orbitSuccessorCrossLevelFormula n := by
  simp [modelIndexedCrossLevelFormula]

/-! ## The represented raw-code function -/

/-- Raw code of the complete model-indexed cross-level field. -/
noncomputable def modelIndexedCrossLevelFormulaCode (n : V) : V :=
  (modelIndexedCrossLevelFormula n).val

@[simp] theorem modelIndexedCrossLevelFormulaCode_zero :
    modelIndexedCrossLevelFormulaCode (V := V) 0 =
      (baseCrossLevelFormula (V := V)).val := by
  simp [modelIndexedCrossLevelFormulaCode]

@[simp] theorem modelIndexedCrossLevelFormulaCode_succ (n : V) :
    modelIndexedCrossLevelFormulaCode (n + 1) =
      (orbitSuccessorCrossLevelFormula n).val := by
  simp [modelIndexedCrossLevelFormulaCode]

/-- The raw code of the zero/successor splice is Sigma-one definable over
every model of `I Sigma 1`.

The graph is written as the disjunction of its two branches.  In the positive
branch, represented truncated subtraction computes the predecessor and the
existing graph theorem computes the successor-field code. -/
theorem modelIndexedCrossLevelFormulaCode_definable :
    HierarchySymbol.sigmaOne.DefinableFunction₁
      (modelIndexedCrossLevelFormulaCode (V := V)) := by
  letI : HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦ (orbitSuccessorCrossLevelFormula n).val) :=
    orbitSuccessorCrossLevelFormulaCode_definable
  have hpositive : HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦
        (orbitSuccessorCrossLevelFormula (n - 1)).val) := by
    have hpred : HierarchySymbol.sigmaOne.DefinableFunction
        (fun v : Fin 1 → V ↦ v 0 - 1) := by
      definability
    simpa using
      (HierarchySymbol.DefinableFunction₁.comp
        (F := fun n : V ↦ (orbitSuccessorCrossLevelFormula n).val)
        hpred)
  letI : HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦
        (orbitSuccessorCrossLevelFormula (n - 1)).val) := hpositive
  have hgraph : HierarchySymbol.sigmaOne.Definable
      (fun v : Fin 2 → V ↦
        (v 1 = 0 ∧ v 0 = (baseCrossLevelFormula (V := V)).val) ∨
        (v 1 ≠ 0 ∧
          v 0 = (orbitSuccessorCrossLevelFormula (v 1 - 1)).val)) := by
    definability
  apply hgraph.of_iff
  intro v
  by_cases hn : v 1 = 0
  · simp [modelIndexedCrossLevelFormulaCode,
      modelIndexedCrossLevelFormula, hn]
  · simp [modelIndexedCrossLevelFormulaCode,
      modelIndexedCrossLevelFormula, hn]

end LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelOrbit
