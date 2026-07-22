import BoundedPAConsistency.DynamicTruthAxiomSoundnessFormula

/-!
# The model-indexed PA-axiom-soundness field

`DynamicTruthAxiomSoundnessFormula` supplies a genuine field at level zero and
the represented field at every positive successor.  A concrete staged truth
certificate, however, needs one formula-code function defined at every element
of a possibly nonstandard model of `I Sigma 1`.

This module performs that splice.  Its positive branch is evaluated at the
model predecessor `n - 1`; Robinson arithmetic proves that every nonzero model
element is a successor, so the displayed successor equation is exact even at
nonstandard indices.  The graph proof uses only represented subtraction, a
definable zero test, and the already represented positive field-code function.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessOrbit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessFormula

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-! ## The zero/successor splice -/

/-- The complete PA-axiom-soundness field at a possibly nonstandard model
index. -/
noncomputable def modelIndexedAxiomSoundnessFormula (n : V) :
    Bootstrapping.Formula V ℒₒᵣ :=
  if n = 0 then
    baseAxiomSoundnessFormula
  else
    orbitSuccessorAxiomSoundnessFormula (n - 1)

/-- The model-indexed field starts with the genuine base assertion. -/
@[simp] theorem modelIndexedAxiomSoundnessFormula_zero :
    modelIndexedAxiomSoundnessFormula (V := V) 0 =
      baseAxiomSoundnessFormula := by
  simp [modelIndexedAxiomSoundnessFormula]

/-- Every successor selects the positive field over the preceding truth-orbit
member, including when the index is nonstandard. -/
@[simp] theorem modelIndexedAxiomSoundnessFormula_succ (n : V) :
    modelIndexedAxiomSoundnessFormula (n + 1) =
      orbitSuccessorAxiomSoundnessFormula n := by
  simp [modelIndexedAxiomSoundnessFormula]

/-! ## The represented raw-code function -/

/-- Raw code of the complete model-indexed axiom-soundness field. -/
noncomputable def modelIndexedAxiomSoundnessFormulaCode (n : V) : V :=
  (modelIndexedAxiomSoundnessFormula n).val

@[simp] theorem modelIndexedAxiomSoundnessFormulaCode_zero :
    modelIndexedAxiomSoundnessFormulaCode (V := V) 0 =
      (baseAxiomSoundnessFormula (V := V)).val := by
  simp [modelIndexedAxiomSoundnessFormulaCode]

@[simp] theorem modelIndexedAxiomSoundnessFormulaCode_succ (n : V) :
    modelIndexedAxiomSoundnessFormulaCode (n + 1) =
      (orbitSuccessorAxiomSoundnessFormula n).val := by
  simp [modelIndexedAxiomSoundnessFormulaCode]

/-- The complete field-code function has one Sigma-one graph in every model
of `I Sigma 1`. -/
theorem modelIndexedAxiomSoundnessFormulaCode_definable :
    HierarchySymbol.sigmaOne.DefinableFunction₁
      (modelIndexedAxiomSoundnessFormulaCode (V := V)) := by
  letI : HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦ (orbitSuccessorAxiomSoundnessFormula n).val) :=
    orbitSuccessorAxiomSoundnessFormulaCode_definable
  have hpositive : HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦
        (orbitSuccessorAxiomSoundnessFormula (n - 1)).val) := by
    have hpred : HierarchySymbol.sigmaOne.DefinableFunction
        (fun v : Fin 1 → V ↦ v 0 - 1) := by
      definability
    simpa using
      (HierarchySymbol.DefinableFunction₁.comp
        (F := fun n : V ↦
          (orbitSuccessorAxiomSoundnessFormula n).val)
        hpred)
  letI : HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦
        (orbitSuccessorAxiomSoundnessFormula (n - 1)).val) := hpositive
  have hgraph : HierarchySymbol.sigmaOne.Definable
      (fun v : Fin 2 → V ↦
        (v 1 = 0 ∧
          v 0 = (baseAxiomSoundnessFormula (V := V)).val) ∨
        (v 1 ≠ 0 ∧
          v 0 =
            (orbitSuccessorAxiomSoundnessFormula (v 1 - 1)).val)) := by
    definability
  apply hgraph.of_iff
  intro v
  by_cases hn : v 1 = 0
  · simp [modelIndexedAxiomSoundnessFormulaCode,
      modelIndexedAxiomSoundnessFormula, hn]
  · simp [modelIndexedAxiomSoundnessFormulaCode,
      modelIndexedAxiomSoundnessFormula, hn]

end LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessOrbit
