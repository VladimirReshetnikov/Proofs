import BoundedPAConsistency.DynamicTruthCrossLevelOrbit

/-!
# Audit: the model-indexed cross-level field

These checks pin down both branches of the splice and its uniform Sigma-one
code graph.  The examples are stated with explicit PA and `I Sigma 1` model
instances, matching the model interface used by the eventual uniform PA
proof selector.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelOrbitAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelOrbit

#check modelIndexedCrossLevelFormula
#check modelIndexedCrossLevelFormula_zero
#check modelIndexedCrossLevelFormula_succ
#check modelIndexedCrossLevelFormulaCode
#check modelIndexedCrossLevelFormulaCode_zero
#check modelIndexedCrossLevelFormulaCode_succ
#check modelIndexedCrossLevelFormulaCode_definable

#print axioms modelIndexedCrossLevelFormula_zero
#print axioms modelIndexedCrossLevelFormula_succ
#print axioms modelIndexedCrossLevelFormulaCode_definable

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* Peano]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-- The zero branch is literally the field comparing level-one truth with
the quantifier-free base predicate. -/
example : modelIndexedCrossLevelFormula (V := V) 0 =
    baseCrossLevelFormula :=
  modelIndexedCrossLevelFormula_zero

/-- The positive branch is indexed by its predecessor inside the model. -/
example (n : V) : modelIndexedCrossLevelFormula (n + 1) =
    orbitSuccessorCrossLevelFormula n :=
  modelIndexedCrossLevelFormula_succ n

/-- One Sigma-one graph covers zero, all standard successors, and all
nonstandard successors. -/
example : HierarchySymbol.sigmaOne.DefinableFunction₁
    (modelIndexedCrossLevelFormulaCode (V := V)) :=
  modelIndexedCrossLevelFormulaCode_definable

end LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelOrbitAudit
