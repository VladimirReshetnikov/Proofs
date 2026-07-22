import BoundedPAConsistency.DynamicTruthFormula

/-! Kernel-facing audit for the model-coded truth-formula successor. -/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthFormulaAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthFormula

#check qfTruthDef
#check baseTruthFormula
#check successorTruthFormula
#check universalRecordBranchCode
#check universalRecordBranchCode_definable
#check successorRecordValidCode
#check successorRecordValidCode_definable
#check successorTruthFormulaCode
#check successorTruthFormulaCode_definable
#check successorTruthFormula_val_eq_code
#check successorTruthFormula_shift_of_lower
#check successorTruthFormula_val_shift_of_lower
#check standardSuccessorTruthFormula
#check typedQuote_standardSuccessorTruthFormula
#check eval_standardSuccessorRecordValid_iff
#check levelZeroTruthFormula
#check levelZeroTruthSyntax
#check levelZeroTruthFormula_eq_typedQuote
#check levelZeroTruthFormula_val_eq_quote
#check eval_levelZeroTruthSyntax_iff
#check levelZeroTruthFormula_shift
#check baseFinalConsistencyFormula
#check baseFinalConsistencyProof
#check baseFinalConsistencyProof_isPAProof
#check baseFinalConsistencyFormula_val_eq_target
#check exists_paProof_restrictedConsistency_zero

#print axioms successorTruthFormula_shift_of_lower
#print axioms universalRecordBranchCode_definable
#print axioms successorRecordValidCode_definable
#print axioms successorTruthFormulaCode_definable
#print axioms typedQuote_standardSuccessorTruthFormula
#print axioms eval_levelZeroTruthSyntax_iff
#print axioms baseFinalConsistencyProof
#print axioms baseFinalConsistencyProof_isPAProof

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

/-- The base checkpoint exposes an actual proof code, not only an external
provability assertion. -/
example :
    Proof Peano (baseFinalConsistencyProof (V := V)).val
      (baseFinalConsistencyFormula (V := V)).val :=
  baseFinalConsistencyProof_isPAProof

end LeanProofs.BoundedPAConsistency.DynamicTruthFormulaAudit
