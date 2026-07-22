import BoundedPAConsistency.DynamicTruthPredecessorFormula

/-!
# Assumption audit for the uniform predecessor truth formula

This file records the public equations needed by cross-level structural
induction and asks Lean to report the assumptions behind the nontrivial
reconstruction, shift, and definability proofs.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthPredecessorFormulaAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthOrbit
open LeanProofs.BoundedPAConsistency.DynamicTruthPredecessorFormula

#check predecessorTruthFormula
#check predecessorTruthFormula_zero
#check predecessorTruthFormula_succ
#check predecessorTruthFormula_shift
#check predecessorTruthFormula_val_shift
#check successorTruthFormula_predecessor_eq
#check predecessorTruthFormulaCode
#check predecessorTruthFormula_val
#check predecessorTruthFormulaCode_zero
#check predecessorTruthFormulaCode_succ
#check predecessorTruthFormulaCode_definable

#print axioms predecessorTruthFormula_zero
#print axioms predecessorTruthFormula_succ
#print axioms predecessorTruthFormula_shift
#print axioms predecessorTruthFormula_val_shift
#print axioms successorTruthFormula_predecessor_eq
#print axioms predecessorTruthFormulaCode_definable

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

example (n : V) :
    successorTruthFormula (predecessorTruthFormula n) n (n + 1) =
      truthFormula n :=
  successorTruthFormula_predecessor_eq n

example : HierarchySymbol.sigmaOne.DefinableFunction₁
    (predecessorTruthFormulaCode (V := V)) :=
  predecessorTruthFormulaCode_definable

end LeanProofs.BoundedPAConsistency.DynamicTruthPredecessorFormulaAudit
