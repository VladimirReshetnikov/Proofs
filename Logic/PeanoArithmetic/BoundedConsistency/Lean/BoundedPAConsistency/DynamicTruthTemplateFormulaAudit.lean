import BoundedPAConsistency.DynamicTruthOrbit
import BoundedPAConsistency.DynamicTruthTemplateFormula

/-! Kernel-facing audit for the fixed source successor-truth template. -/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthTemplateFormulaAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LeanProofs.BoundedPAConsistency.DynamicTruthOrbit
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateParameters
open LeanProofs.BoundedPAConsistency.DynamicTruthTemplateFormula

#check SourceLanguage
#check parameterTerm
#check universalRecordBranch
#check successorRecordValid
#check successorTruthFormula
#check translate_liftArithmeticFormula
#check translate_apply₃
#check translate_apply₂
#check translate_lowerAtom
#check translate_universalRecordBranch
#check translate_successorRecordValid
#check translate_successorTruthFormula

#print axioms translate_universalRecordBranch
#print axioms translate_successorRecordValid
#print axioms translate_successorTruthFormula

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-- The source template specializes to the literal next member of the
represented nonstandard orbit. -/
example (n : V) :
    translateFormula (truthFormula n) ![n + 1, n + 1 + 1]
        (Rewriting.emb successorTruthFormula) =
      truthFormula (n + 1) := by
  rw [translate_successorTruthFormula, truthFormula_succ]

end LeanProofs.BoundedPAConsistency.DynamicTruthTemplateFormulaAudit
