import BoundedPAConsistency.DynamicTruthShiftInvariantFormula

/-!
# Audit: model-coded shift-invariance syntax

These checks pin down the named free-tail relation, the represented shift
graph, literal specialization of the fixed source template, and the two
indexing branches of the dynamic truth orbit.  The audited endpoint is the
certificate-field syntax and its Sigma-one code graph, not an unconstructed
PA induction kernel.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantFormulaAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthOrbit
open LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantFormula
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateParameters
open LeanProofs.BoundedPAConsistency.TermEvaluationTransport

#check isFreeTailDef
#check isFreeTail_defined
#check eval_isFreeTailDef
#check sourceFreeTail
#check sourceBoundedDomain
#check sourceShiftedTruthWitness
#check sourceShiftInvariantBody
#check sourceShiftInvariantPredicate
#check sourceShiftInvariantSentence
#check freeTailFormula
#check boundedDomainFormula
#check shiftedTruthWitnessFormula
#check shiftInvariantBodyFormula
#check shiftInvariantPredicateFormula
#check shiftInvariantFormula
#check translate_sourceShiftedTruthWitness
#check translate_sourceShiftInvariantBody
#check translate_sourceShiftInvariantPredicate
#check translate_sourceShiftInvariantSentence
#check upperShiftInvariantFormula
#check baseShiftInvariantFormula
#check baseShiftInvariantFormula_eq_upper
#check orbitSuccessorShiftInvariantFormula
#check orbitSuccessorShiftInvariantFormula_upper
#check orbitSuccessorShiftInvariantFormulaCode_definable

#print axioms isFreeTail_defined
#print axioms eval_isFreeTailDef
#print axioms translate_sourceShiftedTruthWitness
#print axioms translate_sourceShiftInvariantBody
#print axioms translate_sourceShiftInvariantPredicate
#print axioms translate_sourceShiftInvariantSentence
#print axioms orbitSuccessorShiftInvariantFormulaCode_definable

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-- The stable named arithmetic formula agrees with the semantic lookup-tail
condition in every model. -/
example (shifted free : V) :
    isFreeTailDef.val.Evalb ![shifted, free] ↔
      IsFreeTail shifted free := by
  simpa using (eval_isFreeTailDef (V := V) ![shifted, free])

/-- Specialization remains literal for arbitrary lower syntax and arbitrary
(possibly nonstandard) hierarchy levels. -/
example (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceShiftInvariantSentence) =
      shiftInvariantFormula lower lowerLevel upperLevel :=
  translate_sourceShiftInvariantSentence lower lowerLevel upperLevel

/-- The base branch has exactly the spare-level indexing used for bounded
consistency at quantifier-group bound zero. -/
example : baseShiftInvariantFormula (V := V) =
    upperShiftInvariantFormula (truthFormula 0) 0 :=
  baseShiftInvariantFormula_eq_upper

/-- The positive branch uses the represented successor equation and bound
`n + 1`, with no external decoding of `n`. -/
example (n : V) :
    orbitSuccessorShiftInvariantFormula n =
      upperShiftInvariantFormula (truthFormula (n + 1)) (n + 1) :=
  orbitSuccessorShiftInvariantFormula_upper n

/-- One Sigma-one graph uniformly computes every positive-branch field
code. -/
example : HierarchySymbol.sigmaOne.DefinableFunction₁
    (fun n : V ↦ (orbitSuccessorShiftInvariantFormula n).val) :=
  orbitSuccessorShiftInvariantFormulaCode_definable

end LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantFormulaAudit
