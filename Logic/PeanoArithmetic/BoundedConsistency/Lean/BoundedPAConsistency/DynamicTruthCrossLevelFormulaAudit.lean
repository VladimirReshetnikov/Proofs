import BoundedPAConsistency.DynamicTruthCrossLevelFormula

/-!
# Audit: model-coded cross-level truth syntax

The checks below pin down the fixed source formula, its exact specialization
to arbitrary model-coded truth syntax, and both indexing branches of the
represented orbit.  At this stage the module intentionally exposes syntax;
the PA structural-induction proof is audited separately when compiled.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelFormulaAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthOrbit
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelFormula
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateParameters

#check sourceSigmaDomain
#check sourcePiDomain
#check sourceLowerPiTruth
#check sourceCrossLevelBody
#check sourceCrossLevelPredicate
#check sourceCrossLevelSentence
#check sigmaDomainFormula
#check piDomainFormula
#check lowerPiTruthFormula
#check crossLevelBodyFormula
#check crossLevelPredicateFormula
#check crossLevelFormula
#check translate_sourceCrossLevelBody
#check translate_sourceCrossLevelPredicate
#check translate_sourceCrossLevelSentence
#check baseCrossLevelFormula
#check orbitSuccessorCrossLevelFormula

#print axioms translate_sourceLowerPiTruth
#print axioms translate_sourceCrossLevelBody
#print axioms translate_sourceCrossLevelPredicate
#print axioms translate_sourceCrossLevelSentence

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-- Specialization remains literal for arbitrary lower syntax and arbitrary
(possibly nonstandard) named hierarchy levels. -/
example (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceCrossLevelSentence) =
      crossLevelFormula lower lowerLevel upperLevel :=
  translate_sourceCrossLevelSentence lower lowerLevel upperLevel

/-- The positive branch uses exactly the represented successor equation;
there is no external decoding or standard-index recursion hidden here. -/
example (n : V) :
    DynamicTruthFormula.successorTruthFormula
        (truthFormula n) (n + 1) (n + 1 + 1) =
      truthFormula (n + 1) := by
  symm
  exact truthFormula_succ n

/-- The base branch names the genuine quantifier-free predecessor. -/
example : baseCrossLevelFormula (V := V) =
    crossLevelFormula baseTruthFormula 0 1 := rfl

end LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelFormulaAudit
