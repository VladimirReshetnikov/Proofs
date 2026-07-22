import BoundedPAConsistency.DynamicTruthSubstitutionInvariantFormula

/-!
# Audit: model-coded simultaneous-substitution invariance syntax

The checks pin down the stable substitution-environment formula, represented
substitution witness, literal source specialization, orbit indexing, and
Sigma-one positive-field code graph.  No induction-kernel theorem is claimed.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantFormulaAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthOrbit
open LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantFormula
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateParameters
open LeanProofs.BoundedPAConsistency.TermEvaluationTransport

#check isSubstitutionEnvironmentDef
#check isSubstitutionEnvironment_defined
#check eval_isSubstitutionEnvironmentDef
#check apply₅
#check sourceSemitermVector
#check sourceBoundLength
#check sourceSubstitutionEnvironment
#check sourceSemiformula
#check sourceBoundedDomain
#check sourceSubstitutedTruthWitness
#check sourceSubstitutionInvariantBody
#check sourceSubstitutionInvariantPredicate
#check sourceSubstitutionInvariantSentence
#check semitermVectorFormula
#check boundLengthFormula
#check substitutionEnvironmentFormula
#check semiformulaFormula
#check boundedDomainFormula
#check substitutedTruthWitnessFormula
#check substitutionInvariantBodyFormula
#check substitutionInvariantPredicateFormula
#check substitutionInvariantFormula
#check translate_apply₅
#check translate_sourceSubstitutedTruthWitness
#check translate_sourceSubstitutionInvariantBody
#check translate_sourceSubstitutionInvariantPredicate
#check translate_sourceSubstitutionInvariantSentence
#check upperSubstitutionInvariantFormula
#check baseSubstitutionInvariantFormula
#check baseSubstitutionInvariantFormula_eq_upper
#check orbitSuccessorSubstitutionInvariantFormula
#check orbitSuccessorSubstitutionInvariantFormula_upper
#check orbitSuccessorSubstitutionInvariantFormulaCode_definable

#print axioms isSubstitutionEnvironment_defined
#print axioms eval_isSubstitutionEnvironmentDef
#print axioms translate_apply₅
#print axioms translate_sourceSubstitutedTruthWitness
#print axioms translate_sourceSubstitutionInvariantBody
#print axioms translate_sourceSubstitutionInvariantPredicate
#print axioms translate_sourceSubstitutionInvariantSentence
#print axioms orbitSuccessorSubstitutionInvariantFormulaCode_definable

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-- The stable named syntax agrees with the semantic environment relation in
every model. -/
example (bound free arity terms subBound : V) :
    isSubstitutionEnvironmentDef.val.Evalb
        ![bound, free, arity, terms, subBound] ↔
      IsSubstitutionEnvironment bound free arity terms subBound := by
  simpa using
    (eval_isSubstitutionEnvironmentDef (V := V)
      ![bound, free, arity, terms, subBound])

/-- Source specialization is literal for arbitrary lower truth syntax and
possibly nonstandard hierarchy levels. -/
example (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceSubstitutionInvariantSentence) =
      substitutionInvariantFormula lower lowerLevel upperLevel :=
  translate_sourceSubstitutionInvariantSentence
    lower lowerLevel upperLevel

/-- The base branch names the literal zeroth positive truth-orbit member. -/
example : baseSubstitutionInvariantFormula (V := V) =
    upperSubstitutionInvariantFormula (truthFormula 0) 0 :=
  baseSubstitutionInvariantFormula_eq_upper

/-- The positive branch uses the represented successor orbit equation. -/
example (n : V) :
    orbitSuccessorSubstitutionInvariantFormula n =
      upperSubstitutionInvariantFormula
        (truthFormula (n + 1)) (n + 1) :=
  orbitSuccessorSubstitutionInvariantFormula_upper n

/-- One Sigma-one graph computes all positive-branch field codes. -/
example : HierarchySymbol.sigmaOne.DefinableFunction₁
    (fun n : V ↦
      (orbitSuccessorSubstitutionInvariantFormula n).val) :=
  orbitSuccessorSubstitutionInvariantFormulaCode_definable

end LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantFormulaAudit
