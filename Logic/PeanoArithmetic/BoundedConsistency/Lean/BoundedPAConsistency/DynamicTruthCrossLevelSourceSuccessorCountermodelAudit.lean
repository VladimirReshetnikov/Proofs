import BoundedPAConsistency.DynamicTruthCrossLevelSourceSuccessorCountermodel

/-!
# Audit for the structural successor countermodel

The two public endpoints below record the exact obstruction exposed by the
standard countermodel.  The literal source successor sentence is false in a
model of lifted PA, and therefore no proof object for that sentence can be
constructed from the present source theory.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelSourceSuccessorCountermodelAudit

open LO FirstOrder
open LeanProofs.BoundedPAConsistency.ModelCodedTwoPredicateParameters
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelSourceSuccessor
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelSourceSuccessorCountermodel

#check sourceSuccessorSentence_not_valid
#check sourceSuccessorSentence_unprovable

example : ¬(ℕ↓[
    LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelSourceTemplate.SourceLanguage] ⊧
      sourceSuccessorSentence) :=
  sourceSuccessorSentence_not_valid

example : twoPredicateParameterPeano 3 3 3 ⊬
    sourceSuccessorSentence :=
  sourceSuccessorSentence_unprovable

#print axioms sourceSuccessorSentence_not_valid
#print axioms sourceSuccessorSentence_unprovable

end LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelSourceSuccessorCountermodelAudit
