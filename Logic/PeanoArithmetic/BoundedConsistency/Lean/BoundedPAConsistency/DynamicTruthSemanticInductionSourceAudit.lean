import BoundedPAConsistency.DynamicTruthSemanticInductionSource

/-!
# Axiom audit for the fixed semantic-induction source sentence

The checks below keep the public syntax and its semantic realization visible
to downstream reviews.  In particular, the final theorem identifies one
closed source sentence with the `SemanticInduction` interface consumed by the
dynamic PA-axiom soundness proof.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthSemanticInductionSourceAudit

open LeanProofs.BoundedPAConsistency.DynamicTruthTemplateSemantics
open LeanProofs.BoundedPAConsistency.DynamicTruthSemanticInductionSource

#check arithmeticReduct_eq_standardModel
#check eval_liftArithmeticFormula
#check eval_successorRecordValid
#check eval_successorTruthFormula

#check sourceExtendedTruthPredicate
#check sourceSemanticInductionBody
#check sourceSemanticInductionSentence
#check eval_sourceExtendedTruthPredicate
#check eval_sourceExtendedTruthAt
#check eval_sourceSemanticInductionBody
#check eval_sourceSemanticInductionSentence

#print axioms eval_successorTruthFormula
#print axioms eval_sourceExtendedTruthPredicate
#print axioms eval_sourceSemanticInductionBody
#print axioms eval_sourceSemanticInductionSentence

end LeanProofs.BoundedPAConsistency.DynamicTruthSemanticInductionSourceAudit
