import BoundedPAConsistency.DynamicTruthCrossLevelStrongStepSource

/-!
# Audit: genuine dynamic cross-level strong step

This audit freezes the semantic certificate interface used by the positive
cross-level and shift stages.  In particular, the main theorem requires the
literal current-definition premise and a positive quantifier-free anchor;
there is no theorem reinstating the invalid arbitrary-current interface.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelStrongStepSourceAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelStrongStepSource

#check SuccessorTruth.domain
#check SuccessorTruth.and_iff
#check SuccessorTruth.or_iff
#check SuccessorTruth.exs_iff
#check SuccessorTruth.all_iff
#check SuccessorTruth.rel_iff
#check SuccessorTruth.nrel_iff
#check SuccessorPiTruth.exs_iff_lower
#check successorCrossLaws_strongStep

#check sourceCurrentDefinition
#check sourceTargetQuantifierFreeIntroduction
#check sourceStrongStepPremises
#check sourceStrongStepSentence

#print axioms SuccessorTruth.domain
#print axioms SuccessorTruth.and_iff
#print axioms SuccessorTruth.or_iff
#print axioms SuccessorTruth.exs_iff
#print axioms SuccessorTruth.all_iff
#print axioms successorCrossLaws_strongStep

end LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelStrongStepSourceAudit
