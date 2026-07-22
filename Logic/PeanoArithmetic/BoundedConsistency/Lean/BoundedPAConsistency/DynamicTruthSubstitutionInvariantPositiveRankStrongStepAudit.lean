import BoundedPAConsistency.DynamicTruthSubstitutionInvariantPositiveRankStrongStep

/-!
# Audit: positive-rank substitution-invariance strong step

The audited theorem is uniform in the two model-coded hierarchy levels, the
predecessor relation, and the formula code.  Its only recursive premise is
the strict numeric prefix, and its only semantic interface to the predecessor
stage is the already represented cross-level law.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantPositiveRankStrongStepAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelStrongStepSource
open LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantPositiveRankStrongStep

#check SubstitutionInvariantAt
#check SuccessorTruth.all_intro_of_domain
#check SuccessorTruth.all_iff_of_domain
#check SuccessorTruth.neg_iff_not_of_pi
#check SuccessorTruth.substitution_strongStep

#print axioms SuccessorTruth.all_intro_of_domain
#print axioms SuccessorTruth.all_iff_of_domain
#print axioms SuccessorTruth.neg_iff_not_of_pi
#print axioms SuccessorTruth.substitution_strongStep

end LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantPositiveRankStrongStepAudit
