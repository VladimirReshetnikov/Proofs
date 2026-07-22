import BoundedPAConsistency.DynamicTruthSuccessorLaws

/-!
# Audit: semantic laws for adjacent dynamic truth successors

The public endpoint below works over arbitrary elements of a model of PA;
the hierarchy indices are not restricted to standard numerals.  This audit
also keeps the three certificate interfaces visible: cross-level coherence,
shift invariance, and simultaneous-substitution invariance.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthSuccessorLawsAudit

open LeanProofs.BoundedPAConsistency.DynamicTruthSuccessorLaws

#check nextTruth_neg_iff
#check nextTruth_and_iff
#check nextTruth_or_iff
#check nextTruth_exs_iff
#check nextTruth_all_iff
#check nextTruth_substs1_iff
#check nextTruth_free_iff
#check nextTruth_laws

#print axioms nextTruth_neg_iff
#print axioms nextTruth_all_iff
#print axioms nextTruth_free_iff
#print axioms nextTruth_laws

end LeanProofs.BoundedPAConsistency.DynamicTruthSuccessorLawsAudit
