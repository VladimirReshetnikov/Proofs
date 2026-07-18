import BoundedPAConsistency.FixedLevelTruthSubstitution

/-!
# Audit: fixed-level truth transport

This file keeps the public transport surface visible and asks Lean to report
all axioms used by the principal theorems.  In particular, every code and
environment in these signatures lives in an arbitrary model `V`; none is
decoded into an external Lean syntax tree.
-/

namespace LeanProofs.BoundedPAConsistency.FixedLevelTruthSubstitutionAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.CodedHierarchy
open LeanProofs.BoundedPAConsistency.OrientedHierarchy
open LeanProofs.BoundedPAConsistency.TermEvaluation
open LeanProofs.BoundedPAConsistency.TermEvaluationTransport
open LeanProofs.BoundedPAConsistency.FixedLevelTruth
open LeanProofs.BoundedPAConsistency.FixedLevelTruthSubstitution

#check termValue_termBShift_seqCons
#check znth_seqCons_of_lt
#check isSubstitutionEnvironment_qVec_seqCons

#check sigmaTrue_shift_iff_of_isFreeTail
#check piTrue_shift_iff_of_isFreeTail
#check sigmaTrue_subst_iff_of_isSubstitutionEnvironment
#check piTrue_subst_iff_of_isSubstitutionEnvironment

#check sigmaTrue_succ_shift_iff
#check sigmaTrue_succ_subst_iff_of_isSubstitutionEnvironment

#print axioms termValue_termBShift_seqCons
#print axioms isSubstitutionEnvironment_qVec_seqCons
#print axioms sigmaTrue_shift_iff_of_isFreeTail
#print axioms piTrue_shift_iff_of_isFreeTail
#print axioms sigmaTrue_subst_iff_of_isSubstitutionEnvironment
#print axioms piTrue_subst_iff_of_isSubstitutionEnvironment
#print axioms sigmaTrue_succ_shift_iff
#print axioms sigmaTrue_succ_subst_iff_of_isSubstitutionEnvironment

end LeanProofs.BoundedPAConsistency.FixedLevelTruthSubstitutionAudit
