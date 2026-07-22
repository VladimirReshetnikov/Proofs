import BoundedPAConsistency.FixedLevelPAInduction

/-!
# Axiom audit for model induction and PA-recognizer rank inheritance

This file is intentionally executable documentation.  It keeps the exact
interfaces visible and asks Lean to report every axiom used by the proofs,
making accidental placeholders or new assumptions immediately apparent in
the build log.
-/

namespace LeanProofs.BoundedPAConsistency.FixedLevelPAInductionAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.CodedHierarchy
open LeanProofs.BoundedPAConsistency.FixedLevelTruth
open LeanProofs.BoundedPAConsistency.FixedLevelPAInduction

#check quantifierBoundedCode_of_qqAlls
#check quantifierBoundedCode_of_indBodyVal
#check isSemitermVec_fvarVec
#check bounded_inductionUnivR_data
#check inductionZeroVec
#check inductionSuccVec
#check indBodyVal_true_of_semantic_induction
#check sigmaTrue_succ_induction
#check piTrue_succ_induction

#print axioms quantifierBoundedCode_of_qqAlls
#print axioms quantifierBoundedCode_of_indBodyVal
#print axioms isSemitermVec_fvarVec
#print axioms bounded_inductionUnivR_data
#print axioms indBodyVal_true_of_semantic_induction
#print axioms sigmaTrue_succ_induction
#print axioms piTrue_succ_induction

end LeanProofs.BoundedPAConsistency.FixedLevelPAInductionAudit
