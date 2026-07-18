import BoundedPAConsistency.FixedLevelPAInductionAxioms

/-!
# Kernel audit for truth of internally recognized PA induction axioms

The exported theorems cover nonstandard formula codes, nonstandard free- and
bound-variable environments, and a nonstandard number of leading universal
quantifiers.  This executable audit makes their exact interfaces visible and
checks that the completed proofs rely only on Lean's standard logical
principles, with no semantic soundness postulate or placeholder axiom.
-/

namespace LeanProofs.BoundedPAConsistency.FixedLevelPAInductionAxiomsAudit

open LeanProofs.BoundedPAConsistency.FixedLevelPAInductionAxioms

#check sigmaTrue_succ_indBodyVal
#check sigmaTrue_succ_free_independent
#check exists_fvarVec_substitutionEnvironment
#check sigmaTrue_succ_inductionClosureBody
#check sigmaTrue_succ_qqAlls_intro
#check sigmaTrue_succ_of_inductionUnivR

#print axioms sigmaTrue_succ_indBodyVal
#print axioms sigmaTrue_succ_free_independent
#print axioms exists_fvarVec_substitutionEnvironment
#print axioms sigmaTrue_succ_inductionClosureBody
#print axioms sigmaTrue_succ_qqAlls_intro
#print axioms sigmaTrue_succ_of_inductionUnivR

end LeanProofs.BoundedPAConsistency.FixedLevelPAInductionAxiomsAudit
