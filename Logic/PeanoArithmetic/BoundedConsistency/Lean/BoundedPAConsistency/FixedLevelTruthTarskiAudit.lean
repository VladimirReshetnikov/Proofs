import BoundedPAConsistency.FixedLevelTruthTarski

/-! Axiom and interface audit for fixed-level Tarski clauses. -/

namespace LeanProofs.BoundedPAConsistency.FixedLevelTruthTarski

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LeanProofs.BoundedPAConsistency.FixedLevelTruth

#check SigmaTrue.domain
#check sigmaTrue_and_iff
#check sigmaTrue_or_iff
#check sigmaTrue_exs_iff
#check piTrue_and_iff
#check piTrue_or_iff
#check piTrue_all_iff
#check lowerPiTrue_iff_piTrue
#check sigmaTrue_succ_all_elim
#check sigmaTrue_succ_all_intro
#check sigmaTrue_succ_all_iff
#check piTrue_succ_exs_iff

#print axioms SigmaTrue.domain
#print axioms sigmaTrue_and_iff
#print axioms sigmaTrue_or_iff
#print axioms sigmaTrue_exs_iff
#print axioms piTrue_and_iff
#print axioms piTrue_or_iff
#print axioms piTrue_all_iff
#print axioms sigmaTrue_succ_all_iff
#print axioms piTrue_succ_exs_iff

end LeanProofs.BoundedPAConsistency.FixedLevelTruthTarski
