import BoundedPAConsistency.FixedLevelTruthCoherence

/-! Axiom and interface audit for fixed-level coherence and conservativity. -/

namespace LeanProofs.BoundedPAConsistency.FixedLevelTruthCoherence

#check sigmaTrue_one_qf_sound
#check sigmaTrue_succ_qf_sound
#check sigmaTrue_one_qf_iff
#check sigmaTrue_succ_qf_iff
#check piTrue_zero_qf_iff
#check piTrue_one_qf_iff
#check piTrue_succ_qf_iff
#check sigmaTrue_zero_iff_piTrue_zero
#check sigmaTrue_one_iff_piTrue_one_of_qf
#check sigmaTrue_succ_iff_of_isSigmaCode
#check sigmaTrue_succ_iff_piTrue_of_isPiCode
#check sigmaTrue_iff_piTrue_of_domains

#print axioms sigmaTrue_one_qf_sound
#print axioms sigmaTrue_succ_qf_sound
#print axioms sigmaTrue_one_qf_iff
#print axioms sigmaTrue_succ_qf_iff
#print axioms piTrue_zero_qf_iff
#print axioms piTrue_one_qf_iff
#print axioms piTrue_succ_qf_iff
#print axioms sigmaTrue_zero_iff_piTrue_zero
#print axioms sigmaTrue_one_iff_piTrue_one_of_qf
#print axioms sigmaTrue_succ_iff_of_isSigmaCode
#print axioms sigmaTrue_succ_iff_piTrue_of_isPiCode
#print axioms sigmaTrue_iff_piTrue_of_domains

end LeanProofs.BoundedPAConsistency.FixedLevelTruthCoherence
