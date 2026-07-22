import BoundedPAConsistency.DynamicTruthAxiomSoundnessSemantic

/-! # Axiom audit for abstract dynamic PA-axiom soundness -/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessSemanticAudit

open LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessSemantic

#check SemanticInduction
#check FreeEnvironmentIndependence
#check UniversalClosureIntroduction
#check sat_subst_one
#check indBodyVal_true
#check inductionClosureBody_true
#check of_inductionUnivR
#check of_mem_pa_delta1Class

#print axioms sat_subst_one
#print axioms indBodyVal_true
#print axioms inductionClosureBody_true
#print axioms of_inductionUnivR
#print axioms of_mem_pa_delta1Class

end LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessSemanticAudit
