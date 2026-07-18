import BoundedPAConsistency.FixedLevelPAAxioms

/-!
# Kernel audit for the final fixed-level PA theorem

The last theorem below is the requested object-language result, not merely a
metatheoretic consistency statement: for every external `n`, its conclusion
is a derivation in PA.  The axiom reports guard the complete chain from the
represented PA recognizer through restricted derivation soundness and
arithmetic completeness.
-/

namespace LeanProofs.BoundedPAConsistency.FixedLevelPAAxiomsAudit

open LeanProofs.BoundedPAConsistency.FixedLevelPAAxioms

#check sigmaTrue_succ_of_mem_pa_delta1Class
#check restrictedConsistent_pa_fixedLevel
#check pa_proves_restrictedConsistency

#print axioms sigmaTrue_succ_of_mem_pa_delta1Class
#print axioms restrictedConsistent_pa_fixedLevel
#print axioms pa_proves_restrictedConsistency

end LeanProofs.BoundedPAConsistency.FixedLevelPAAxiomsAudit
