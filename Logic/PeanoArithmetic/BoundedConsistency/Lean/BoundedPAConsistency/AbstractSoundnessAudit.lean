import BoundedPAConsistency.AbstractSoundness

/-!
# Kernel audit for abstract fixed-level rule soundness

The theorem below is intentionally parameterized by an explicit partial-truth
interface, a definability witness for the sequent invariant, and truth of the
chosen theory's internally recognized axioms.  Later audits will ensure that
the concrete PA instance discharges all three parameters.
-/

namespace LeanProofs.BoundedPAConsistency.AbstractSoundnessAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LeanProofs.BoundedPAConsistency.AbstractSoundness

#check Laws
#check SequentTrue
#check restrictedDerivation_sound
#check restrictedConsistent_of_laws

#print axioms restrictedDerivation_sound
#print axioms restrictedConsistent_of_laws

end LeanProofs.BoundedPAConsistency.AbstractSoundnessAudit
