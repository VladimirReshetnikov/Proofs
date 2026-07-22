import BoundedPAConsistency.AbstractSoundness

/-!
# Kernel audit for abstract fixed-level rule soundness

The core theorem is parameterized by an explicit partial-truth interface, an
exact restricted-derivation induction interface, and truth of the chosen
theory's internally recognized axioms.  The compatibility wrapper recovers
that induction interface from an externally fixed definability witness.
-/

namespace LeanProofs.BoundedPAConsistency.AbstractSoundnessAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LeanProofs.BoundedPAConsistency.AbstractSoundness

#check Laws
#check SequentTrue
#check RestrictedDerivationInduction
#check restrictedDerivation_sequent_step
#check restrictedDerivation_sequent_strongStep
#check restrictedDerivation_sound_of_induction
#check restrictedDerivation_sound
#check restrictedConsistent_of_soundness
#check restrictedConsistent_of_laws_of_induction
#check restrictedConsistent_of_laws

#print axioms restrictedDerivation_sequent_step
#print axioms restrictedDerivation_sequent_strongStep
#print axioms restrictedDerivation_sound_of_induction
#print axioms restrictedDerivation_sound
#print axioms restrictedConsistent_of_soundness
#print axioms restrictedConsistent_of_laws_of_induction
#print axioms restrictedConsistent_of_laws

end LeanProofs.BoundedPAConsistency.AbstractSoundnessAudit
