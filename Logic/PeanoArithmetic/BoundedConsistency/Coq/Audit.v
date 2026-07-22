(** Kernel-assumption audit for phase-one bounded PA consistency. *)

From BoundedPAConsistency Require Import BoundedConsistency.

Import PABoundedConsistency.

Check sigmaRank.
Check piRank.
Check quantifierGroups.
Check ranks_rename.
Check ranks_subst.
Check ProvTree.
Check eraseProvTree.
Check ProvTree_complete.
Check proofOccurrenceRank.
Check ProofAllBounded.
Check QuantifierBounded_mono.
Check ProofAllBounded_mono.
Check RestrictedProv.
Check RestrictedBProv.
Check restrictedProv_erase.
Check restrictedBProv_erase.
Check RestrictedProv_mono.
Check RestrictedBProv_mono.
Check ProofAllBounded_cofinal.
Check RestrictedProv_cofinal.
Check RestrictedBProv_cofinal.
Check ConclusionRestrictedProv_bot_iff.
Check ConclusionRestrictedBProv_bot_iff.
Check restrictedPA_consistent_standard.

Print Assumptions ranks_rename.
Print Assumptions ranks_subst.
Print Assumptions ProvTree_complete.
Print Assumptions ProofAllBounded_mono.
Print Assumptions restrictedBProv_erase.
Print Assumptions RestrictedBProv_mono.
Print Assumptions RestrictedBProv_cofinal.
Print Assumptions ConclusionRestrictedBProv_bot_iff.
Print Assumptions restrictedPA_consistent_standard.
