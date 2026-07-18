(** Assumption audit for standalone existential-elimination soundness. *)

From BoundedPAConsistency Require Import
  RawCodedRestrictedProofExERuleSoundness.

Import PABoundedRawCodedRestrictedProofExERuleSoundness.

Check raw_exE_contextAllCodesBelow_cons_tail.
Check raw_restrictedProofCovered_exE_sound.

Print Assumptions raw_exE_contextAllCodesBelow_cons_tail.
Print Assumptions raw_restrictedProofCovered_exE_sound.
