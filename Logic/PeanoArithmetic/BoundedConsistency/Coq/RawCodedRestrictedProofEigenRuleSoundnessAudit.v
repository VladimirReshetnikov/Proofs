(** Audit the completed All-I eigenvariable case. *)

From BoundedPAConsistency Require Import
  RawCodedRestrictedProofEigenRuleSoundness.

Import PABoundedRawCodedRestrictedProofEigenRuleSoundness.

Check raw_restrictedProofCovered_allI_sound.

Print Assumptions raw_restrictedProofCovered_allI_sound.
