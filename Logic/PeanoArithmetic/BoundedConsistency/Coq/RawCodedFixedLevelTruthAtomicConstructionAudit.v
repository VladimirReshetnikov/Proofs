(** Assumption audit for rank-zero positive fixed-truth leaves. *)

From BoundedPAConsistency Require Import
  RawCodedFixedLevelTruthAtomicConstruction.

Import PABoundedRawCodedFixedLevelTruthAtomicConstruction.

Check raw_fixedLevelRankZero_sigma_domain.
Check raw_fixedLevelRankZero_pi_domain.
Check raw_fixedLevelRankZero_decides.
Check raw_fixedLevelEq_decides.
Check raw_fixedLevelBot_decides.

Print Assumptions raw_fixedLevelRankZero_decides.
Print Assumptions raw_fixedLevelEq_decides.
Print Assumptions raw_fixedLevelBot_decides.
