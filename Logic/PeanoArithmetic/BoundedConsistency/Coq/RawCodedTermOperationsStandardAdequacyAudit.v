(** Assumption audit for standard quotation of coded term operations. *)

From PAHF Require Import PAHF.
From BoundedPAConsistency Require Import
  RawCodedTermOperationsStandardAdequacy.

Import PA.
Import PABoundedRawCodedTermOperationsStandardAdequacy.

Check standardTermShift.
Check standardTermOpening.
Check standardTermShift_zero_one.

Check raw_standardTermShift_closed_step.
Check raw_standardTermOpening_closed_step.
Check raw_codedTermShift_standard.
Check raw_codedTermOpening_standard.

Print Assumptions standardTermShift_zero_one.
Print Assumptions raw_standardTermShift_closed_step.
Print Assumptions raw_standardTermOpening_closed_step.
Print Assumptions raw_codedTermShift_standard.
Print Assumptions raw_codedTermOpening_standard.
