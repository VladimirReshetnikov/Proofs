(** Assumption audit for the raw-model completeness bridge. *)

From BoundedPAConsistency Require Import RawModelCompleteness.

Import PABoundedRawModelCompleteness.

Check PA_BProv_of_raw_valid.
Print Assumptions PA_BProv_of_raw_valid.
