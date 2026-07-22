(** Assumption audit for the final premise-free bounded-consistency theorem. *)

From BoundedPAConsistency Require Import
  RawCodedRestrictedPAConsistencyTheorem.

Import PABoundedRawCodedRestrictedPAConsistencyTheorem.

Check PA_BProv_restrictedPAConsistencyFormula.
Print Assumptions PA_BProv_restrictedPAConsistencyFormula.
