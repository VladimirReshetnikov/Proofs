(** Audit for pointwise internal provability of bounded consistency. *)

From BoundedPAConsistency Require Import
  RawCodedPAProvabilityRestrictedConsistency.

Import PABoundedRawCodedPAProvabilityRestrictedConsistency.

Check restrictedPAConsistencyProvabilityFormula.
Check PA_BProv_restrictedPAConsistencyProvabilityFormula.

Print Assumptions PA_BProv_restrictedPAConsistencyProvabilityFormula.
