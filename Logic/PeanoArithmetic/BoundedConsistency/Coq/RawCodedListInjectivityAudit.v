(** Assumption audit for arbitrary-arity raw list-code injectivity. *)

From BoundedPAConsistency Require Import RawCodedListInjectivity.

Import PABoundedRawCodedListInjectivity.

Check rawListNode_not_zero.
Check rawListCode_injective.
Check rawListCode_cons_injective.
Check rawListCode_standard_payload.

Print Assumptions rawListNode_not_zero.
Print Assumptions rawListCode_injective.
Print Assumptions rawListCode_cons_injective.
Print Assumptions rawListCode_standard_payload.
