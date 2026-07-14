(* ===================================================================== *)
(*  RecursiveEquivalenceAudit.v                                        *)
(*                                                                       *)
(*  Public theorem checks and kernel-assumption audit for the exact      *)
(*  partial-recursion/weak-CBV-lambda equivalence.                       *)
(* ===================================================================== *)

From CombinatoryLogic Require Import RecursiveEquivalence.

Check RecursiveEquivalence.muRec_iff_L_computable_closed.
Check RecursiveEquivalence.muRec_iff_L_computable.

Print Assumptions RecursiveEquivalence.muRec_iff_L_computable_closed.
Print Assumptions RecursiveEquivalence.muRec_iff_L_computable.
