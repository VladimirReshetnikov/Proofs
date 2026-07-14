(* ===================================================================== *)
(*  TuringEquivalenceAudit.v                                             *)
(*                                                                       *)
(*  Public theorem checks and kernel-assumption audit for the exact      *)
(*  recursion/lambda-calculus/Turing-machine equivalences.                *)
(* ===================================================================== *)

From CombinatoryLogic Require Import TuringEquivalence.

Check TuringEquivalence.muRec_iff_TM_computable.
Check TuringEquivalence.L_computable_closed_iff_TM_computable.
Check TuringEquivalence.L_computable_iff_TM_computable.

Print Assumptions TuringEquivalence.muRec_iff_TM_computable.
Print Assumptions TuringEquivalence.L_computable_closed_iff_TM_computable.
Print Assumptions TuringEquivalence.L_computable_iff_TM_computable.
