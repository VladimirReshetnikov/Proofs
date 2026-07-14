(* ===================================================================== *)
(*  RecursiveEquivalence.v                                             *)
(*                                                                       *)
(*  Exact extensional equivalence between partial recursive functions    *)
(*  and the weak call-by-value lambda calculus L formalized by Forster,   *)
(*  Smolka, and the Coq Library of Undecidability Proofs.                 *)
(*                                                                       *)
(*  Important semantic boundary: upstream [L] uses unscoped de Bruijn     *)
(*  terms, weak call-by-value big-step evaluation, and Scott numerals.     *)
(*  It is not [CombinatoryLogic.UntypedLambda], whose intrinsically        *)
(*  scoped terms carry a weak context-closed beta relation. In            *)
(*  particular, this file does not identify those two operational          *)
(*  semantics or claim that their individual reduction relations agree.   *)
(* ===================================================================== *)

From Undecidability Require Import L.L MuRec.MuRec.
From Undecidability.L.Util Require Import ClosedLAdmissible.
From Undecidability.Synthetic Require Import Models_Equivalent.

Set Implicit Arguments.

Module RecursiveEquivalence.

(* Upstream's [equivalence] theorem presents the model equivalence as a   *)
(* checked cycle of concrete simulations. These two projections package   *)
(* precisely the paths between partial recursive relations and closed L.  *)
Theorem muRec_iff_L_computable_closed {k}
    (R : Vector.t nat k -> nat -> Prop) :
  MuRec_computable R <-> L_computable_closed R.
Proof.
  pose proof (equivalence R) as
    [Htm_bsm [Hbsm_mm [Hmm_fractran [Hfractran_dio [Hdio_murec
    [Hmurec_mm [Hmm_mma [Hmma_l [Hl_mma Hmma_tm]]]]]]]]].
  split.
  - intro H.
    exact (Hmma_l (Hmm_mma (Hmurec_mm H))).
  - intro H.
    exact (Hdio_murec
      (Hfractran_dio
        (Hmm_fractran
          (Hbsm_mm
            (Htm_bsm
              (Hmma_tm (Hl_mma H))))))).
Qed.

(* Any well-behaved L realizer can itself be replaced by a closed one.     *)
(* Combining that theorem with the closed equivalence gives the exact      *)
(* equality of the two classes of partial functional relations.            *)
Theorem muRec_iff_L_computable {k}
    (R : Vector.t nat k -> nat -> Prop) :
  MuRec_computable R <-> L_computable R.
Proof.
  rewrite <- (L_computable_can_closed R).
  apply muRec_iff_L_computable_closed.
Qed.

End RecursiveEquivalence.
