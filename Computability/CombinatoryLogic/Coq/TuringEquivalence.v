(* ===================================================================== *)
(*  TuringEquivalence.v                                                  *)
(*                                                                       *)
(*  Exact extensional equivalence among partial recursive relations,     *)
(*  the weak call-by-value lambda calculus L, and finite Turing machines  *)
(*  from the Coq Library of Undecidability Proofs.                        *)
(*                                                                       *)
(*  The statements use the upstream relational computability predicates, *)
(*  so divergence/undefinedness is part of the equivalence rather than    *)
(*  being erased by a defined-case-only simulation.                       *)
(* ===================================================================== *)

From Undecidability Require Import L.L TM.TM MuRec.MuRec.
From Undecidability.Synthetic Require Import Models_Equivalent.
From CombinatoryLogic Require Import RecursiveEquivalence.

Set Implicit Arguments.

Module TuringEquivalence.

(* The checked model-equivalence cycle contains concrete simulations in  *)
(* both directions between partial-recursive programs and Turing machines. *)
Theorem muRec_iff_TM_computable {k}
    (R : Vector.t nat k -> nat -> Prop) :
  MuRec_computable R <-> TM_computable R.
Proof.
  pose proof (equivalence R) as
    [Htm_bsm [Hbsm_mm [Hmm_fractran [Hfractran_dio [Hdio_murec
    [Hmurec_mm [Hmm_mma [Hmma_l [Hl_mma Hmma_tm]]]]]]]]].
  split.
  - intro H.
    exact (Hmma_tm (Hmm_mma (Hmurec_mm H))).
  - intro H.
    exact (Hdio_murec
      (Hfractran_dio
        (Hmm_fractran
          (Hbsm_mm
            (Htm_bsm H))))).
Qed.

(* Closed L programs and Turing machines compute exactly the same partial *)
(* functional relations.                                                  *)
Theorem L_computable_closed_iff_TM_computable {k}
    (R : Vector.t nat k -> nat -> Prop) :
  L_computable_closed R <-> TM_computable R.
Proof.
  split.
  - intro H.
    apply (proj1 (muRec_iff_TM_computable R)).
    exact (proj2 (RecursiveEquivalence.muRec_iff_L_computable_closed R) H).
  - intro H.
    apply (proj1 (RecursiveEquivalence.muRec_iff_L_computable_closed R)).
    exact (proj2 (muRec_iff_TM_computable R) H).
Qed.

(* Upstream closure conversion removes the closed-program side condition, *)
(* yielding the public lambda-calculus/Turing-machine equivalence.         *)
Theorem L_computable_iff_TM_computable {k}
    (R : Vector.t nat k -> nat -> Prop) :
  L_computable R <-> TM_computable R.
Proof.
  split.
  - intro H.
    apply (proj1 (muRec_iff_TM_computable R)).
    exact (proj2 (RecursiveEquivalence.muRec_iff_L_computable R) H).
  - intro H.
    apply (proj1 (RecursiveEquivalence.muRec_iff_L_computable R)).
    exact (proj2 (muRec_iff_TM_computable R) H).
Qed.

End TuringEquivalence.
