(* ===================================================================== *)
(*  The expensive finite certificate for the four-state score bound.     *)
(*                                                                       *)
(*  The semantic checker and its soundness proof live in                  *)
(*  [BusyBeaverBB4Score], while the VM equality is cached separately in   *)
(*  [BusyBeaverBB4ScoreComputation].  This module connects that equality  *)
(*  to the semantic queue invariant.                                      *)
(* ===================================================================== *)

From Stdlib Require Import List.
Import ListNotations.

From CoqBB4 Require Import
  BB4_Statement BB4_Deciders_Pipeline BB4_TNF_Enumeration TM.
From BusyBeaver Require Import
  BusyBeaverBB4Score BusyBeaverBB4ScoreComputation.

Module BusyBeaverBB4ScoreCertificate.

Module S := BusyBeaverBB4Score.
Module Q := BusyBeaverBB4ScoreComputation.

(** Establish the initial and one-round invariant boundaries while the queue
    aliases are transparent.  We seal the aliases immediately afterwards:
    otherwise Rocq's conversion checker unfolds [score_q_suc] recursively
    underneath [Nat.iter], turning the harmless 200-round specialization into
    an enormous reduction.  Opacity changes proof-checking performance only;
    the separately kernel-checked computation equality remains unchanged. *)
Lemma score_q_0_WF : S.ScoreQueue_WF Q.score_q_0 root.
Proof.
  unfold Q.score_q_0.
  exact S.root_score_q_upd1_simplified_WF.
Qed.

Lemma score_q_suc_WF : forall q,
  S.ScoreQueue_WF q root -> S.ScoreQueue_WF (Q.score_q_suc q) root.
Proof.
  intros q hq.
  unfold Q.score_q_suc.
  apply S.score_upds_spec.
  - exact hq.
  - unfold S.scoreFuel. exact decider_all_spec.
Qed.

Global Opaque Q.score_q_0 Q.score_q_suc.

Lemma score_q_iter_WF : forall rounds,
  S.ScoreQueue_WF (Nat.iter rounds Q.score_q_suc Q.score_q_0) root.
Proof.
  intro rounds.
  induction rounds as [|rounds ih].
  - change (S.ScoreQueue_WF Q.score_q_0 root).
    exact score_q_0_WF.
  - change (S.ScoreQueue_WF
      (Q.score_q_suc (Nat.iter rounds Q.score_q_suc Q.score_q_0)) root).
    apply score_q_suc_WF.
    exact ih.
Qed.

Lemma score_q_200_WF : S.ScoreQueue_WF Q.score_q_200 root.
Proof.
  unfold Q.score_q_200.
  exact (score_q_iter_WF 200).
Qed.

Theorem root_score_upper_bound : S.TNF_Node_SB root.
Proof.
  pose proof score_q_200_WF as hWF.
  rewrite Q.score_q_200_empty in hWF.
  unfold S.ScoreQueue_WF in hWF; cbn in hWF.
  destruct hWF as [_ hRoot].
  apply hRoot; [reflexivity|].
  intros x hx. contradiction.
Qed.

Theorem allTM_first_halt_list_score_le_twelve : forall tm n e,
  S.FirstHaltAt tm n e -> S.listScore e <= 12.
Proof.
  intros tm n e hFirst.
  pose proof root_score_upper_bound as hRoot.
  unfold S.TNF_Node_SB in hRoot.
  apply (hRoot tm n e).
  - unfold LE. intros q i. right. reflexivity.
  - exact hFirst.
Qed.

End BusyBeaverBB4ScoreCertificate.
