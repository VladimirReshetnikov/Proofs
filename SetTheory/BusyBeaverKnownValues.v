(* ===================================================================== *)
(*  BusyBeaverKnownValues.v                                              *)
(*                                                                       *)
(*  Coq counterpart of the Lean small-state Rado busy-beaver witnesses.  *)
(*  The concrete machines prove the lower-bound half of the A028444       *)
(*  prefix through four states.  The one-state upper bound is proved      *)
(*  directly; the remaining upper bounds are kept as explicit certificate *)
(*  interfaces, just as in the Lean development.                          *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Bool.Bool Lia List ZArith.
From SetTheory Require Import BusyBeaver.
Import ListNotations.

Module BB := BusyBeaver.

Module BusyBeaverKnownValues.

Definition halt (write : bool) (mv : BB.move) : BB.action :=
  {| BB.action_write := write;
     BB.action_move := mv;
     BB.action_next := None |}.

Definition go (write : bool) (mv : BB.move) (next : nat) : BB.action :=
  {| BB.action_write := write;
     BB.action_move := mv;
     BB.action_next := Some next |}.

Definition sigma1Transition (_q : nat) (bit : bool) : BB.action :=
  match bit with
  | false => halt true BB.right
  | true => halt false BB.right
  end.

Lemma sigma1Transition_next_lt : forall q bit next,
  BB.action_next (sigma1Transition q bit) = Some next -> next < 1.
Proof.
  intros q [] next hnext; simpl in hnext; discriminate.
Qed.

Definition sigma1Champion : BB.machine 1 :=
  {| BB.transition := sigma1Transition;
     BB.transition_next_lt := sigma1Transition_next_lt |}.

Definition sigma2Transition (q : nat) (bit : bool) : BB.action :=
  match q, bit with
  | 0, false => go true BB.right 1
  | 0, true => go true BB.left 1
  | 1, false => go true BB.left 0
  | _, true => halt true BB.right
  | _, _ => halt false BB.right
  end.

Lemma sigma2Transition_next_lt : forall q bit next,
  BB.action_next (sigma2Transition q bit) = Some next -> next < 2.
Proof.
  intros [|[|q]] [] next hnext; simpl in hnext;
    try discriminate; inversion hnext; lia.
Qed.

Definition sigma2Champion : BB.machine 2 :=
  {| BB.transition := sigma2Transition;
     BB.transition_next_lt := sigma2Transition_next_lt |}.

Definition sigma3Transition (q : nat) (bit : bool) : BB.action :=
  match q, bit with
  | 0, false => go true BB.right 1
  | 0, true => halt true BB.right
  | 1, false => go false BB.right 2
  | 1, true => go true BB.right 1
  | 2, false => go true BB.left 2
  | _, true => go true BB.left 0
  | _, _ => halt false BB.right
  end.

Lemma sigma3Transition_next_lt : forall q bit next,
  BB.action_next (sigma3Transition q bit) = Some next -> next < 3.
Proof.
  intros [|[|[|q]]] [] next hnext; simpl in hnext;
    try discriminate; inversion hnext; lia.
Qed.

Definition sigma3Champion : BB.machine 3 :=
  {| BB.transition := sigma3Transition;
     BB.transition_next_lt := sigma3Transition_next_lt |}.

Definition sigma4Transition (q : nat) (bit : bool) : BB.action :=
  match q, bit with
  | 0, false => go true BB.right 1
  | 0, true => go true BB.left 1
  | 1, false => go true BB.left 0
  | 1, true => go false BB.left 2
  | 2, false => halt true BB.right
  | 2, true => go true BB.left 3
  | 3, false => go true BB.right 3
  | _, true => go false BB.right 0
  | _, _ => halt false BB.right
  end.

Lemma sigma4Transition_next_lt : forall q bit next,
  BB.action_next (sigma4Transition q bit) = Some next -> next < 4.
Proof.
  intros [|[|[|[|q]]]] [] next hnext; simpl in hnext;
    try discriminate; inversion hnext; lia.
Qed.

Definition sigma4Champion : BB.machine 4 :=
  {| BB.transition := sigma4Transition;
     BB.transition_next_lt := sigma4Transition_next_lt |}.

Theorem sigma1Champion_haltsWithScore :
  BB.Machine.HaltsWithScore sigma1Champion 1.
Proof.
  exists 1. vm_compute. split; reflexivity.
Qed.

Theorem sigma2Champion_haltsWithScore :
  BB.Machine.HaltsWithScore sigma2Champion 4.
Proof.
  exists 6. vm_compute. split; reflexivity.
Qed.

Theorem sigma3Champion_haltsWithScore :
  BB.Machine.HaltsWithScore sigma3Champion 6.
Proof.
  exists 14. vm_compute. split; reflexivity.
Qed.

Theorem sigma4Champion_haltsWithScore :
  BB.Machine.HaltsWithScore sigma4Champion 13.
Proof.
  exists 107. vm_compute. split; reflexivity.
Qed.

Theorem attainableScore_one_one : BB.AttainableScore 1 1.
Proof.
  exists sigma1Champion. exact sigma1Champion_haltsWithScore.
Qed.

Theorem attainableScore_two_four : BB.AttainableScore 2 4.
Proof.
  exists sigma2Champion. exact sigma2Champion_haltsWithScore.
Qed.

Theorem attainableScore_three_six : BB.AttainableScore 3 6.
Proof.
  exists sigma3Champion. exact sigma3Champion_haltsWithScore.
Qed.

Theorem attainableScore_four_thirteen : BB.AttainableScore 4 13.
Proof.
  exists sigma4Champion. exact sigma4Champion_haltsWithScore.
Qed.

Theorem one_le_sigma_one : forall Sigma,
  BB.IsSigma Sigma -> 1 <= Sigma 1.
Proof.
  intros Sigma hSigma.
  exact (BB.sigma_upper Sigma hSigma 1 1 attainableScore_one_one).
Qed.

Theorem four_le_sigma_two : forall Sigma,
  BB.IsSigma Sigma -> 4 <= Sigma 2.
Proof.
  intros Sigma hSigma.
  exact (BB.sigma_upper Sigma hSigma 2 4 attainableScore_two_four).
Qed.

Theorem six_le_sigma_three : forall Sigma,
  BB.IsSigma Sigma -> 6 <= Sigma 3.
Proof.
  intros Sigma hSigma.
  exact (BB.sigma_upper Sigma hSigma 3 6 attainableScore_three_six).
Qed.

Theorem thirteen_le_sigma_four : forall Sigma,
  BB.IsSigma Sigma -> 13 <= Sigma 4.
Proof.
  intros Sigma hSigma.
  exact (BB.sigma_upper Sigma hSigma 4 13 attainableScore_four_thirteen).
Qed.

Theorem a028444_prefix_lower_bounds_through_four : forall Sigma,
  BB.IsSigma Sigma ->
  1 <= Sigma 1 /\ 4 <= Sigma 2 /\ 6 <= Sigma 3 /\ 13 <= Sigma 4.
Proof.
  intros Sigma hSigma.
  repeat split.
  - exact (one_le_sigma_one Sigma hSigma).
  - exact (four_le_sigma_two Sigma hSigma).
  - exact (six_le_sigma_three Sigma hSigma).
  - exact (thirteen_le_sigma_four Sigma hSigma).
Qed.

Lemma oneState_zero_halts_run_succ :
  forall (M : BB.machine 1),
    BB.action_next (BB.transition 1 M 0 false) = None ->
    forall t,
      BB.cfg_state 1 (BB.Machine.run M (S t)) = None /\
      length (BB.cfg_tape 1 (BB.Machine.run M (S t))) <= 1.
Proof.
  intros M hnext t.
  induction t as [|t [ihState ihLen]].
  - simpl.
    unfold BB.Machine.step, BB.initial, BB.start_state, BB.Tape.read.
    simpl. rewrite hnext.
    split; [reflexivity | ].
    destruct (BB.action_write (BB.transition 1 M 0 false));
      unfold BB.Tape.write; simpl; lia.
  - change (BB.cfg_state 1
      (BB.Machine.step M (BB.Machine.run M (S t))) = None /\
      length (BB.cfg_tape 1
        (BB.Machine.step M (BB.Machine.run M (S t)))) <= 1).
    rewrite (BB.Machine.step_of_halted 1 M (BB.Machine.run M (S t)) ihState).
    split; [exact ihState | exact ihLen].
Qed.

Lemma oneState_zero_continue_right_run :
  forall (M : BB.machine 1),
    BB.action_next (BB.transition 1 M 0 false) = Some 0 ->
    BB.action_move (BB.transition 1 M 0 false) = BB.right ->
    forall t,
      BB.cfg_state 1 (BB.Machine.run M t) = Some 0 /\
      BB.cfg_head 1 (BB.Machine.run M t) = Z.of_nat t /\
      forall q,
        In q (BB.cfg_tape 1 (BB.Machine.run M t)) ->
        (q < BB.cfg_head 1 (BB.Machine.run M t))%Z.
Proof.
  intros M hnext hmove t.
  induction t as [|t [ihState [ihHead ihTape]]].
  - simpl. split; [reflexivity | ].
    split; [reflexivity | ].
    intros q hq. contradiction.
  - simpl.
    set (old := BB.Machine.run M t) in *.
    assert (hnot : ~ In (BB.cfg_head 1 old) (BB.cfg_tape 1 old)).
    {
      intro hmem.
      specialize (ihTape (BB.cfg_head 1 old) hmem).
      lia.
    }
    assert (hread :
      BB.Tape.read (BB.cfg_tape 1 old) (BB.cfg_head 1 old) = false).
    {
      unfold BB.Tape.read.
      destruct (in_dec Z.eq_dec (BB.cfg_head 1 old) (BB.cfg_tape 1 old))
        as [hin | _]; [contradiction | reflexivity].
    }
    split.
    + unfold BB.Machine.step.
      rewrite ihState, hread, hnext.
      reflexivity.
    + split.
      * unfold BB.Machine.step.
        rewrite ihState, hread, hmove.
        simpl. rewrite ihHead. unfold BB.move_apply. lia.
      * intros q hq.
        unfold BB.Machine.step in hq |- *.
        rewrite ihState, hread, hmove in hq |- *.
        simpl in hq |- *.
        destruct (BB.action_write (BB.transition 1 M 0 false)) eqn:hwrite.
        -- unfold BB.Tape.write in hq.
           destruct (in_dec Z.eq_dec (BB.cfg_head 1 old) (BB.cfg_tape 1 old))
             as [hin | _]; [contradiction | ].
           simpl in hq.
           destruct hq as [hq | hq].
           ++ subst q. rewrite ihHead. unfold BB.move_apply. lia.
           ++ specialize (ihTape q hq). unfold BB.move_apply. lia.
        -- unfold BB.Tape.write in hq.
           apply filter_In in hq.
           destruct hq as [hq _].
           specialize (ihTape q hq). unfold BB.move_apply. lia.
Qed.

Lemma oneState_zero_continue_left_run :
  forall (M : BB.machine 1),
    BB.action_next (BB.transition 1 M 0 false) = Some 0 ->
    BB.action_move (BB.transition 1 M 0 false) = BB.left ->
    forall t,
      BB.cfg_state 1 (BB.Machine.run M t) = Some 0 /\
      BB.cfg_head 1 (BB.Machine.run M t) = (- Z.of_nat t)%Z /\
      forall q,
        In q (BB.cfg_tape 1 (BB.Machine.run M t)) ->
        (BB.cfg_head 1 (BB.Machine.run M t) < q)%Z.
Proof.
  intros M hnext hmove t.
  induction t as [|t [ihState [ihHead ihTape]]].
  - simpl. split; [reflexivity | ].
    split; [lia | ].
    intros q hq. contradiction.
  - simpl.
    set (old := BB.Machine.run M t) in *.
    assert (hnot : ~ In (BB.cfg_head 1 old) (BB.cfg_tape 1 old)).
    {
      intro hmem.
      specialize (ihTape (BB.cfg_head 1 old) hmem).
      lia.
    }
    assert (hread :
      BB.Tape.read (BB.cfg_tape 1 old) (BB.cfg_head 1 old) = false).
    {
      unfold BB.Tape.read.
      destruct (in_dec Z.eq_dec (BB.cfg_head 1 old) (BB.cfg_tape 1 old))
        as [hin | _]; [contradiction | reflexivity].
    }
    split.
    + unfold BB.Machine.step.
      rewrite ihState, hread, hnext.
      reflexivity.
    + split.
      * unfold BB.Machine.step.
        rewrite ihState, hread, hmove.
        simpl. rewrite ihHead. unfold BB.move_apply. lia.
      * intros q hq.
        unfold BB.Machine.step in hq |- *.
        rewrite ihState, hread, hmove in hq |- *.
        simpl in hq |- *.
        destruct (BB.action_write (BB.transition 1 M 0 false)) eqn:hwrite.
        -- unfold BB.Tape.write in hq.
           destruct (in_dec Z.eq_dec (BB.cfg_head 1 old) (BB.cfg_tape 1 old))
             as [hin | _]; [contradiction | ].
           simpl in hq.
           destruct hq as [hq | hq].
           ++ subst q. rewrite ihHead. unfold BB.move_apply. lia.
           ++ specialize (ihTape q hq). unfold BB.move_apply. lia.
        -- unfold BB.Tape.write in hq.
           apply filter_In in hq.
           destruct hq as [hq _].
           specialize (ihTape q hq). unfold BB.move_apply. lia.
Qed.

Lemma oneState_zero_continue_never_halts :
  forall (M : BB.machine 1) next,
    BB.action_next (BB.transition 1 M 0 false) = Some next ->
    forall t, BB.cfg_state 1 (BB.Machine.run M t) = Some 0.
Proof.
  intros M next hnext t.
  assert (next = 0) as ->.
  {
    pose proof (BB.transition_next_lt 1 M 0 false next hnext).
    lia.
  }
  destruct (BB.action_move (BB.transition 1 M 0 false)) eqn:hmove.
  - exact (proj1 (oneState_zero_continue_left_run M hnext hmove t)).
  - exact (proj1 (oneState_zero_continue_right_run M hnext hmove t)).
Qed.

Theorem upperBound_one : forall score,
  BB.AttainableScore 1 score -> score <= 1.
Proof.
  intros score [M [t [hState hScore]]].
  destruct (BB.action_next (BB.transition 1 M 0 false)) as [next | ] eqn:hnext.
  - pose proof (oneState_zero_continue_never_halts M next hnext t) as hnever.
    rewrite hnever in hState. discriminate.
  - destruct t as [|t].
    + simpl in hState. discriminate.
    + destruct (oneState_zero_halts_run_succ M hnext t) as [_ hle].
      rewrite hScore in hle.
      exact hle.
Qed.

Definition ExactScore (states score : nat) : Prop :=
  BB.AttainableScore states score /\
    forall other, BB.AttainableScore states other -> other <= score.

Module ExactScore.

Theorem sigma_eq : forall Sigma,
  BB.IsSigma Sigma ->
  forall states score,
    0 < states -> ExactScore states score -> Sigma states = score.
Proof.
  intros Sigma hSigma states score hpos [hAtt hUpper].
  apply Nat.le_antisymm.
  - exact (hUpper (Sigma states)
      (BB.sigma_attained Sigma hSigma states hpos)).
  - exact (BB.sigma_upper Sigma hSigma states score hAtt).
Qed.

End ExactScore.

Theorem exactScore_one : ExactScore 1 1.
Proof.
  split.
  - exact attainableScore_one_one.
  - intros other hOther. exact (upperBound_one other hOther).
Qed.

Theorem sigma_one_eq_one : forall Sigma,
  BB.IsSigma Sigma -> Sigma 1 = 1.
Proof.
  intros Sigma hSigma.
  exact (ExactScore.sigma_eq Sigma hSigma 1 1 (Nat.lt_0_succ 0) exactScore_one).
Qed.

Record A028444UpperBoundsThroughFour : Prop := {
  a028444_upper_one :
    forall score, BB.AttainableScore 1 score -> score <= 1;
  a028444_upper_two :
    forall score, BB.AttainableScore 2 score -> score <= 4;
  a028444_upper_three :
    forall score, BB.AttainableScore 3 score -> score <= 6;
  a028444_upper_four :
    forall score, BB.AttainableScore 4 score -> score <= 13
}.

Record A028444UpperBoundsTwoThroughFour : Prop := {
  a028444_upper_two_remaining :
    forall score, BB.AttainableScore 2 score -> score <= 4;
  a028444_upper_three_remaining :
    forall score, BB.AttainableScore 3 score -> score <= 6;
  a028444_upper_four_remaining :
    forall score, BB.AttainableScore 4 score -> score <= 13
}.

Module A028444UpperBoundsThroughFour.

Theorem of_twoThroughFour :
  A028444UpperBoundsTwoThroughFour -> A028444UpperBoundsThroughFour.
Proof.
  intro hUpper.
  refine {| a028444_upper_one := upperBound_one;
            a028444_upper_two := _;
            a028444_upper_three := _;
            a028444_upper_four := _ |}.
  - exact (a028444_upper_two_remaining hUpper).
  - exact (a028444_upper_three_remaining hUpper).
  - exact (a028444_upper_four_remaining hUpper).
Defined.

End A028444UpperBoundsThroughFour.

Theorem exactScore_one_of_upperBounds :
  A028444UpperBoundsThroughFour -> ExactScore 1 1.
Proof.
  intro _hUpper. exact exactScore_one.
Qed.

Theorem exactScore_two_of_upperBounds :
  A028444UpperBoundsThroughFour -> ExactScore 2 4.
Proof.
  intro hUpper.
  split.
  - exact attainableScore_two_four.
  - intros other hOther. exact (a028444_upper_two hUpper other hOther).
Qed.

Theorem exactScore_three_of_upperBounds :
  A028444UpperBoundsThroughFour -> ExactScore 3 6.
Proof.
  intro hUpper.
  split.
  - exact attainableScore_three_six.
  - intros other hOther. exact (a028444_upper_three hUpper other hOther).
Qed.

Theorem exactScore_four_of_upperBounds :
  A028444UpperBoundsThroughFour -> ExactScore 4 13.
Proof.
  intro hUpper.
  split.
  - exact attainableScore_four_thirteen.
  - intros other hOther. exact (a028444_upper_four hUpper other hOther).
Qed.

Theorem exactScore_two_of_remainingUpperBounds :
  A028444UpperBoundsTwoThroughFour -> ExactScore 2 4.
Proof.
  intro hUpper.
  exact (exactScore_two_of_upperBounds
    (A028444UpperBoundsThroughFour.of_twoThroughFour hUpper)).
Qed.

Theorem exactScore_three_of_remainingUpperBounds :
  A028444UpperBoundsTwoThroughFour -> ExactScore 3 6.
Proof.
  intro hUpper.
  exact (exactScore_three_of_upperBounds
    (A028444UpperBoundsThroughFour.of_twoThroughFour hUpper)).
Qed.

Theorem exactScore_four_of_remainingUpperBounds :
  A028444UpperBoundsTwoThroughFour -> ExactScore 4 13.
Proof.
  intro hUpper.
  exact (exactScore_four_of_upperBounds
    (A028444UpperBoundsThroughFour.of_twoThroughFour hUpper)).
Qed.

Theorem a028444_values_through_four_from_upperBounds : forall Sigma,
  BB.IsSigma Sigma ->
  A028444UpperBoundsThroughFour ->
  Sigma 1 = 1 /\ Sigma 2 = 4 /\ Sigma 3 = 6 /\ Sigma 4 = 13.
Proof.
  intros Sigma hSigma hUpper.
  split.
  - exact (sigma_one_eq_one Sigma hSigma).
  - split.
    + exact (ExactScore.sigma_eq Sigma hSigma 2 4
        (Nat.lt_0_succ 1) (exactScore_two_of_upperBounds hUpper)).
    + split.
      * exact (ExactScore.sigma_eq Sigma hSigma 3 6
          (Nat.lt_0_succ 2) (exactScore_three_of_upperBounds hUpper)).
      * exact (ExactScore.sigma_eq Sigma hSigma 4 13
          (Nat.lt_0_succ 3) (exactScore_four_of_upperBounds hUpper)).
Qed.

Theorem a028444_values_through_four_from_remainingUpperBounds : forall Sigma,
  BB.IsSigma Sigma ->
  A028444UpperBoundsTwoThroughFour ->
  Sigma 1 = 1 /\ Sigma 2 = 4 /\ Sigma 3 = 6 /\ Sigma 4 = 13.
Proof.
  intros Sigma hSigma hUpper.
  exact (a028444_values_through_four_from_upperBounds Sigma hSigma
    (A028444UpperBoundsThroughFour.of_twoThroughFour hUpper)).
Qed.

End BusyBeaverKnownValues.
