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

(* --------------------------------------------------------------------- *)
(* A bounded two-state score check                                       *)
(* --------------------------------------------------------------------- *)

Definition actionOfCode2 (code : nat) : BB.action :=
  match code with
  | 0 => go false BB.left 0
  | 1 => go false BB.left 1
  | 2 => halt false BB.left
  | 3 => go false BB.right 0
  | 4 => go false BB.right 1
  | 5 => halt false BB.right
  | 6 => go true BB.left 0
  | 7 => go true BB.left 1
  | 8 => halt true BB.left
  | 9 => go true BB.right 0
  | 10 => go true BB.right 1
  | _ => halt true BB.right
  end.

Lemma actionOfCode2_next_lt : forall code next,
  BB.action_next (actionOfCode2 code) = Some next -> next < 2.
Proof.
  intros [|[|[|[|[|[|[|[|[|[|[|code]]]]]]]]]]] next hnext;
    simpl in hnext; try discriminate; inversion hnext; lia.
Qed.

Definition codedTransition2 (c00 c01 c10 c11 q : nat) (bit : bool) : BB.action :=
  match q, bit with
  | 0, false => actionOfCode2 c00
  | 0, true => actionOfCode2 c01
  | _, false => actionOfCode2 c10
  | _, true => actionOfCode2 c11
  end.

Lemma codedTransition2_next_lt : forall c00 c01 c10 c11 q bit next,
  BB.action_next (codedTransition2 c00 c01 c10 c11 q bit) = Some next ->
  next < 2.
Proof.
  intros c00 c01 c10 c11 [|q] [] next hnext;
    simpl in hnext;
    eapply actionOfCode2_next_lt; exact hnext.
Qed.

Definition codedMachine2 (c00 c01 c10 c11 : nat) : BB.machine 2 :=
  {| BB.transition := codedTransition2 c00 c01 c10 c11;
     BB.transition_next_lt := codedTransition2_next_lt c00 c01 c10 c11 |}.

Lemma action_code_complete_2 : forall a,
  (forall next, BB.action_next a = Some next -> next < 2) ->
  exists code, code < 12 /\ actionOfCode2 code = a.
Proof.
  intros [write mv next] hnext.
  destruct write; destruct mv; destruct next as [next|].
  - pose proof (hnext next eq_refl) as hlt.
    assert (next = 0 \/ next = 1) as [-> | ->] by lia.
    + exists 6. split; [lia | reflexivity].
    + exists 7. split; [lia | reflexivity].
  - exists 8. split; [lia | reflexivity].
  - pose proof (hnext next eq_refl) as hlt.
    assert (next = 0 \/ next = 1) as [-> | ->] by lia.
    + exists 9. split; [lia | reflexivity].
    + exists 10. split; [lia | reflexivity].
  - exists 11. split; [lia | reflexivity].
  - pose proof (hnext next eq_refl) as hlt.
    assert (next = 0 \/ next = 1) as [-> | ->] by lia.
    + exists 0. split; [lia | reflexivity].
    + exists 1. split; [lia | reflexivity].
  - exists 2. split; [lia | reflexivity].
  - pose proof (hnext next eq_refl) as hlt.
    assert (next = 0 \/ next = 1) as [-> | ->] by lia.
    + exists 3. split; [lia | reflexivity].
    + exists 4. split; [lia | reflexivity].
  - exists 5. split; [lia | reflexivity].
Qed.

Lemma run_state_lt : forall states (M : BB.machine states) t q,
  BB.cfg_state _ (BB.Machine.run M t) = Some q -> q < states.
Proof.
  intros states M t.
  induction t as [|t IH]; intros q hq.
  - simpl in hq.
    unfold BB.initial, BB.start_state in hq.
    destruct states as [|states]; simpl in hq; inversion hq; subst; lia.
  - simpl in hq.
    unfold BB.Machine.step in hq.
    destruct (BB.cfg_state states (BB.Machine.run M t)) as [old|] eqn:hOld.
    + exact (BB.transition_next_lt states M old
        (BB.Tape.read (BB.cfg_tape states (BB.Machine.run M t))
          (BB.cfg_head states (BB.Machine.run M t))) q hq).
    + rewrite hOld in hq. discriminate.
Qed.

Lemma run_ext_on_two : forall (M N : BB.machine 2),
  (forall q bit, q < 2 -> BB.transition 2 M q bit = BB.transition 2 N q bit) ->
  forall t, BB.Machine.run M t = BB.Machine.run N t.
Proof.
  intros M N htrans t.
  induction t as [|t IH]; [reflexivity | ].
  simpl.
  rewrite IH.
  unfold BB.Machine.step.
  destruct (BB.cfg_state 2 (BB.Machine.run N t)) as [q|] eqn:hq.
  - rewrite htrans by exact (run_state_lt 2 N t q hq).
    reflexivity.
  - reflexivity.
Qed.

Definition haltedScoreLeFourAtCode
    (c00 c01 c10 c11 t : nat) : bool :=
  let cfg := BB.Machine.run (codedMachine2 c00 c01 c10 c11) t in
  match BB.cfg_state _ cfg with
  | None => Nat.leb (length (BB.cfg_tape _ cfg)) 4
  | Some _ => true
  end.

Definition checkCodeTimes2 (c00 c01 c10 c11 : nat) : bool :=
  forallb (fun t => haltedScoreLeFourAtCode c00 c01 c10 c11 t)
    (seq 0 7).

Definition checkAllCodes2 : bool :=
  forallb (fun c00 =>
  forallb (fun c01 =>
  forallb (fun c10 =>
  forallb (fun c11 => checkCodeTimes2 c00 c01 c10 c11)
    (seq 0 12)) (seq 0 12)) (seq 0 12)) (seq 0 12).

Lemma checkAllCodes2_true : checkAllCodes2 = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma checkAllCodes2_at : forall c00 c01 c10 c11 t,
  c00 < 12 -> c01 < 12 -> c10 < 12 -> c11 < 12 -> t <= 6 ->
  haltedScoreLeFourAtCode c00 c01 c10 c11 t = true.
Proof.
  intros c00 c01 c10 c11 t hc00 hc01 hc10 hc11 ht.
  pose proof checkAllCodes2_true as hcheck.
  unfold checkAllCodes2 in hcheck.
  rewrite forallb_forall in hcheck.
  assert (Hin00 : In c00 (seq 0 12)) by (apply in_seq; lia).
  specialize (hcheck c00 Hin00).
  rewrite forallb_forall in hcheck.
  assert (Hin01 : In c01 (seq 0 12)) by (apply in_seq; lia).
  specialize (hcheck c01 Hin01).
  rewrite forallb_forall in hcheck.
  assert (Hin10 : In c10 (seq 0 12)) by (apply in_seq; lia).
  specialize (hcheck c10 Hin10).
  rewrite forallb_forall in hcheck.
  assert (Hin11 : In c11 (seq 0 12)) by (apply in_seq; lia).
  specialize (hcheck c11 Hin11).
  unfold checkCodeTimes2 in hcheck.
  rewrite forallb_forall in hcheck.
  apply hcheck.
  apply in_seq. lia.
Qed.

Lemma haltedScoreLeFourAtCode_sound : forall c00 c01 c10 c11 t,
  haltedScoreLeFourAtCode c00 c01 c10 c11 t = true ->
  BB.cfg_state _ (BB.Machine.run (codedMachine2 c00 c01 c10 c11) t) = None ->
  length (BB.cfg_tape _ (BB.Machine.run (codedMachine2 c00 c01 c10 c11) t)) <= 4.
Proof.
  intros c00 c01 c10 c11 t hcheck hhalt.
  unfold haltedScoreLeFourAtCode in hcheck.
  rewrite hhalt in hcheck.
  apply Nat.leb_le.
  exact hcheck.
Qed.

Theorem two_state_halted_score_le_four_by_time : forall (M : BB.machine 2) t,
  t <= 6 ->
  BB.cfg_state _ (BB.Machine.run M t) = None ->
  length (BB.cfg_tape _ (BB.Machine.run M t)) <= 4.
Proof.
  intros M t ht hhalt.
  destruct (action_code_complete_2 (BB.transition 2 M 0 false)
    (fun next h => BB.transition_next_lt 2 M 0 false next h))
    as [c00 [hc00 hc00eq]].
  destruct (action_code_complete_2 (BB.transition 2 M 0 true)
    (fun next h => BB.transition_next_lt 2 M 0 true next h))
    as [c01 [hc01 hc01eq]].
  destruct (action_code_complete_2 (BB.transition 2 M 1 false)
    (fun next h => BB.transition_next_lt 2 M 1 false next h))
    as [c10 [hc10 hc10eq]].
  destruct (action_code_complete_2 (BB.transition 2 M 1 true)
    (fun next h => BB.transition_next_lt 2 M 1 true next h))
    as [c11 [hc11 hc11eq]].
  set (N := codedMachine2 c00 c01 c10 c11).
  assert (hrun : forall k, BB.Machine.run M k = BB.Machine.run N k).
  {
    apply run_ext_on_two.
    intros q bit hq.
    destruct q as [|[|q]]; try lia; destruct bit;
      simpl; symmetry; assumption.
  }
  rewrite hrun in hhalt |- *.
  eapply haltedScoreLeFourAtCode_sound.
  - apply checkAllCodes2_at; eassumption.
  - exact hhalt.
Qed.

Theorem upperBound_two_of_halting_time_bound :
  (forall (M : BB.machine 2) t,
    BB.cfg_state _ (BB.Machine.run M t) = None -> t <= 6) ->
  forall score, BB.AttainableScore 2 score -> score <= 4.
Proof.
  intros hTime score [M [t [hState hScore]]].
  pose proof (hTime M t hState) as ht.
  pose proof (two_state_halted_score_le_four_by_time M t ht hState) as hle.
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
Qed.

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
