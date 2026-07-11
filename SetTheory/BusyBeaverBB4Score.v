(* ===================================================================== *)
(*  A score-aware certificate layer for the vendored BB(4) enumeration.  *)
(*                                                                       *)
(*  CoqBB4's TNF enumeration proves the 106-successful-transition time   *)
(*  bound.  Whenever its first (loop) decider reports an undefined       *)
(*  transition, this layer independently replays that partial machine    *)
(*  on the finite [ListES] tape and checks that at most twelve cells are  *)
(*  marked.  A local Rado halt action can add at most one further mark,   *)
(*  giving the intended score bound thirteen.                            *)
(* ===================================================================== *)

From Stdlib Require Import List Lia ZArith Bool.
Import ListNotations.

From CoqBB4 Require Import
  BB4_Statement BB4_Encodings BB4_Make_TM TM TNF List_Tape Tactics
  Deciders_Common BB4_Deciders_Pipeline BB4_TNF_Enumeration.

Module BusyBeaverBB4Score.

Definition sigmaScore (x : Σ) : nat :=
  match x with
  | Σ0 => 0
  | Σ1 => 1
  end.

Fixpoint listScore0 (xs : list Σ) : nat :=
  match xs with
  | [] => 0
  | x :: xs' => sigmaScore x + listScore0 xs'
  end.

Definition listScore (e : ListES) : nat :=
  listScore0 (l e) + sigmaScore (m e) + listScore0 (r e).

Definition initialListES : ListES :=
  Build_ListES [] [] Σ0 St0.

(** [haltWithin fuel tm e] checks the current transition before consuming
    fuel.  Consequently fuel 106 covers precisely halting times 0..106,
    which are the undefined-transition times certified by CoqBB4. *)
Fixpoint haltWithin (fuel : nat) (tm : TM Σ) (e : ListES) : option ListES :=
  match tm (s e) (m e) with
  | None => Some e
  | Some tr =>
      match fuel with
      | O => None
      | S fuel' => haltWithin fuel' tm (ListES_step' tr e)
      end
  end.

Definition scoreFuel : nat := N.to_nat BB4_minus_one.
Definition scoreLimit : nat := 12.

Definition scoreOK (tm : TM Σ) : bool :=
  match haltWithin scoreFuel tm initialListES with
  | Some e => Nat.leb (listScore e) scoreLimit
  | None => false
  end.

Definition FirstHaltFrom
    (tm : TM Σ) (start : ListES) (n : nat) (e : ListES) : Prop :=
  ListES_Steps tm n start = Some e /\ tm (s e) (m e) = None.

Definition FirstHaltAt (tm : TM Σ) (n : nat) (e : ListES) : Prop :=
  FirstHaltFrom tm initialListES n e.

Lemma initialListES_toES :
  ListES_toES initialListES = InitES Σ Σ0.
Proof.
  exact ListES_toES_O.
Qed.

Lemma FirstHaltFrom_HaltsAt : forall tm start n e,
  FirstHaltFrom tm start n e ->
  HaltsAt Σ tm n (ListES_toES start).
Proof.
  intros tm start n e [hSteps hHalt].
  unfold HaltsAt.
  exists (ListES_toES e).
  split.
  - pose proof (ListES_Steps_spec tm n start) as hSpec.
    rewrite hSteps in hSpec.
    exact hSpec.
  - destruct e as [el er em es].
    unfold step, ListES_toES.
    cbn in hHalt |- *.
    rewrite hHalt.
    reflexivity.
Qed.

Lemma FirstHaltAt_HaltsAt : forall tm n e,
  FirstHaltAt tm n e ->
  HaltsAt Σ tm n (InitES Σ Σ0).
Proof.
  intros tm n e h.
  rewrite <- initialListES_toES.
  now apply FirstHaltFrom_HaltsAt with (e := e).
Qed.

Lemma haltWithin_some_FirstHaltFrom : forall fuel tm start e,
  haltWithin fuel tm start = Some e ->
  exists n, n <= fuel /\ FirstHaltFrom tm start n e.
Proof.
  induction fuel as [|fuel ih]; intros tm start e hRun.
  - cbn in hRun.
    destruct (tm (s start) (m start)) as [tr|] eqn:hStep.
    + discriminate.
    + inversion hRun; subst e.
      exists 0.
      split; [lia|].
      split; [reflexivity|exact hStep].
  - cbn in hRun.
    destruct (tm (s start) (m start)) as [tr|] eqn:hStep.
    + destruct (ih tm (ListES_step' tr start) e hRun) as
        [n [hn hFirst]].
      exists (S n).
      split; [lia|].
      destruct hFirst as [hSteps hHalt].
      split.
      * cbn. rewrite hStep. exact hSteps.
      * exact hHalt.
    + inversion hRun; subst e.
      exists 0.
      split; [lia|].
      split; [reflexivity|exact hStep].
Qed.

Lemma haltWithin_none_long_run : forall fuel tm start,
  haltWithin fuel tm start = None ->
  exists st,
    Steps Σ tm (S fuel) (ListES_toES start) st.
Proof.
  induction fuel as [|fuel ih]; intros tm start hRun.
  - cbn in hRun.
    destruct start as [el er em es].
    cbn in hRun |- *.
    destruct (tm es em) as [tr|] eqn:hStep; [|discriminate].
    exists (ListES_toES (ListES_step' tr (Build_ListES el er em es))).
    econstructor.
    + constructor.
    + pose proof (ListES_step'_spec tm el er em es) as hSpec.
      rewrite hStep in hSpec.
      exact hSpec.
  - cbn in hRun.
    destruct start as [el er em es].
    cbn in hRun |- *.
    destruct (tm es em) as [tr|] eqn:hStep; [|discriminate].
    specialize (ih tm (ListES_step' tr (Build_ListES el er em es)) hRun).
    destruct ih as [st hLong].
    exists st.
    replace (S (S fuel)) with (S fuel + 1) by lia.
    eapply Steps_trans.
    + econstructor.
      * constructor.
      * pose proof (ListES_step'_spec tm el er em es) as hSpec.
        rewrite hStep in hSpec.
        exact hSpec.
    + exact hLong.
Qed.

Lemma haltWithin_complete_of_halt : forall fuel tm start n,
  HaltsAt Σ tm n (ListES_toES start) ->
  n <= fuel ->
  exists e, haltWithin fuel tm start = Some e.
Proof.
  intros fuel tm start n hHalt hn.
  destruct (haltWithin fuel tm start) as [e|] eqn:hRun.
  - now exists e.
  - destruct (haltWithin_none_long_run fuel tm start hRun) as [st hLong].
    exfalso.
    assert (hLt : n < S fuel) by lia.
    exact (@Steps_NonHalt Σ tm n (S fuel)
      (ListES_toES start) st hLt hLong hHalt).
Qed.

Lemma scoreOK_sound : forall tm n,
  scoreOK tm = true ->
  HaltsAt Σ tm n (InitES Σ Σ0) ->
  n <= scoreFuel ->
  exists e, FirstHaltAt tm n e /\ listScore e <= scoreLimit.
Proof.
  intros tm n hOK hHalt hn.
  unfold scoreOK in hOK.
  destruct (haltWithin scoreFuel tm initialListES) as [e|] eqn:hRun;
    [|discriminate].
  apply Nat.leb_le in hOK.
  destruct (haltWithin_some_FirstHaltFrom scoreFuel tm initialListES e hRun)
    as [n' [hn' hFirst]].
  assert (hHalt' : HaltsAt Σ tm n' (InitES Σ Σ0)).
  { rewrite <- initialListES_toES.
    exact (FirstHaltFrom_HaltsAt tm initialListES n' e hFirst). }
  pose proof (HaltsAt_unique Σ hHalt hHalt') as hEq.
  subst n'.
  exists e.
  split; assumption.
Qed.

(** Semantic score obligation propagated by the TNF search. *)
Definition HaltListScoreUpperBound (P : TM Σ -> Prop) : Prop :=
  forall tm n e,
    P tm -> FirstHaltAt tm n e -> listScore e <= scoreLimit.

Definition TNF_Node_SB (x : TNF_Node) : Prop :=
  HaltListScoreUpperBound (LE Σ (TNF_tm x)).

Lemma HaltListScoreUpperBound_LE_NonHalt : forall tm,
  ~ HaltsFromInit Σ Σ0 tm ->
  HaltListScoreUpperBound (LE Σ tm).
Proof.
  intros base hNonhalt.
  unfold HaltListScoreUpperBound.
  intros tm n e hLE hFirst.
  exfalso.
  apply (LE_NonHalts Σ hLE hNonhalt).
  exists n.
  exact (FirstHaltAt_HaltsAt tm n e hFirst).
Qed.

Lemma TNF_Node_SB_NonHalt : forall x,
  ~ HaltsFromInit Σ Σ0 (TNF_tm x) -> TNF_Node_SB x.
Proof.
  intros x hNonhalt.
  unfold TNF_Node_SB.
  now apply HaltListScoreUpperBound_LE_NonHalt.
Qed.

Lemma ListES_Steps_LE : forall tm tm' n start e,
  LE Σ tm tm' ->
  ListES_Steps tm n start = Some e ->
  ListES_Steps tm' n start = Some e.
Proof.
  intros tm tm' n.
  induction n as [|n ih]; intros start e hLE hRun.
  - cbn in hRun |- *.
    exact hRun.
  - destruct start as [el er em es].
    cbn in hRun |- *.
    destruct (tm es em) as [tr|] eqn:hStep; [|discriminate].
    pose proof (hLE es em) as hCell.
    destruct hCell as [hSame|hNone].
    + rewrite <- hSame, hStep.
      eapply ih; eauto.
    + rewrite hStep in hNone.
      discriminate.
Qed.

(** The score analogue of [HaltTimeUpperBound_LE_Halt].  The [scoreOK]
    premise discharges the completion which leaves the currently undefined
    transition undefined; all defined completions are delegated to the
    corresponding updated partial table. *)
Lemma HaltListScoreUpperBound_LE_Halt : forall tm n qs tape,
  HaltsAt Σ tm n (InitES Σ Σ0) ->
  Steps Σ tm n (InitES Σ Σ0) (qs, tape) ->
  n <= scoreFuel ->
  scoreOK tm = true ->
  (forall tr,
    HaltListScoreUpperBound
      (LE Σ (TM_upd Σ Σ_eqb tm qs (tape Z0) (Some tr)))) ->
  HaltListScoreUpperBound (LE Σ tm).
Proof.
  intros tm n qs tape hHalt hSteps hn hOK hChildren.
  unfold HaltListScoreUpperBound.
  intros tm' n' e' hLE hFirst.
  destruct (tm' qs (tape Z0)) as [tr|] eqn:hCompletion.
  - apply (hChildren tr tm' n' e').
    + eapply LE_HaltsAtES_2; eauto.
      exact Σ_eqb_spec.
    + exact hFirst.
  - pose proof (LE_HaltsAtES_1 Σ hLE hHalt hSteps hCompletion)
      as hCompletionHalt.
    pose proof (FirstHaltAt_HaltsAt tm' n' e' hFirst) as hFirstHalt.
    pose proof (HaltsAt_unique Σ hCompletionHalt hFirstHalt) as hTime.
    subst n'.
    destruct (scoreOK_sound tm n hOK hHalt hn) as
      [e [hPartialFirst hScore]].
    destruct hPartialFirst as [hPartialRun hPartialUndefined].
    destruct hFirst as [hCompletionRun hCompletionUndefined].
    pose proof (ListES_Steps_LE tm tm' n initialListES e
      hLE hPartialRun) as hLiftedRun.
    rewrite hCompletionRun in hLiftedRun.
    inversion hLiftedRun; subst e'.
    exact hScore.
Qed.

Section ScoreSwap.

Variables s1 s2 : St.
Hypothesis s1_ne_s2 : s1 <> s2.
Hypothesis s1_ne_St0 : s1 <> St0.
Hypothesis s2_ne_St0 : s2 <> St0.

Definition ListES_swap (e : ListES) : ListES :=
  Build_ListES (l e) (r e) (m e) (St_swap s1 s2 (s e)).

Lemma ListES_swap_swap : forall e,
  ListES_swap (ListES_swap e) = e.
Proof.
  intros [el er em es].
  unfold ListES_swap; cbn.
  rewrite (St_swap_swap s1 s2 s1_ne_s2).
  reflexivity.
Qed.

Lemma ListES_swap_initial :
  ListES_swap initialListES = initialListES.
Proof.
  unfold ListES_swap, initialListES; cbn.
  pose proof (InitES_swap Σ Σ0 s1 s2 s1_ne_St0 s2_ne_St0) as hInit.
  unfold ExecState_swap, InitES in hInit; cbn in hInit.
  pose proof (f_equal (fun p : ExecState Σ => fst p) hInit) as hState.
  cbn in hState.
  now rewrite hState.
Qed.

Lemma listScore_swap : forall e,
  listScore (ListES_swap e) = listScore e.
Proof.
  intros [el er em es].
  reflexivity.
Qed.

Lemma ListES_step'_swap : forall tr e,
  ListES_step' (Trans_swap Σ s1 s2 tr) (ListES_swap e) =
  ListES_swap (ListES_step' tr e).
Proof.
  intros [next direction write] [el er em es].
  destruct direction, el, er; reflexivity.
Qed.

Lemma TM_swap_at_ListES_swap : forall tm e,
  TM_swap Σ s1 s2 tm (s (ListES_swap e)) (m (ListES_swap e)) =
  option_Trans_swap Σ s1 s2 (tm (s e) (m e)).
Proof.
  intros tm [el er em es].
  change (TM_swap Σ s1 s2 tm (St_swap s1 s2 es) em =
    option_Trans_swap Σ s1 s2 (tm es em)).
  unfold TM_swap.
  rewrite (St_swap_swap s1 s2 s1_ne_s2).
  reflexivity.
Qed.

Lemma ListES_Steps_swap : forall tm n e,
  ListES_Steps (TM_swap Σ s1 s2 tm) n (ListES_swap e) =
  option_map ListES_swap (ListES_Steps tm n e).
Proof.
  intros tm n.
  induction n as [|n ih]; intros e.
  - reflexivity.
  - cbn [ListES_Steps].
    rewrite TM_swap_at_ListES_swap.
    destruct (tm (s e) (m e)) as [tr|] eqn:hStep; [|reflexivity].
    cbn [option_Trans_swap].
    rewrite ListES_step'_swap.
    apply ih.
Qed.

Lemma FirstHaltFrom_swap : forall tm start n e,
  FirstHaltFrom tm start n e ->
  FirstHaltFrom (TM_swap Σ s1 s2 tm) (ListES_swap start) n
    (ListES_swap e).
Proof.
  intros tm start n e [hRun hHalt].
  split.
  - rewrite ListES_Steps_swap.
    rewrite hRun.
    reflexivity.
  - rewrite TM_swap_at_ListES_swap.
    rewrite hHalt.
    reflexivity.
Qed.

Lemma HaltListScoreUpperBound_LE_swap : forall tm,
  HaltListScoreUpperBound (LE Σ tm) ->
  HaltListScoreUpperBound (LE Σ (TM_swap Σ s1 s2 tm)).
Proof.
  intros tm hBound.
  unfold HaltListScoreUpperBound in hBound |- *.
  intros tm' n e hLE hFirst.
  assert (hLEBack : LE Σ tm (TM_swap Σ s1 s2 tm')).
  { apply (proj2 (LE_swap Σ s1 s2 s1_ne_s2 tm
      (TM_swap Σ s1 s2 tm'))).
    rewrite (TM_swap_swap Σ s1 s2 s1_ne_s2).
    exact hLE. }
  assert (hFirstBack :
      FirstHaltAt (TM_swap Σ s1 s2 tm') n (ListES_swap e)).
  { unfold FirstHaltAt in hFirst |- *.
    rewrite <- ListES_swap_initial.
    now apply FirstHaltFrom_swap. }
  pose proof (hBound _ _ _ hLEBack hFirstBack) as hScore.
  rewrite listScore_swap in hScore.
  exact hScore.
Qed.

End ScoreSwap.

(** State names not yet used by a TNF partial machine are interchangeable.
    The proof is the score analogue of CoqBB4's
    [HaltTimeUpperBound_LE_HaltsAtES_UnusedState]. *)
Lemma HaltListScoreUpperBound_LE_HaltsAtES_UnusedState :
  forall tm n qs tape s1 s2 d o,
  HaltsAt Σ tm n (InitES Σ Σ0) ->
  Steps Σ tm n (InitES Σ Σ0) (qs, tape) ->
  UnusedState tm s1 ->
  UnusedState tm s2 ->
  HaltListScoreUpperBound
    (LE Σ (TM_upd Σ Σ_eqb tm qs (tape Z0)
      (Some {| nxt := s1; dir := d; out := o |}))) ->
  HaltListScoreUpperBound
    (LE Σ (TM_upd Σ Σ_eqb tm qs (tape Z0)
      (Some {| nxt := s2; dir := d; out := o |}))).
Proof.
  intros tm n qs tape s1 s2 d o hHalt hSteps hUnused1 hUnused2 hBound.
  St_eq_dec s1 s2.
  1: subst; exact hBound.
  pose proof (Steps_UnusedState hSteps) as hUsedQ.
  assert (s1_ne_qs : s1 <> qs) by (intro h; subst; contradiction).
  assert (s2_ne_qs : s2 <> qs) by (intro h; subst; contradiction).
  destruct hUnused1 as [hUnused1a [hUnused1b hUnused1c]].
  destruct hUnused2 as [hUnused2a [hUnused2b hUnused2c]].
  assert (hMachines :
    TM_swap Σ s1 s2
      (TM_upd Σ Σ_eqb tm qs (tape Z0)
        (Some {| nxt := s1; dir := d; out := o |})) =
    TM_upd Σ Σ_eqb tm qs (tape Z0)
      (Some {| nxt := s2; dir := d; out := o |})).
  {
    fext. fext.
    unfold TM_upd, TM_swap, option_Trans_swap; cbn.
    unfold St_swap; cbn.
    St_eq_dec s1 x.
    { subst.
      St_eq_dec s2 qs; try congruence. cbn.
      rewrite hUnused1b, hUnused2b.
      St_eq_dec x qs; try congruence. cbn. reflexivity. }
    St_eq_dec s2 x.
    { subst.
      St_eq_dec s1 qs; try congruence. cbn.
      rewrite hUnused1b, hUnused2b.
      St_eq_dec x qs; try congruence. cbn. reflexivity. }
    St_eq_dec x qs.
    { subst. cbn.
      eq_dec Σ_eqb_spec Σ_eqb x0 (tape Z0).
      - subst. f_equal. cbn. f_equal.
        unfold St_swap.
        St_eq_dec s1 s1; congruence.
      - specialize (hUnused1a qs x0).
        specialize (hUnused2a qs x0).
        destruct (tm qs x0) as [[next direction write]|]; try reflexivity.
        f_equal. cbn in hUnused1a, hUnused2a.
        erewrite <- Trans_swap_id; eauto. }
    cbn.
    specialize (hUnused1a x x0).
    specialize (hUnused2a x x0).
    destruct (tm x x0) as [[next direction write]|]; try reflexivity.
    f_equal. cbn in hUnused1a, hUnused2a.
    erewrite <- Trans_swap_id; eauto.
  }
  rewrite <- hMachines.
  eapply HaltListScoreUpperBound_LE_swap; eauto.
Qed.

Lemma HaltListScoreUpperBound_LE_HaltAtES_MergeUnusedState :
  forall tm n qs tape (P : St -> Prop),
  HaltsAt Σ tm n (InitES Σ Σ0) ->
  Steps Σ tm n (InitES Σ Σ0) (qs, tape) ->
  n <= scoreFuel ->
  scoreOK tm = true ->
  ((exists q, P q /\ UnusedState tm q) \/
   (forall q, ~ UnusedState tm q)) ->
  (forall q, ~ UnusedState tm q -> P q) ->
  (forall tr,
    P (nxt Σ tr) ->
    HaltListScoreUpperBound
      (LE Σ (TM_upd Σ Σ_eqb tm qs (tape Z0) (Some tr)))) ->
  HaltListScoreUpperBound (LE Σ tm).
Proof.
  intros tm n qs tape P hHalt hSteps hn hOK hUnused hUsedChildren.
  intros hChildren.
  destruct hUnused as [[canonical [hCanonicalP hCanonicalUnused]]|hNoUnused].
  - eapply HaltListScoreUpperBound_LE_Halt; eauto.
    intro tr.
    destruct (UnusedState_dec tm (nxt Σ tr)) as [hTargetUnused|hTargetUsed].
    + destruct tr as [target direction write].
      cbn in hTargetUnused |- *.
      eapply HaltListScoreUpperBound_LE_HaltsAtES_UnusedState.
      * exact hHalt.
      * exact hSteps.
      * exact hCanonicalUnused.
      * exact hTargetUnused.
      * apply hChildren. exact hCanonicalP.
    + apply hChildren.
      now apply hUsedChildren.
  - eapply HaltListScoreUpperBound_LE_Halt; eauto.
Qed.

Lemma HaltListScoreUpperBound_LE_HaltAtES_UnusedState_ptr :
  forall tm n qs tape ptr,
  HaltsAt Σ tm n (InitES Σ Σ0) ->
  Steps Σ tm n (InitES Σ Σ0) (qs, tape) ->
  n <= scoreFuel ->
  scoreOK tm = true ->
  UnusedState_ptr tm ptr ->
  (forall tr,
    St_le ptr (nxt Σ tr) ->
    HaltListScoreUpperBound
      (LE Σ (TM_upd Σ Σ_eqb tm qs (tape Z0) (Some tr)))) ->
  HaltListScoreUpperBound (LE Σ tm).
Proof.
  intros tm n qs tape ptr hHalt hSteps hn hOK hPtr hChildren.
  destruct hPtr as [hSomeUnused|[hNoUnused hPtrLeast]].
  - eapply (HaltListScoreUpperBound_LE_HaltAtES_MergeUnusedState
      tm n qs tape (St_le ptr)); eauto.
    + left. exists ptr. rewrite hSomeUnused.
      split; unfold St_le; lia.
    + intros q hUsed.
      rewrite hSomeUnused in hUsed.
      unfold St_le in hUsed |- *.
      lia.
  - eapply (HaltListScoreUpperBound_LE_HaltAtES_MergeUnusedState
      tm n qs tape (St_le ptr)); eauto.
Qed.

Lemma TNF_Node_expand_score_spec : forall x n qs tape,
  HaltsAt Σ (TNF_tm x) n (InitES Σ Σ0) ->
  Steps Σ (TNF_tm x) n (InitES Σ Σ0) (qs, tape) ->
  n <= scoreFuel ->
  TNF_Node_WF x ->
  scoreOK (TNF_tm x) = true ->
  (forall x', In x' (TNF_Node_expand x qs (tape Z0)) -> TNF_Node_SB x') ->
  TNF_Node_SB x.
Proof.
  intros [tm cnt ptr] n qs tape hHalt hSteps hn hWF hOK hChildren.
  cbn in hHalt, hSteps, hOK |- *.
  destruct hWF as [hCount [hCountNonzero hPtr]].
  unfold TNF_Node_SB.
  eapply HaltListScoreUpperBound_LE_HaltAtES_UnusedState_ptr; eauto.
  intros tr hPtrTr.
  destruct (Nat.eqb_spec cnt 1) as [hCntOne|hCntNotOne].
  - apply HaltListScoreUpperBound_LE_NonHalt.
    apply CountHaltTrans_0_NonHalt.
    change (CountHaltTrans
      (TM_upd Σ Σ_eqb tm qs (tape Z0) (Some tr)) = 0).
    pose proof (HaltsAtES_Trans hHalt hSteps) as hUndefined.
    pose proof (CountHaltTrans_upd tr hUndefined) as hCountUpd.
    assert (hOne : CountHaltTrans tm = 1).
    { rewrite <- hCount. exact hCntOne. }
    rewrite hOne in hCountUpd.
    destruct (CountHaltTrans
      (TM_upd Σ Σ_eqb tm qs (tape Z0) (Some tr)));
      [reflexivity|discriminate].
  - specialize (hChildren
      (TNF_Node_upd
        {| TNF_tm := tm; TNF_cnt := cnt; TNF_ptr := ptr |}
        qs (tape Z0) tr)).
    rewrite <- TM_upd'_spec.
    apply hChildren.
    unfold TNF_Node_expand.
    assert (hEqb : Nat.eqb cnt 1 = false) by now apply Nat.eqb_neq.
    rewrite hEqb.
    rewrite in_map_iff.
    exists tr.
    split; [reflexivity|].
    rewrite filter_In.
    split.
    + apply Trans_list_spec.
    + destruct (St_leb ptr (nxt Σ tr)) eqn:hLeb; [reflexivity|].
      pose proof (St_leb_spec ptr (nxt Σ tr)) as hNotLe.
      rewrite hLeb in hNotLe.
      contradiction.
Qed.

Definition ListES_rev (e : ListES) : ListES :=
  Build_ListES (r e) (l e) (m e) (s e).

Lemma ListES_rev_rev : forall e,
  ListES_rev (ListES_rev e) = e.
Proof.
  intros [el er em es]. reflexivity.
Qed.

Lemma ListES_rev_initial :
  ListES_rev initialListES = initialListES.
Proof.
  reflexivity.
Qed.

Lemma listScore_rev : forall e,
  listScore (ListES_rev e) = listScore e.
Proof.
  intros [el er em es].
  unfold listScore, ListES_rev; cbn.
  lia.
Qed.

Lemma ListES_step'_rev : forall tr e,
  ListES_step' (Trans_rev Σ tr) (ListES_rev e) =
  ListES_rev (ListES_step' tr e).
Proof.
  intros [next direction write] [el er em es].
  destruct direction, el, er; reflexivity.
Qed.

Lemma TM_rev_at_ListES_rev : forall tm e,
  TM_rev Σ tm (s (ListES_rev e)) (m (ListES_rev e)) =
  option_Trans_rev Σ (tm (s e) (m e)).
Proof.
  intros tm [el er em es]. reflexivity.
Qed.

Lemma ListES_Steps_rev : forall tm n e,
  ListES_Steps (TM_rev Σ tm) n (ListES_rev e) =
  option_map ListES_rev (ListES_Steps tm n e).
Proof.
  intros tm n.
  induction n as [|n ih]; intros e.
  - reflexivity.
  - cbn [ListES_Steps].
    rewrite TM_rev_at_ListES_rev.
    destruct (tm (s e) (m e)) as [tr|] eqn:hStep; [|reflexivity].
    cbn [option_Trans_rev].
    rewrite ListES_step'_rev.
    apply ih.
Qed.

Lemma FirstHaltFrom_rev : forall tm start n e,
  FirstHaltFrom tm start n e ->
  FirstHaltFrom (TM_rev Σ tm) (ListES_rev start) n (ListES_rev e).
Proof.
  intros tm start n e [hRun hHalt].
  split.
  - rewrite ListES_Steps_rev, hRun.
    reflexivity.
  - rewrite TM_rev_at_ListES_rev.
    rewrite hHalt.
    reflexivity.
Qed.

Lemma HaltListScoreUpperBound_LE_rev : forall tm,
  HaltListScoreUpperBound (LE Σ tm) ->
  HaltListScoreUpperBound (LE Σ (TM_rev Σ tm)).
Proof.
  intros tm hBound.
  unfold HaltListScoreUpperBound in hBound |- *.
  intros tm' n e hLE hFirst.
  assert (hLEBack : LE Σ tm (TM_rev Σ tm')).
  { apply (proj2 (LE_rev Σ tm (TM_rev Σ tm'))).
    rewrite TM_rev_rev.
    exact hLE. }
  assert (hFirstBack : FirstHaltAt (TM_rev Σ tm') n (ListES_rev e)).
  { unfold FirstHaltAt in hFirst |- *.
    rewrite <- ListES_rev_initial.
    now apply FirstHaltFrom_rev. }
  pose proof (hBound _ _ _ hLEBack hFirstBack) as hScore.
  rewrite listScore_rev in hScore.
  exact hScore.
Qed.

(** A queue paired with the conjunction of all score guards encountered at
    halting TNF nodes.  Its first projection is exactly the ordinary CoqBB4
    search queue. *)
Definition ScoreQueue := (SearchQueue * bool)%type.

Definition ScoreQueue_WF (q : ScoreQueue) (rootNode : TNF_Node) : Prop :=
  let '((q1, q2), ok) := q in
  (forall x, In x (q1 ++ q2) -> TNF_Node_WF x) /\
  (ok = true ->
   (forall x, In x (q1 ++ q2) -> TNF_Node_SB x) ->
   TNF_Node_SB rootNode).

Definition score_upd
    (q : ScoreQueue) (f : HaltDeciderWithIdentifier) : ScoreQueue :=
  match q with
  | ((h :: t, q2), ok) =>
      let res := f (TNF_tm h) in
      match fst res with
      | Result_Halt qs i =>
          ((TNF_Node_expand h qs i ++ t, q2),
            andb ok (scoreOK (TNF_tm h)))
      | Result_NonHalt => ((t, q2), ok)
      | Result_Unknown => ((t, h :: q2), ok)
      end
  | _ => q
  end.

Lemma score_upd_spec : forall q rootNode f,
  ScoreQueue_WF q rootNode ->
  HaltDeciderWithIdentifier_WF scoreFuel f ->
  ScoreQueue_WF (score_upd q f) rootNode.
Proof.
  intros [[q1 q2] ok] rootNode f hQueue hDecider.
  destruct q1 as [|h q1]; [exact hQueue|].
  cbn [ScoreQueue_WF score_upd] in hQueue |- *.
  destruct hQueue as [hNodes hRoot].
  specialize (hDecider (TNF_tm h)).
  destruct (fst (f (TNF_tm h))) as [haltState haltSymbol| |] eqn:hResult.
  - cbn in hDecider |- *.
    split.
    + intros x hx.
      repeat rewrite in_app_iff in hx.
      rewrite or_assoc in hx.
      rewrite <- in_app_iff in hx.
      destruct hx as [hx|hx].
      * destruct hDecider as [n [tape [hHalt [hSteps [hRead hn]]]]].
        subst haltSymbol.
        eapply TNF_Node_expand_spec; eauto.
        apply hNodes. cbn. tauto.
      * apply hNodes. cbn. tauto.
    + intros hOK hBounds.
      apply Bool.andb_true_iff in hOK.
      destruct hOK as [hOldOK hNodeOK].
      apply hRoot; [exact hOldOK|].
      intros x hx.
      destruct hx as [hx|hx].
      * subst x.
        destruct hDecider as [n [tape [hHalt [hSteps [hRead hn]]]]].
        subst haltSymbol.
        eapply TNF_Node_expand_score_spec.
        -- exact hHalt.
        -- exact hSteps.
        -- exact hn.
        -- apply hNodes. cbn. tauto.
        -- exact hNodeOK.
        -- intros child hChild.
           apply hBounds.
           repeat rewrite in_app_iff.
           tauto.
      * apply hBounds.
        rewrite in_app_iff in hx.
        rewrite in_app_iff.
        destruct hx as [hx|hx].
        -- left. rewrite in_app_iff. now right.
        -- now right.
  - cbn in hDecider |- *.
    split.
    + intros x hx. apply hNodes. cbn. tauto.
    + intros hOK hBounds.
      apply hRoot; [exact hOK|].
      intros x hx.
      destruct hx as [hx|hx].
      * subst x. now apply TNF_Node_SB_NonHalt.
      * apply hBounds.
        repeat rewrite in_app_iff in hx |- *.
        tauto.
  - cbn in hDecider |- *.
    split.
    + intros x hx. apply hNodes.
      repeat rewrite in_app_iff in hx |- *.
      cbn in hx |- *.
      tauto.
    + intros hOK hBounds.
      apply hRoot; [exact hOK|].
      intros x hx. apply hBounds.
      repeat rewrite in_app_iff in hx |- *.
      cbn in hx |- *.
      tauto.
Qed.

Fixpoint score_upds
    (q : ScoreQueue) (f : HaltDeciderWithIdentifier) (n : nat) : ScoreQueue :=
  match fst (fst q) with
  | [] => q
  | _ :: _ =>
      match n with
      | O => score_upd q f
      | S n' => score_upds (score_upds q f n') f n'
      end
  end.

Lemma score_upds_spec : forall q rootNode f n,
  ScoreQueue_WF q rootNode ->
  HaltDeciderWithIdentifier_WF scoreFuel f ->
  ScoreQueue_WF (score_upds q f n) rootNode.
Proof.
  intros q rootNode f n hQueue hDecider.
  revert q hQueue.
  induction n as [|n ih]; intros q hQueue; cbn.
  - destruct (fst (fst q)) as [|h t]; [exact hQueue|].
    now apply score_upd_spec.
  - destruct (fst (fst q)) as [|h t]; [exact hQueue|].
    apply ih. apply ih. exact hQueue.
Qed.

Definition score_init (x : TNF_Node) : ScoreQueue :=
  (([x], []), true).

Lemma score_init_spec : forall x,
  TNF_Node_WF x -> ScoreQueue_WF (score_init x) x.
Proof.
  intros x hWF.
  unfold score_init, ScoreQueue_WF; cbn.
  split.
  - intros y [hy|[]]. now subst y.
  - intros _ hBound. apply hBound. tauto.
Qed.

Definition root_score_q : ScoreQueue := score_init root.

Definition root_score_q_upd1 : ScoreQueue :=
  score_upd root_score_q (MakeHaltDeciderWithIdentifier decider2).

Definition root_score_q_upd1_simplified : ScoreQueue :=
  ((filter first_trans_is_R (fst (fst root_score_q_upd1)), []),
    snd root_score_q_upd1).

Lemma root_score_q_WF : ScoreQueue_WF root_score_q root.
Proof.
  apply score_init_spec, root_WF.
Qed.

Lemma root_score_q_upd1_WF : ScoreQueue_WF root_score_q_upd1 root.
Proof.
  apply score_upd_spec.
  - apply root_score_q_WF.
  - unfold scoreFuel. apply decider2_WF.
Qed.

Lemma root_left_score_of_right : forall target write,
  TNF_Node_SB
    (TNF_Node_upd root St0 Σ0
      {| nxt := target; dir := Dpos; out := write |}) ->
  TNF_Node_SB
    (TNF_Node_upd root St0 Σ0
      {| nxt := target; dir := Dneg; out := write |}).
Proof.
  intros target write hRight.
  unfold TNF_Node_SB in hRight |- *.
  change (HaltListScoreUpperBound
    (LE Σ (TM_upd' TM0 St0 Σ0
      (Some {| nxt := target; dir := Dpos; out := write |})))) in hRight.
  change (HaltListScoreUpperBound
    (LE Σ (TM_upd' TM0 St0 Σ0
      (Some {| nxt := target; dir := Dneg; out := write |})))).
  rewrite TM_rev_upd'_TM0.
  now apply HaltListScoreUpperBound_LE_rev.
Qed.

Lemma root_score_q_upd1_simplified_WF :
  ScoreQueue_WF root_score_q_upd1_simplified root.
Proof.
  pose proof root_score_q_upd1_WF as hWF.
  unfold root_score_q_upd1, root_score_q, score_init,
    ScoreQueue_WF, score_upd in hWF.
  cbn in hWF.
  destruct hWF as [hNodes hRoot].
  unfold root_score_q_upd1_simplified, root_score_q_upd1,
    root_score_q, score_init, ScoreQueue_WF, score_upd.
  cbn.
  split.
  - intros x hx. apply hNodes. tauto.
  - intros _ hKept.
    apply hRoot; [reflexivity|].
    intros x hx.
    destruct hx as
      [hx|[hx|[hx|[hx|[hx|[hx|[hx|[hx|[]]]]]]]]].
    + subst x. apply root_left_score_of_right.
      apply hKept. cbn. tauto.
    + subst x. apply root_left_score_of_right.
      apply hKept. cbn. tauto.
    + apply hKept. subst x. cbn. tauto.
    + apply hKept. subst x. cbn. tauto.
    + subst x. apply root_left_score_of_right.
      apply hKept. cbn. tauto.
    + subst x. apply root_left_score_of_right.
      apply hKept. cbn. tauto.
    + apply hKept. subst x. cbn. tauto.
    + apply hKept. subst x. cbn. tauto.
Qed.

End BusyBeaverBB4Score.
