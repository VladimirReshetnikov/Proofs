From Stdlib Require Import ZArith Lia List.
From Stdlib Require Import Logic.FunctionalExtensionality.

From SetTheory Require Import BusyBeaver BusyBeaverKnownValues.

From CoqBB2 Require Import BB2_Statement BB2_Encodings TM BB2_Theorem.

Module BB := BusyBeaver.
Module BBKV := BusyBeaverKnownValues.

Module BusyBeaverBB2Bridge.

Open Scope Z_scope.

Definition stOfNat (q : nat) : St :=
  match q with
  | O => St0
  | _ => St1
  end.

Definition natOfSt (s : St) : nat :=
  match s with
  | St0 => O
  | St1 => S O
  end.

Lemma natOfSt_stOfNat_lt_two : forall q,
  (q < 2)%nat -> natOfSt (stOfNat q) = q.
Proof.
  destruct q as [|[|q]]; cbn; intros; try reflexivity; lia.
Qed.

Definition sigmaOfBool (b : bool) : Σ :=
  if b then Σ1 else Σ0.

Definition boolOfSigma (s : Σ) : bool :=
  match s with
  | Σ0 => false
  | Σ1 => true
  end.

Definition dirOfMove (m : BB.move) : Dir :=
  match m with
  | BB.left => Dneg
  | BB.right => Dpos
  end.

Definition transOfAction (a : BB.action) : option (Trans Σ) :=
  match BB.action_next a with
  | Some q =>
      Some {| nxt := stOfNat q;
              dir := dirOfMove (BB.action_move a);
              out := sigmaOfBool (BB.action_write a) |}
  | None => None
  end.

Definition tmOfMachine (M : BB.machine 2) : TM Σ :=
  fun s i => transOfAction (BB.transition 2 M (natOfSt s) (boolOfSigma i)).

Definition tapeOfConfig {states : nat} (cfg : BB.config states) : Z -> Σ :=
  fun rel => sigmaOfBool (BB.Tape.read (BB.cfg_tape _ cfg) (BB.cfg_head _ cfg + rel)).

Definition esOfConfig {states : nat} (cfg : BB.config states) (q : nat) : ExecState Σ :=
  (stOfNat q, tapeOfConfig cfg).

Lemma boolOfSigma_sigmaOfBool : forall b,
  boolOfSigma (sigmaOfBool b) = b.
Proof.
  destruct b; reflexivity.
Qed.

Lemma dirOfMove_to_Z : forall mv,
  Dir_to_Z (dirOfMove mv) =
    match mv with BB.left => -1 | BB.right => 1 end.
Proof.
  destruct mv; reflexivity.
Qed.

Lemma tapeOfConfig_zero : forall states (cfg : BB.config states),
  tapeOfConfig cfg 0 = sigmaOfBool (BB.Tape.read (BB.cfg_tape _ cfg) (BB.cfg_head _ cfg)).
Proof.
  intros. unfold tapeOfConfig. rewrite Z.add_0_r. reflexivity.
Qed.

Lemma tapeOfConfig_step :
  forall (M : BB.machine 2) (cfg : BB.config 2) q q',
    BB.cfg_state _ cfg = Some q ->
    BB.action_next
      (BB.transition 2 M q (BB.Tape.read (BB.cfg_tape _ cfg) (BB.cfg_head _ cfg))) =
      Some q' ->
    mov Σ
      (upd Σ (tapeOfConfig cfg)
        (sigmaOfBool
          (BB.action_write
            (BB.transition 2 M q (BB.Tape.read (BB.cfg_tape _ cfg) (BB.cfg_head _ cfg))))))
      (dirOfMove
        (BB.action_move
          (BB.transition 2 M q (BB.Tape.read (BB.cfg_tape _ cfg) (BB.cfg_head _ cfg))))) =
    tapeOfConfig (BB.Machine.step M cfg).
Proof.
  intros M cfg q q' hState hNext.
  unfold tapeOfConfig.
  apply functional_extensionality; intro rel.
  unfold mov, upd.
  rewrite dirOfMove_to_Z.
  unfold BB.Machine.step.
  rewrite hState.
  set (bit := BB.Tape.read (BB.cfg_tape 2 cfg) (BB.cfg_head 2 cfg)).
  change (BB.Tape.read (BB.cfg_tape 2 cfg) (BB.cfg_head 2 cfg)) with bit in hNext |- *.
  rewrite hNext.
  set (a := BB.transition 2 M q bit) in *.
  destruct (BB.action_move a) eqn:hMove; cbn [dirOfMove Dir_to_Z BB.move_apply].
  all: cbn [BB.cfg_head BB.cfg_tape].
  - destruct (Z.eqb (rel + -1) 0) eqn:hEq.
    + apply Z.eqb_eq in hEq.
      replace (BB.cfg_head 2 cfg - 1 + rel)%Z with
        (BB.cfg_head 2 cfg) by (unfold BB.move_apply; lia).
      rewrite BB.Tape.read_write_same.
      reflexivity.
    + apply Z.eqb_neq in hEq.
      rewrite BB.Tape.read_write_of_ne.
      * replace (BB.cfg_head 2 cfg + (rel + -1))%Z with
          (BB.cfg_head 2 cfg - 1 + rel)%Z by lia.
        reflexivity.
      * lia.
  - destruct (Z.eqb (rel + 1) 0) eqn:hEq.
    + apply Z.eqb_eq in hEq.
      replace (BB.cfg_head 2 cfg + 1 + rel)%Z with
        (BB.cfg_head 2 cfg) by (unfold BB.move_apply; lia).
      rewrite BB.Tape.read_write_same.
      reflexivity.
    + apply Z.eqb_neq in hEq.
      rewrite BB.Tape.read_write_of_ne.
      * replace (BB.cfg_head 2 cfg + (rel + 1))%Z with
          (BB.cfg_head 2 cfg + 1 + rel)%Z by lia.
        reflexivity.
      * lia.
Qed.

Lemma step_some_bridge :
  forall (M : BB.machine 2) (cfg : BB.config 2) q q',
    (q < 2)%nat ->
    BB.cfg_state _ cfg = Some q ->
    BB.action_next
      (BB.transition 2 M q (BB.Tape.read (BB.cfg_tape _ cfg) (BB.cfg_head _ cfg))) =
      Some q' ->
    step Σ (tmOfMachine M) (esOfConfig cfg q) =
      Some (esOfConfig (BB.Machine.step M cfg) q').
Proof.
  intros M cfg q q' hqLt hState hNext.
  unfold step, esOfConfig, tmOfMachine, transOfAction.
  rewrite tapeOfConfig_zero.
  rewrite boolOfSigma_sigmaOfBool.
  rewrite (natOfSt_stOfNat_lt_two q hqLt).
  rewrite hNext.
  f_equal.
  f_equal.
  eapply tapeOfConfig_step; eassumption.
Qed.

Lemma run_some_steps_bridge :
  forall (M : BB.machine 2) n q,
    BB.cfg_state _ (BB.Machine.run M n) = Some q ->
    Steps Σ (tmOfMachine M) n (InitES Σ Σ0)
      (esOfConfig (BB.Machine.run M n) q).
Proof.
  intros M n.
  induction n as [|n ih]; intros q hState.
  - cbn in hState. inversion hState; subst q.
    unfold InitES, esOfConfig, tapeOfConfig, BB.initial, BB.start_state.
    cbn.
    replace (fun rel : Z => sigmaOfBool (BB.Tape.read nil (0 + rel))) with
      (fun _ : Z => Σ0).
    + constructor.
    + apply functional_extensionality; intro rel.
      unfold BB.Tape.read. cbn. reflexivity.
  - cbn in hState.
    set (prev := BB.Machine.run M n) in *.
    destruct (BB.cfg_state 2 prev) as [old|] eqn:hOld.
    + unfold BB.Machine.step in hState.
      rewrite hOld in hState.
      set (bit := BB.Tape.read (BB.cfg_tape 2 prev) (BB.cfg_head 2 prev)) in *.
      destruct (BB.action_next (BB.transition 2 M old bit)) as [next|] eqn:hNext.
      * inversion hState; subst q.
        econstructor.
        -- apply ih. reflexivity.
        -- apply step_some_bridge.
           ++ exact (BBKV.run_state_lt 2 M n old hOld).
           ++ exact hOld.
           ++ exact hNext.
      * discriminate hState.
    + rewrite (BB.Machine.step_of_halted 2 M prev hOld) in hState.
      rewrite hOld in hState. discriminate hState.
Qed.

Lemma step_none_bridge :
  forall (M : BB.machine 2) (cfg : BB.config 2) q,
    (q < 2)%nat ->
    BB.cfg_state _ cfg = Some q ->
    BB.action_next
      (BB.transition 2 M q (BB.Tape.read (BB.cfg_tape _ cfg) (BB.cfg_head _ cfg))) =
      None ->
    step Σ (tmOfMachine M) (esOfConfig cfg q) = None.
Proof.
  intros M cfg q hqLt hState hNext.
  unfold step, esOfConfig, tmOfMachine, transOfAction.
  rewrite tapeOfConfig_zero.
  rewrite boolOfSigma_sigmaOfBool.
  rewrite (natOfSt_stOfNat_lt_two q hqLt).
  rewrite hNext.
  reflexivity.
Qed.

Lemma local_halt_event_to_coqbb2 :
  forall (M : BB.machine 2) n q,
    BB.cfg_state _ (BB.Machine.run M n) = Some q ->
    BB.cfg_state _ (BB.Machine.run M (S n)) = None ->
    HaltsAt Σ (tmOfMachine M) n (InitES Σ Σ0).
Proof.
  intros M n q hSome hNextNone.
  unfold HaltsAt.
  exists (esOfConfig (BB.Machine.run M n) q).
  split.
  - apply run_some_steps_bridge. exact hSome.
  - cbn in hNextNone.
    unfold BB.Machine.step in hNextNone.
    rewrite hSome in hNextNone.
    set (bit := BB.Tape.read (BB.cfg_tape 2 (BB.Machine.run M n))
      (BB.cfg_head 2 (BB.Machine.run M n))) in *.
    destruct (BB.action_next (BB.transition 2 M q bit)) as [next|] eqn:hActionNext.
    + discriminate hNextNone.
    + apply step_none_bridge.
      * exact (BBKV.run_state_lt 2 M n q hSome).
      * exact hSome.
      * exact hActionNext.
Qed.

Lemma local_halt_event_time_le_six :
  forall (M : BB.machine 2) n q,
    BB.cfg_state _ (BB.Machine.run M n) = Some q ->
    BB.cfg_state _ (BB.Machine.run M (S n)) = None ->
    (S n <= 6)%nat.
Proof.
  intros M n q hSome hNone.
  pose proof (local_halt_event_to_coqbb2 M n q hSome hNone) as hHalt.
  pose proof (BB2_upperbound (tmOfMachine M) n hHalt) as hBound.
  unfold BB2_minus_one in hBound. lia.
Qed.

Lemma local_halted_has_early_event :
  forall (M : BB.machine 2) t,
    BB.cfg_state _ (BB.Machine.run M t) = None ->
    exists n q,
      (n < t)%nat /\
      BB.cfg_state _ (BB.Machine.run M n) = Some q /\
      BB.cfg_state _ (BB.Machine.run M (S n)) = None.
Proof.
  intros M t.
  induction t as [|t ih]; intro hNone.
  - cbn in hNone. discriminate hNone.
  - destruct (BB.cfg_state 2 (BB.Machine.run M t)) as [q|] eqn:hPrev.
    + exists t, q. repeat split; try lia; assumption.
    + destruct (ih eq_refl) as [n [q [hlt [hSome hEvent]]]].
      exists n, q. repeat split; try lia; assumption.
Qed.

Lemma run_add_of_halted :
  forall (states : nat) (M : BB.machine states) h k,
    BB.cfg_state _ (BB.Machine.run M h) = None ->
    BB.Machine.run M (h + k) = BB.Machine.run M h.
Proof.
  intros states M h k hHalt.
  induction k as [|k ih].
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite Nat.add_succ_r.
    cbn.
    rewrite ih.
    apply BB.Machine.step_of_halted.
    exact hHalt.
Qed.

Lemma local_run_eq_early_halt_event :
  forall (M : BB.machine 2) t n q,
    (n < t)%nat ->
    BB.cfg_state _ (BB.Machine.run M n) = Some q ->
    BB.cfg_state _ (BB.Machine.run M (S n)) = None ->
    BB.Machine.run M t = BB.Machine.run M (S n).
Proof.
  intros M t n q hlt _ hEvent.
  replace t with (S n + (t - S n))%nat by lia.
  apply run_add_of_halted.
  exact hEvent.
Qed.

Theorem two_state_halting_time_bound_event :
  forall (M : BB.machine 2) t,
    BB.cfg_state _ (BB.Machine.run M t) = None ->
    exists h,
      (h <= 6)%nat /\
      BB.cfg_state _ (BB.Machine.run M h) = None /\
      BB.Machine.run M t = BB.Machine.run M h.
Proof.
  intros M t hNone.
  destruct (local_halted_has_early_event M t hNone) as
    [n [q [hlt [hSome hEvent]]]].
  exists (S n).
  repeat split.
  - exact (local_halt_event_time_le_six M n q hSome hEvent).
  - exact hEvent.
  - apply local_run_eq_early_halt_event with (q := q); assumption.
Qed.

Theorem upperBound_two : forall score,
  BB.AttainableScore 2 score -> (score <= 4)%nat.
Proof.
  intros score [M [t [hState hScore]]].
  destruct (two_state_halting_time_bound_event M t hState) as
    [h [hLe [hHalt hRun]]].
  rewrite hRun in hScore.
  pose proof (BBKV.two_state_halted_score_le_four_by_time M h hLe hHalt) as hScoreLe.
  lia.
Qed.

Theorem exactScore_two : BBKV.ExactScore 2 4.
Proof.
  split.
  - exact BBKV.attainableScore_two_four.
  - exact upperBound_two.
Qed.

Theorem sigma_two_eq_four : forall Sigma,
  BB.IsSigma Sigma -> Sigma 2%nat = 4%nat.
Proof.
  intros Sigma hSigma.
  apply BBKV.ExactScore.sigma_eq.
  - exact hSigma.
  - lia.
  - exact exactScore_two.
Qed.

End BusyBeaverBB2Bridge.
