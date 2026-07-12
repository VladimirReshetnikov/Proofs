(* ===================================================================== *)
(*  Transport the score-aware CoqBB4 TNF certificate to the repository's *)
(*  local Rado machine model.                                             *)
(*                                                                       *)
(*  [BusyBeaverBB4Score] bounds the finite [ListES] tape immediately      *)
(*  before CoqBB4 encounters an undefined transition.  Here a synchronized *)
(*  invariant relates that execution to [BusyBeaver.Machine.run], proving *)
(*  that the finite score is exactly the length of the local marked-cell   *)
(*  list.  The local model then executes one final write/move action; its  *)
(*  score can increase by at most one.                                    *)
(* ===================================================================== *)

From Stdlib Require Import List Lia ZArith Bool.
Import ListNotations.

From CoqBB4 Require Import BB4_Statement BB4_Encodings List_Tape TM.
From SetTheory Require Import
  BusyBeaver BusyBeaverKnownValues BusyBeaverBB4Bridge BusyBeaverBB4Score
  BusyBeaverBB4ScoreCertificate.

Module BusyBeaverBB4ScoreBridge.

Module BB := BusyBeaver.
Module BBKV := BusyBeaverKnownValues.
Module B4 := BusyBeaverBB4Bridge.
Module S := BusyBeaverBB4Score.
Module C := BusyBeaverBB4ScoreCertificate.

Definition bitScore (b : bool) : nat := if b then 1 else 0.

Lemma sigmaScore_sigmaOfBool : forall b,
  S.sigmaScore (B4.sigmaOfBool b) = bitScore b.
Proof.
  destruct b; reflexivity.
Qed.

Lemma listScore_step'_balance : forall tr e,
  S.listScore (ListES_step' tr e) + S.sigmaScore (m e) =
  S.listScore e + S.sigmaScore (out Σ tr).
Proof.
  intros [next direction write] [el er em es].
  destruct direction, el, er, em, write;
    cbv [ListES_step' BusyBeaverBB4Score.listScore
      BusyBeaverBB4Score.listScore0 BusyBeaverBB4Score.sigmaScore
      l r m s out]; lia.
Qed.

Lemma filter_ne_length_balance : forall t pos,
  NoDup t ->
  length (filter (fun q => negb (Z.eqb q pos)) t) +
    (if in_dec Z.eq_dec pos t then 1 else 0) = length t.
Proof.
  intros t pos hNoDup.
  induction hNoDup as [|x xs hNotIn hNoDup ih].
  - cbn. destruct (in_dec Z.eq_dec pos []); [contradiction|reflexivity].
  - change
      (length
        (if negb (Z.eqb x pos)
         then x :: filter (fun q => negb (Z.eqb q pos)) xs
         else filter (fun q => negb (Z.eqb q pos)) xs) +
       (if in_dec Z.eq_dec pos (x :: xs) then 1 else 0) =
       S (length xs)).
    destruct (Z.eqb x pos) eqn:hxp.
    + cbn [negb].
      apply Z.eqb_eq in hxp. subst x.
      rewrite (BB.Tape.filter_absent_eq xs pos hNotIn).
      destruct (in_dec Z.eq_dec pos (pos :: xs)); [lia|].
      exfalso. apply n. now left.
    + cbn [negb].
      apply Z.eqb_neq in hxp.
      change
        (S (length (filter (fun q => negb (Z.eqb q pos)) xs)) +
         (if in_dec Z.eq_dec pos (x :: xs) then 1 else 0) =
         S (length xs)).
      destruct (in_dec Z.eq_dec pos xs) as [hIn|hNot].
      * destruct (in_dec Z.eq_dec pos (x :: xs)) as [_|hBad].
        -- lia.
        -- exfalso. apply hBad. now right.
      * destruct (in_dec Z.eq_dec pos (x :: xs)) as [hBad|_].
        -- destruct hBad as [hEq|hIn]; [congruence|contradiction].
        -- lia.
Qed.

Lemma Tape_write_length_balance : forall t pos write,
  NoDup t ->
  length (BB.Tape.write t pos write) + bitScore (BB.Tape.read t pos) =
  length t + bitScore write.
Proof.
  intros t pos write hNoDup.
  destruct write.
  - unfold BB.Tape.write, BB.Tape.read, bitScore.
    destruct (in_dec Z.eq_dec pos t); cbn; lia.
  - unfold BB.Tape.write, BB.Tape.read, bitScore.
    pose proof (filter_ne_length_balance t pos hNoDup) as hFilter.
    destruct (in_dec Z.eq_dec pos t); cbn in hFilter |- *; lia.
Qed.

Lemma ListES_local_step_score : forall e t head tr write,
  NoDup t ->
  m e = B4.sigmaOfBool (BB.Tape.read t head) ->
  out Σ tr = B4.sigmaOfBool write ->
  S.listScore e = length t ->
  S.listScore (ListES_step' tr e) =
    length (BB.Tape.write t head write).
Proof.
  intros e t head tr write hNoDup hRead hWrite hScore.
  pose proof (listScore_step'_balance tr e) as hList.
  pose proof (Tape_write_length_balance t head write hNoDup) as hTape.
  rewrite hRead, hWrite in hList.
  repeat rewrite sigmaScore_sigmaOfBool in hList.
  rewrite hScore in hList.
  lia.
Qed.

Lemma run_tape_NoDup : forall states (M : BB.machine states) n,
  NoDup (BB.cfg_tape _ (BB.Machine.run M n)).
Proof.
  intros states M n.
  induction n as [|n ih].
  - constructor.
  - cbn.
    unfold BB.Machine.step.
    destruct (BB.cfg_state states (BB.Machine.run M n)) as [q|] eqn:hState;
      [|exact ih].
    cbn.
    apply BB.Tape.write_nodup.
    exact ih.
Qed.

Lemma runFrom_succ_start_four : forall (M : BB.machine 4) cfg n,
  BB.Machine.runFrom M cfg (S n) =
  BB.Machine.runFrom M (BB.Machine.step M cfg) n.
Proof.
  intros M cfg n.
  replace (S n) with (1 + n) by lia.
  rewrite BB.Machine.runFrom_add.
  reflexivity.
Qed.

Definition Sync (_M : BB.machine 4) (e : ListES) (cfg : BB.config 4) : Prop :=
  exists q,
    q < 4 /\
    BB.cfg_state _ cfg = Some q /\
    ListES_toES e = B4.esOfConfig cfg q /\
    S.listScore e = length (BB.cfg_tape _ cfg) /\
    NoDup (BB.cfg_tape _ cfg).

Lemma Sync_initial : forall M,
  Sync M S.initialListES (BB.initial 4).
Proof.
  intro M.
  exists 0%nat.
  split; [lia|].
  split; [reflexivity|].
  split.
  - rewrite S.initialListES_toES.
    unfold B4.esOfConfig, B4.tapeOfConfig, BB.initial, BB.start_state, InitES.
    cbn.
    f_equal.
  - split.
    + reflexivity.
    + constructor.
Qed.

Lemma Sync_step : forall M e cfg tr,
  Sync M e cfg ->
  B4.tmOfMachine M (s e) (m e) = Some tr ->
  Sync M (ListES_step' tr e) (BB.Machine.step M cfg).
Proof.
  intros M [el er em es] cfg tr hSync hTrans.
  destruct hSync as [q [hq [hCfg [hES [hScore hNoDup]]]]].
  assert (hState : es = B4.stOfNat q).
  { pose proof (f_equal (fun st : ExecState Σ => fst st) hES) as h.
    exact h. }
  assert (hRead :
      em = B4.sigmaOfBool
        (BB.Tape.read (BB.cfg_tape _ cfg) (BB.cfg_head _ cfg))).
  { pose proof (f_equal (fun st : ExecState Σ => snd st Z0) hES) as h.
    change (em = B4.tapeOfConfig cfg Z0) in h.
    rewrite B4.tapeOfConfig_zero in h.
    exact h. }
  pose proof hTrans as hLookup.
  cbv [s m] in hLookup.
  cbv [s m] in hTrans.
  unfold B4.tmOfMachine in hTrans.
  rewrite hState in hTrans.
  rewrite (B4.natOfSt_stOfNat_lt_four q hq) in hTrans.
  rewrite hRead, B4.boolOfSigma_sigmaOfBool in hTrans.
  unfold B4.transOfAction in hTrans.
  destruct (BB.transition 4 M q
      (BB.Tape.read (BB.cfg_tape _ cfg) (BB.cfg_head _ cfg)))
    as [write move [q'|]] eqn:hAction; cbn in hTrans; [|discriminate].
  inversion hTrans; subst tr.
  assert (hNext :
      BB.action_next
        (BB.transition 4 M q
          (BB.Tape.read (BB.cfg_tape _ cfg) (BB.cfg_head _ cfg))) = Some q').
  { rewrite hAction. reflexivity. }
  assert (hq' : q' < 4).
  { eapply BB.transition_next_lt. exact hNext. }
  exists q'.
  split; [exact hq'|].
  split.
  - unfold BB.Machine.step. rewrite hCfg, hAction. reflexivity.
  - split.
    + pose proof (ListES_step'_spec (B4.tmOfMachine M) el er em es)
        as hListStep.
      rewrite hLookup in hListStep.
      pose proof (B4.step_some_bridge M cfg q q' hq hCfg hNext)
        as hLocalStep.
      rewrite hES in hListStep.
      rewrite hLocalStep in hListStep.
      inversion hListStep.
      symmetry. exact H0.
    + split.
      * replace (BB.cfg_tape 4 (BB.Machine.step M cfg)) with
          (BB.Tape.write (BB.cfg_tape 4 cfg) (BB.cfg_head 4 cfg) write).
        2: { unfold BB.Machine.step. rewrite hCfg, hAction. reflexivity. }
        eapply ListES_local_step_score.
        -- exact hNoDup.
        -- exact hRead.
        -- reflexivity.
        -- exact hScore.
      * unfold BB.Machine.step. rewrite hCfg, hAction. cbn.
        apply BB.Tape.write_nodup. exact hNoDup.
Qed.

Lemma ListES_Steps_sync : forall M n start e cfg,
  Sync M start cfg ->
  ListES_Steps (B4.tmOfMachine M) n start = Some e ->
  Sync M e (BB.Machine.runFrom M cfg n).
Proof.
  intros M n.
  induction n as [|n ih]; intros start e cfg hSync hRun.
  - cbn in hRun. inversion hRun; subst e. exact hSync.
  - rewrite runFrom_succ_start_four.
    cbn [ListES_Steps] in hRun.
    destruct (B4.tmOfMachine M (s start) (m start)) as [tr|]
      eqn:hTrans; [|discriminate].
    eapply ih.
    + eapply Sync_step; eassumption.
    + exact hRun.
Qed.

Lemma run_eq_runFrom_initial_four : forall (M : BB.machine 4) n,
  BB.Machine.run M n = BB.Machine.runFrom M (BB.initial 4) n.
Proof.
  intros M n.
  induction n as [|n ih]; [reflexivity|].
  cbn. now rewrite ih.
Qed.

Lemma ListES_Steps_local_score : forall M n e,
  ListES_Steps (B4.tmOfMachine M) n S.initialListES = Some e ->
  S.listScore e = length (BB.cfg_tape 4 (BB.Machine.run M n)).
Proof.
  intros M n e hRun.
  pose proof (ListES_Steps_sync M n S.initialListES e (BB.initial 4)
    (Sync_initial M) hRun) as hSync.
  rewrite <- run_eq_runFrom_initial_four in hSync.
  destruct hSync as [q [hq [hState [hES [hScore hNoDup]]]]].
  exact hScore.
Qed.

Lemma local_halt_event_FirstHaltAt : forall M n q,
  BB.cfg_state 4 (BB.Machine.run M n) = Some q ->
  BB.cfg_state 4 (BB.Machine.run M (S n)) = None ->
  exists e, S.FirstHaltAt (B4.tmOfMachine M) n e.
Proof.
  intros M n q hSome hNone.
  pose proof (B4.local_halt_event_to_coqbb4 M n q hSome hNone) as hHalt.
  assert (hn : n <= S.scoreFuel).
  { pose proof
      (B4.local_halt_event_time_le_one_hundred_seven M n q hSome hNone)
      as hTime.
    unfold S.scoreFuel, BB4_minus_one.
    cbn. lia. }
  assert (hHaltFromList :
      HaltsAt Σ (B4.tmOfMachine M) n (ListES_toES S.initialListES)).
  { rewrite S.initialListES_toES. exact hHalt. }
  destruct (S.haltWithin_complete_of_halt S.scoreFuel (B4.tmOfMachine M)
      S.initialListES n hHaltFromList hn) as [e hWithin].
  destruct (S.haltWithin_some_FirstHaltFrom S.scoreFuel (B4.tmOfMachine M)
      S.initialListES e hWithin) as [n' [hn' hFirst]].
  assert (hHalt' : HaltsAt Σ (B4.tmOfMachine M) n' (InitES Σ Σ0)).
  { rewrite <- S.initialListES_toES.
    now apply S.FirstHaltFrom_HaltsAt with (e := e). }
  pose proof (HaltsAt_unique Σ hHalt hHalt') as hEq.
  subst n'.
  now exists e.
Qed.

Lemma local_halt_event_pre_score : forall M n q,
  BB.cfg_state 4 (BB.Machine.run M n) = Some q ->
  BB.cfg_state 4 (BB.Machine.run M (S n)) = None ->
  exists e,
    S.FirstHaltAt (B4.tmOfMachine M) n e /\
    S.listScore e = length (BB.cfg_tape 4 (BB.Machine.run M n)).
Proof.
  intros M n q hSome hNone.
  destruct (local_halt_event_FirstHaltAt M n q hSome hNone) as [e hFirst].
  exists e. split; [exact hFirst|].
  now apply ListES_Steps_local_score, hFirst.
Qed.

Lemma Tape_write_length_le_succ : forall t pos write,
  NoDup t -> length (BB.Tape.write t pos write) <= S (length t).
Proof.
  intros t pos write hNoDup.
  pose proof (Tape_write_length_balance t pos write hNoDup) as hBalance.
  destruct write; destruct (BB.Tape.read t pos) eqn:hRead;
    cbn [bitScore] in hBalance; lia.
Qed.

Lemma local_halt_event_score_le_thirteen :
  (forall tm n e, S.FirstHaltAt tm n e -> S.listScore e <= 12) ->
  forall M n q,
  BB.cfg_state 4 (BB.Machine.run M n) = Some q ->
  BB.cfg_state 4 (BB.Machine.run M (S n)) = None ->
  length (BB.cfg_tape 4 (BB.Machine.run M (S n))) <= 13.
Proof.
  intros hAll M n q hSome hNone.
  destruct (local_halt_event_pre_score M n q hSome hNone) as
    [e [hFirst hScore]].
  pose proof (hAll (B4.tmOfMachine M) n e hFirst) as hPreBound.
  rewrite hScore in hPreBound.
  cbn.
  unfold BB.Machine.step.
  rewrite hSome.
  destruct (BB.transition 4 M q
      (BB.Tape.read (BB.cfg_tape 4 (BB.Machine.run M n))
        (BB.cfg_head 4 (BB.Machine.run M n))))
    as [write move next] eqn:hAction.
  cbn.
  pose proof (Tape_write_length_le_succ
    (BB.cfg_tape 4 (BB.Machine.run M n))
    (BB.cfg_head 4 (BB.Machine.run M n)) write
    (run_tape_NoDup 4 M n)) as hWrite.
  lia.
Qed.

Lemma upperBound_four_from_allTM :
  (forall tm n e, S.FirstHaltAt tm n e -> S.listScore e <= 12) ->
  forall score, BB.AttainableScore 4 score -> score <= 13.
Proof.
  intros hAll score [M [t [hHalted hScore]]].
  destruct (B4.local_halted_has_early_event M t hHalted) as
    [n [q [hn [hSome hEvent]]]].
  pose proof (local_halt_event_score_le_thirteen hAll M n q hSome hEvent)
    as hBound.
  pose proof (B4.local_run_eq_early_halt_event M t n q hn hSome hEvent)
    as hRun.
  rewrite hRun in hScore.
  rewrite hScore in hBound.
  exact hBound.
Qed.

Theorem upperBound_four : forall score,
  BB.AttainableScore 4 score -> score <= 13.
Proof.
  exact (upperBound_four_from_allTM C.allTM_first_halt_list_score_le_twelve).
Qed.

Theorem exactScore_four : BBKV.ExactScore 4 13.
Proof. exact (conj BBKV.attainableScore_four_thirteen upperBound_four). Qed.

Theorem sigma_four_eq_thirteen : forall Sigma,
  BB.IsSigma Sigma -> Sigma 4 = 13.
Proof.
  intros Sigma hSigma.
  exact (BBKV.ExactScore.sigma_eq Sigma hSigma 4 13
    (Nat.lt_0_succ 3) exactScore_four).
Qed.

End BusyBeaverBB4ScoreBridge.
