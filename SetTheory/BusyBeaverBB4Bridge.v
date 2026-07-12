(* ===================================================================== *)
(*  Bridge from the local Rado machine model to the vendored CoqBB4       *)
(*  proof of BB(4)=107.                                                    *)
(*                                                                       *)
(*  CoqBB4 represents halting as an undefined transition.  The local     *)
(*  model instead executes a final write/move action whose next state is  *)
(*  [None].  Thus CoqBB4's 106 successful transitions followed by an     *)
(*  undefined transition correspond exactly to a 107-step local halt.    *)
(*                                                                       *)
(*  This file proves only the four-state *time* value.  It deliberately   *)
(*  makes no four-state marked-symbol score upper-bound claim.            *)
(* ===================================================================== *)

From Stdlib Require Import ZArith Lia List.
From Stdlib Require Import Logic.FunctionalExtensionality.

From SetTheory Require Import BusyBeaver BusyBeaverKnownValues.

From CoqBB4 Require Import BB4_Statement BB4_Encodings TM BB4_Theorem.

Module BB := BusyBeaver.
Module BBKV := BusyBeaverKnownValues.

Module BusyBeaverBB4Bridge.

Open Scope Z_scope.

Definition stOfNat (q : nat) : St :=
  match q with
  | O => St0
  | S O => St1
  | S (S O) => St2
  | _ => St3
  end.

Definition natOfSt (s : St) : nat :=
  match s with
  | St0 => O
  | St1 => S O
  | St2 => S (S O)
  | St3 => S (S (S O))
  end.

Lemma natOfSt_stOfNat_lt_four : forall q,
  (q < 4)%nat -> natOfSt (stOfNat q) = q.
Proof.
  destruct q as [|[|[|[|q]]]]; cbn; intros; try reflexivity; lia.
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

Definition tmOfMachine (M : BB.machine 4) : TM Σ :=
  fun s i => transOfAction (BB.transition 4 M (natOfSt s) (boolOfSigma i)).

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
  forall (M : BB.machine 4) (cfg : BB.config 4) q q',
    BB.cfg_state _ cfg = Some q ->
    BB.action_next
      (BB.transition 4 M q (BB.Tape.read (BB.cfg_tape _ cfg) (BB.cfg_head _ cfg))) =
      Some q' ->
    mov Σ
      (upd Σ (tapeOfConfig cfg)
        (sigmaOfBool
          (BB.action_write
            (BB.transition 4 M q (BB.Tape.read (BB.cfg_tape _ cfg) (BB.cfg_head _ cfg))))))
      (dirOfMove
        (BB.action_move
          (BB.transition 4 M q (BB.Tape.read (BB.cfg_tape _ cfg) (BB.cfg_head _ cfg))))) =
    tapeOfConfig (BB.Machine.step M cfg).
Proof.
  intros M cfg q q' hState hNext.
  unfold tapeOfConfig.
  apply functional_extensionality; intro rel.
  unfold mov, upd.
  rewrite dirOfMove_to_Z.
  unfold BB.Machine.step.
  rewrite hState.
  set (bit := BB.Tape.read (BB.cfg_tape 4 cfg) (BB.cfg_head 4 cfg)).
  change (BB.Tape.read (BB.cfg_tape 4 cfg) (BB.cfg_head 4 cfg)) with bit in hNext |- *.
  rewrite hNext.
  set (a := BB.transition 4 M q bit) in *.
  destruct (BB.action_move a);
    cbn [dirOfMove Dir_to_Z BB.move_apply BB.cfg_head BB.cfg_tape];
    symmetry.
  - exact (BB.Tape.read_write_after_move
      Σ sigmaOfBool (BB.cfg_tape 4 cfg) (BB.cfg_head 4 cfg)
      rel BB.left (BB.action_write a)).
  - exact (BB.Tape.read_write_after_move
      Σ sigmaOfBool (BB.cfg_tape 4 cfg) (BB.cfg_head 4 cfg)
      rel BB.right (BB.action_write a)).
Qed.

Lemma step_some_bridge :
  forall (M : BB.machine 4) (cfg : BB.config 4) q q',
    (q < 4)%nat ->
    BB.cfg_state _ cfg = Some q ->
    BB.action_next
      (BB.transition 4 M q (BB.Tape.read (BB.cfg_tape _ cfg) (BB.cfg_head _ cfg))) =
      Some q' ->
    step Σ (tmOfMachine M) (esOfConfig cfg q) =
      Some (esOfConfig (BB.Machine.step M cfg) q').
Proof.
  intros M cfg q q' hqLt hState hNext.
  unfold step, esOfConfig, tmOfMachine, transOfAction.
  rewrite tapeOfConfig_zero.
  rewrite boolOfSigma_sigmaOfBool.
  rewrite (natOfSt_stOfNat_lt_four q hqLt).
  rewrite hNext.
  f_equal.
  f_equal.
  eapply tapeOfConfig_step; eassumption.
Qed.

Lemma run_some_steps_bridge :
  forall (M : BB.machine 4) n q,
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
    destruct (BB.cfg_state 4 prev) as [old|] eqn:hOld.
    + unfold BB.Machine.step in hState.
      rewrite hOld in hState.
      set (bit := BB.Tape.read (BB.cfg_tape 4 prev) (BB.cfg_head 4 prev)) in *.
      destruct (BB.action_next (BB.transition 4 M old bit)) as [next|] eqn:hNext.
      * inversion hState; subst q.
        econstructor.
        -- apply ih. reflexivity.
        -- apply step_some_bridge.
           ++ exact (BBKV.run_state_lt 4 M n old hOld).
           ++ exact hOld.
           ++ exact hNext.
      * discriminate hState.
    + rewrite (BB.Machine.step_of_halted 4 M prev hOld) in hState.
      rewrite hOld in hState. discriminate hState.
Qed.

Lemma step_none_bridge :
  forall (M : BB.machine 4) (cfg : BB.config 4) q,
    (q < 4)%nat ->
    BB.cfg_state _ cfg = Some q ->
    BB.action_next
      (BB.transition 4 M q (BB.Tape.read (BB.cfg_tape _ cfg) (BB.cfg_head _ cfg))) =
      None ->
    step Σ (tmOfMachine M) (esOfConfig cfg q) = None.
Proof.
  intros M cfg q hqLt hState hNext.
  unfold step, esOfConfig, tmOfMachine, transOfAction.
  rewrite tapeOfConfig_zero.
  rewrite boolOfSigma_sigmaOfBool.
  rewrite (natOfSt_stOfNat_lt_four q hqLt).
  rewrite hNext.
  reflexivity.
Qed.

Lemma local_halt_event_to_coqbb4 :
  forall (M : BB.machine 4) n q,
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
    set (bit := BB.Tape.read (BB.cfg_tape 4 (BB.Machine.run M n))
      (BB.cfg_head 4 (BB.Machine.run M n))) in *.
    destruct (BB.action_next (BB.transition 4 M q bit)) as [next|] eqn:hActionNext.
    + discriminate hNextNone.
    + apply step_none_bridge.
      * exact (BBKV.run_state_lt 4 M n q hSome).
      * exact hSome.
      * exact hActionNext.
Qed.

Lemma local_halt_event_to_coqbb4_plus_one :
  forall (M : BB.machine 4) n q,
    BB.cfg_state _ (BB.Machine.run M n) = Some q ->
    BB.cfg_state _ (BB.Machine.run M (S n)) = None ->
    HaltsAtPlusOne Σ (tmOfMachine M) (S n) (InitES Σ Σ0).
Proof.
  intros M n q hSome hNone.
  constructor.
  exact (local_halt_event_to_coqbb4 M n q hSome hNone).
Qed.

Lemma local_halt_event_time_le_one_hundred_seven :
  forall (M : BB.machine 4) n q,
    BB.cfg_state _ (BB.Machine.run M n) = Some q ->
    BB.cfg_state _ (BB.Machine.run M (S n)) = None ->
    (S n <= 107)%nat.
Proof.
  intros M n q hSome hNone.
  pose proof (local_halt_event_to_coqbb4_plus_one M n q hSome hNone) as hHalt.
  pose proof ((proj1 BB4_value) (tmOfMachine M) (S n) hHalt) as hBound.
  unfold BB4 in hBound. exact hBound.
Qed.

Lemma local_halted_has_early_event :
  forall (M : BB.machine 4) t,
    BB.cfg_state _ (BB.Machine.run M t) = None ->
    exists n q,
      (n < t)%nat /\
      BB.cfg_state _ (BB.Machine.run M n) = Some q /\
      BB.cfg_state _ (BB.Machine.run M (S n)) = None.
Proof. exact (BB.Machine.halted_has_early_event 3). Qed.

Lemma run_add_of_halted :
  forall (states : nat) (M : BB.machine states) h k,
    BB.cfg_state _ (BB.Machine.run M h) = None ->
    BB.Machine.run M (h + k) = BB.Machine.run M h.
Proof. exact BB.Machine.run_add_of_halted. Qed.

Lemma local_run_eq_early_halt_event :
  forall (M : BB.machine 4) t n q,
    (n < t)%nat ->
    BB.cfg_state _ (BB.Machine.run M n) = Some q ->
    BB.cfg_state _ (BB.Machine.run M (S n)) = None ->
    BB.Machine.run M t = BB.Machine.run M (S n).
Proof. exact (fun M t n _ hlt _ hEvent =>
  BB.Machine.run_eq_early_halt_event 4 M t n hlt hEvent). Qed.

Theorem four_state_halting_time_bound_event :
  forall (M : BB.machine 4) t,
    BB.cfg_state _ (BB.Machine.run M t) = None ->
    exists h,
      (h <= 107)%nat /\
      BB.cfg_state _ (BB.Machine.run M h) = None /\
      BB.Machine.run M t = BB.Machine.run M h.
Proof.
  intros M t hNone.
  destruct (local_halted_has_early_event M t hNone) as
    [n [q [hlt [hSome hEvent]]]].
  exists (S n).
  repeat split.
  - exact (local_halt_event_time_le_one_hundred_seven M n q hSome hEvent).
  - exact hEvent.
  - apply local_run_eq_early_halt_event with (q := q); assumption.
Qed.

(* A positive local time is attained precisely by a live configuration at *)
(* the preceding run and a halted configuration after its final action.   *)
Definition HaltsAtTime {states : nat} (M : BB.machine states) (time : nat) : Prop :=
  exists n q,
    time = S n /\
    BB.cfg_state _ (BB.Machine.run M n) = Some q /\
    BB.cfg_state _ (BB.Machine.run M time) = None.

Lemma haltsAtTime_is_first : forall states (M : BB.machine states) time,
  HaltsAtTime M time ->
  forall earlier, (earlier < time)%nat ->
    exists q, BB.cfg_state _ (BB.Machine.run M earlier) = Some q.
Proof.
  intros states M time [n [q [hTime [hPrev _]]]] earlier hEarlier.
  subst time.
  destruct (BB.cfg_state states (BB.Machine.run M earlier)) as [old|] eqn:hOld.
  - exists old. reflexivity.
  - exfalso.
    assert (hLe : (earlier <= n)%nat) by lia.
    assert (hRun : BB.Machine.run M n = BB.Machine.run M earlier).
    { replace n with (earlier + (n - earlier))%nat by lia.
      apply run_add_of_halted. exact hOld. }
    rewrite hRun in hPrev.
    rewrite hOld in hPrev.
    discriminate.
Qed.

Definition AttainableHaltingTime (states time : nat) : Prop :=
  exists M : BB.machine states, HaltsAtTime M time.

Definition ExactBusyBeaverTime (states time : nat) : Prop :=
  AttainableHaltingTime states time /\
  forall candidate, AttainableHaltingTime states candidate -> (candidate <= time)%nat.

Lemma tmOf_sigma4Champion_eq_BB4_champion :
  tmOfMachine BBKV.sigma4Champion = BB4_champion.
Proof.
  apply functional_extensionality; intro s.
  apply functional_extensionality; intro i.
  destruct s, i; reflexivity.
Qed.

Theorem sigma4Champion_halts_at_time_107 :
  HaltsAtTime BBKV.sigma4Champion 107.
Proof.
  exists 106%nat, 2%nat.
  vm_compute.
  repeat split; reflexivity.
Qed.

Theorem sigma4Champion_maps_to_coqbb4_halt_at_106 :
  HaltsAt Σ (tmOfMachine BBKV.sigma4Champion) 106 (InitES Σ Σ0).
Proof.
  apply local_halt_event_to_coqbb4 with (q := 2%nat);
    vm_compute; reflexivity.
Qed.

Theorem attainableHaltingTime_four_107 :
  AttainableHaltingTime 4 107.
Proof.
  exists BBKV.sigma4Champion.
  exact sigma4Champion_halts_at_time_107.
Qed.

Theorem attainableHaltingTime_four_le_107 : forall candidate,
  AttainableHaltingTime 4 candidate -> (candidate <= 107)%nat.
Proof.
  intros candidate [M [n [q [hCandidate [hSome hNone]]]]].
  subst candidate.
  exact (local_halt_event_time_le_one_hundred_seven M n q hSome hNone).
Qed.

Theorem busy_beaver_time_four_eq_107 :
  ExactBusyBeaverTime 4 107.
Proof.
  split.
  - exact attainableHaltingTime_four_107.
  - exact attainableHaltingTime_four_le_107.
Qed.

End BusyBeaverBB4Bridge.
