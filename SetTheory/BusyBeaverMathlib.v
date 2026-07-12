(* ===================================================================== *)
(*  BusyBeaverMathlib.v                                                  *)
(*                                                                       *)
(*  Coq counterpart of the Lean mathlib-facing BusyBeaver bridge.        *)
(*  Lean's file connects SetTheory.BusyBeaver to mathlib's Turing        *)
(*  machine and partial-recursive-code library; this Coq development has *)
(*  no such dependency.  The low-level compiler connection is therefore  *)
(*  exposed as an explicit record, while the reusable finite tape/counting*)
(*  lemmas and the domination consequence are proved directly.           *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Lia List ZArith.
From SetTheory Require Import BusyBeaver.
Import ListNotations.

Module BB := BusyBeaver.

Module BusyBeaverMathlib.

Theorem list_length_le_of_nodup_subset :
  forall (A : Type) (xs ys : list A),
    NoDup xs -> (forall x, In x xs -> In x ys) ->
    length xs <= length ys.
Proof.
  exact @NoDup_incl_length.
Qed.

Theorem tape_mem_of_read_true : forall tape pos,
  BB.Tape.read tape pos = true -> In pos tape.
Proof.
  intros tape pos h.
  unfold BB.Tape.read in h.
  destruct (in_dec Z.eq_dec pos tape) as [hin | hnot].
  - exact hin.
  - discriminate.
Qed.

(* The `NoDup tape` hypothesis is not needed by this Coq proof
   (`NoDup_incl_length` counts only the left list), but it is kept for
   statement parity with the Lean counterpart, whose erase-based counting
   argument genuinely uses it. *)
Theorem positions_length_le_tape_length_of_read_true :
  forall positions tape,
    NoDup positions ->
    NoDup tape ->
    (forall pos, In pos positions -> BB.Tape.read tape pos = true) ->
    length positions <= length tape.
Proof.
  intros positions tape hPositions _hTape hRead.
  apply list_length_le_of_nodup_subset.
  - exact hPositions.
  - intros pos hpos.
    apply tape_mem_of_read_true.
    exact (hRead pos hpos).
Qed.

Definition rado_positions_of_nat_offsets (head : Z)
    (offsets : list nat) : BB.tape :=
  map (fun n => (head + Z.of_nat n)%Z) offsets.

Theorem nat_offset_position_injective : forall head,
  forall a b,
    (head + Z.of_nat a = head + Z.of_nat b)%Z -> a = b.
Proof.
  intros head a b h.
  apply Nat2Z.inj.
  lia.
Qed.

Theorem rado_positions_of_nat_offsets_nodup :
  forall head offsets,
    NoDup offsets -> NoDup (rado_positions_of_nat_offsets head offsets).
Proof.
  intros head offsets h.
  unfold rado_positions_of_nat_offsets.
  apply NoDup_map_NoDup_ForallPairs.
  - intros a b _ _ hab.
    exact (nat_offset_position_injective head a b hab).
  - exact h.
Qed.

Theorem rado_positions_of_nat_offsets_length :
  forall head offsets,
    length (rado_positions_of_nat_offsets head offsets) = length offsets.
Proof.
  intros head offsets.
  unfold rado_positions_of_nat_offsets.
  apply length_map.
Qed.

Theorem rado_positions_of_nat_offsets_read_true :
  forall head offsets tape,
    (forall n, In n offsets ->
      BB.Tape.read tape (head + Z.of_nat n)%Z = true) ->
    forall pos,
      In pos (rado_positions_of_nat_offsets head offsets) ->
      BB.Tape.read tape pos = true.
Proof.
  intros head offsets tape hRead pos hpos.
  unfold rado_positions_of_nat_offsets in hpos.
  apply in_map_iff in hpos.
  destruct hpos as [n [hpos hn]].
  rewrite <- hpos.
  exact (hRead n hn).
Qed.

Definition fintype_card_sum (left_card right_card : nat) : nat :=
  left_card + right_card.

Fixpoint initInputTape (input : list bool) (k : nat) : BB.tape :=
  match k with
  | O => []
  | S j => BB.Tape.write (initInputTape input j) (Z.of_nat j)
      (nth j input false)
  end.

Theorem initInputTape_zero : forall input,
  initInputTape input 0 = [].
Proof.
  reflexivity.
Qed.

Theorem initInputTape_succ : forall input k,
  initInputTape input (S k) =
    BB.Tape.write (initInputTape input k) (Z.of_nat k)
      (nth k input false).
Proof.
  reflexivity.
Qed.

Theorem initInputTape_read_nat : forall input k j,
  BB.Tape.read (initInputTape input k) (Z.of_nat j) =
    if Nat.ltb j k then nth j input false else false.
Proof.
  intros input k.
  induction k as [|k IH]; intros j.
  - simpl.
    unfold BB.Tape.read.
    destruct (in_dec Z.eq_dec (Z.of_nat j) []); [contradiction | ].
    reflexivity.
  - simpl.
    destruct (Nat.eq_dec j k) as [heq | hne].
    + subst j.
      rewrite BB.Tape.read_write_same.
      destruct (Nat.ltb_spec0 k (S k)); [reflexivity | lia].
    + rewrite BB.Tape.read_write_of_ne.
      * rewrite IH.
        destruct (Nat.ltb_spec0 j k);
          destruct (Nat.ltb_spec0 j (S k)); try reflexivity; lia.
      * intro h.
        apply Nat2Z.inj in h.
        contradiction.
Qed.

Theorem initInputTape_read_neg : forall input k n,
  BB.Tape.read (initInputTape input k) (- Z.of_nat (S n))%Z = false.
Proof.
  intros input k.
  induction k as [|k IH]; intros n.
  - simpl.
    unfold BB.Tape.read.
    destruct (in_dec Z.eq_dec (- Z.of_nat (S n))%Z []); [contradiction | ].
    reflexivity.
  - simpl.
    rewrite BB.Tape.read_write_of_ne.
    + exact (IH n).
    + lia.
Qed.

Theorem initInputTape_matches_tm0_init : forall input,
  (forall j,
    BB.Tape.read (initInputTape input (length input)) (Z.of_nat j) =
      nth j input false) /\
  (forall n,
    BB.Tape.read (initInputTape input (length input))
      (- Z.of_nat (S n))%Z = false).
Proof.
  intros input.
  split.
  - intro j.
    rewrite initInputTape_read_nat.
    destruct (Nat.ltb_spec0 j (length input)) as [hlt | hle].
    + reflexivity.
    + symmetry.
      apply nth_overflow.
      lia.
  - intro n.
    apply initInputTape_read_neg.
Qed.

Inductive TM0RadoState (Label : Type) : Type :=
| tm0Normal : Label -> TM0RadoState Label
| tm0WriteReturn : Label -> TM0RadoState Label.

Arguments tm0Normal {Label} _.
Arguments tm0WriteReturn {Label} _.

Inductive InitThenTM0State (Label : Type) : Type :=
| initWrite : nat -> InitThenTM0State Label
| initReturn : nat -> InitThenTM0State Label
| initSim : TM0RadoState Label -> InitThenTM0State Label.

Arguments initWrite {Label} _.
Arguments initReturn {Label} _.
Arguments initSim {Label} _.

Definition initThenTM0ToTypedRado {Label : Type}
    (start : Label) (sim : BB.typed_machine (TM0RadoState Label))
    (input : list bool) : BB.typed_machine (InitThenTM0State Label) :=
  {| BB.typed_transition := fun state bit =>
      match state with
      | initWrite k =>
          let out := nth k input false in
          if Nat.ltb (S k) (length input) then
            (out, BB.right, Some (initWrite (S k)))
          else
            (out, BB.right, Some (initReturn k))
      | initReturn k =>
          if Nat.eqb k 0 then
            (bit, BB.left, Some (initSim (tm0Normal start)))
          else
            (bit, BB.left, Some (initReturn (Nat.pred k)))
      | initSim simState =>
          let '(write, mv, next) :=
            BB.typed_transition (TM0RadoState Label) sim simState bit in
          (write, mv, option_map initSim next)
      end |}.

Definition liftSimCfg {Label : Type} {input : list bool}
    (cfg : BB.typed_config (TM0RadoState Label)) :
    BB.typed_config (InitThenTM0State Label) :=
  {| BB.typed_cfg_state :=
       match BB.typed_cfg_state _ cfg with
       | Some state => Some (initSim state)
       | None => None
       end;
     BB.typed_cfg_head := BB.typed_cfg_head _ cfg;
     BB.typed_cfg_tape := BB.typed_cfg_tape _ cfg |}.

Theorem liftSimCfg_step : forall Label start
    (sim : BB.typed_machine (TM0RadoState Label)) input
    (cfg : BB.typed_config (TM0RadoState Label)),
  BB.TypedMachine.step (initThenTM0ToTypedRado start sim input)
    (liftSimCfg (input := input) cfg) =
  liftSimCfg (input := input) (BB.TypedMachine.step sim cfg).
Proof.
  intros Label start sim input [state head tape].
  destruct state as [state | ].
  - unfold liftSimCfg, BB.TypedMachine.step, initThenTM0ToTypedRado.
    simpl.
    destruct (BB.typed_transition (TM0RadoState Label) sim state
      (BB.Tape.read tape head)) as [[write mv] next].
    reflexivity.
  - reflexivity.
Qed.

Definition TypedMachineReaches {State : Type}
    (M : BB.typed_machine State)
    (cfg cfg' : BB.typed_config State) : Prop :=
  exists t, BB.TypedMachine.runFrom M cfg t = cfg'.

Theorem typedMachineReaches_refl : forall State
    (M : BB.typed_machine State) cfg,
  TypedMachineReaches M cfg cfg.
Proof.
  intros State M cfg.
  exists 0. reflexivity.
Qed.

Theorem typedMachineReaches_step_eq : forall State
    (M : BB.typed_machine State) cfg cfg',
  BB.TypedMachine.step M cfg = cfg' ->
  TypedMachineReaches M cfg cfg'.
Proof.
  intros State M cfg cfg' h.
  exists 1. simpl. exact h.
Qed.

Theorem typedMachine_runFrom_add : forall State
    (M : BB.typed_machine State) cfg t u,
  BB.TypedMachine.runFrom M cfg (t + u) =
    BB.TypedMachine.runFrom M (BB.TypedMachine.runFrom M cfg t) u.
Proof.
  intros State M cfg t u.
  induction u as [|u IH].
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite Nat.add_succ_r. simpl.
    rewrite IH. reflexivity.
Qed.

Theorem typedMachineReaches_trans : forall State
    (M : BB.typed_machine State) cfg1 cfg2 cfg3,
  TypedMachineReaches M cfg1 cfg2 ->
  TypedMachineReaches M cfg2 cfg3 ->
  TypedMachineReaches M cfg1 cfg3.
Proof.
  intros State M cfg1 cfg2 cfg3 [t ht] [u hu].
  exists (t + u).
  rewrite typedMachine_runFrom_add.
  rewrite ht.
  exact hu.
Qed.

Lemma liftSimCfg_runFrom : forall Label start
    (sim : BB.typed_machine (TM0RadoState Label)) input
    (cfg : BB.typed_config (TM0RadoState Label)) t,
  BB.TypedMachine.runFrom (initThenTM0ToTypedRado start sim input)
    (liftSimCfg (input := input) cfg) t =
  liftSimCfg (input := input) (BB.TypedMachine.runFrom sim cfg t).
Proof.
  intros Label start sim input cfg t.
  induction t as [|t IH].
  - reflexivity.
  - simpl. rewrite IH. apply liftSimCfg_step.
Qed.

Theorem liftSimCfg_reaches : forall Label start
    (sim : BB.typed_machine (TM0RadoState Label)) input
    cfg cfg',
  TypedMachineReaches sim cfg cfg' ->
  TypedMachineReaches (initThenTM0ToTypedRado start sim input)
    (liftSimCfg (input := input) cfg) (liftSimCfg (input := input) cfg').
Proof.
  intros Label start sim input cfg cfg' [t ht].
  exists t.
  rewrite liftSimCfg_runFrom.
  rewrite ht.
  reflexivity.
Qed.

(* The `input` parameter is unused in the body (the Coq state type is not
   input-indexed), but it is kept so call sites mirror the Lean `abbrev`,
   whose start state lives in the input-indexed `Fin input.length`. *)
Definition initThenTM0Start {Label : Type} (input : list bool) :
    BB.typed_config (InitThenTM0State Label) :=
  {| BB.typed_cfg_state := Some (initWrite 0);
     BB.typed_cfg_head := 0%Z;
     BB.typed_cfg_tape := [] |}.

Definition initThenTM0WriteCfg {Label : Type} (input : list bool) (k : nat) :
    BB.typed_config (InitThenTM0State Label) :=
  {| BB.typed_cfg_state := Some (initWrite k);
     BB.typed_cfg_head := Z.of_nat k;
     BB.typed_cfg_tape := initInputTape input k |}.

Definition initThenTM0ReturnCfg {Label : Type} (input : list bool) (k : nat) :
    BB.typed_config (InitThenTM0State Label) :=
  {| BB.typed_cfg_state := Some (initReturn k);
     BB.typed_cfg_head := Z.of_nat (S k);
     BB.typed_cfg_tape := initInputTape input (length input) |}.

Definition initThenTM0SimInitCfg {Label : Type} (start : Label)
    (input : list bool) : BB.typed_config (InitThenTM0State Label) :=
  liftSimCfg (input := input)
    {| BB.typed_cfg_state := Some (tm0Normal start);
       BB.typed_cfg_head := 0%Z;
       BB.typed_cfg_tape := initInputTape input (length input) |}.

Lemma initThenTM0_write_step : forall Label start
    (sim : BB.typed_machine (TM0RadoState Label)) input k,
  S k < length input ->
  BB.TypedMachine.step (initThenTM0ToTypedRado start sim input)
    (initThenTM0WriteCfg (Label := Label) input k) =
  initThenTM0WriteCfg (Label := Label) input (S k).
Proof.
  intros Label start sim input k hlt.
  unfold initThenTM0WriteCfg, initThenTM0ToTypedRado, BB.TypedMachine.step.
  simpl.
  destruct (Nat.ltb_spec0 (S k) (length input)) as [_ | hbad]; [| lia].
  unfold BB.move_apply.
  replace (Z.of_nat k + 1)%Z with (Z.of_nat (S k)) by lia.
  reflexivity.
Qed.

Lemma initThenTM0_last_write_step : forall Label start
    (sim : BB.typed_machine (TM0RadoState Label)) input k,
  k < length input ->
  ~ S k < length input ->
  BB.TypedMachine.step (initThenTM0ToTypedRado start sim input)
    (initThenTM0WriteCfg (Label := Label) input k) =
  initThenTM0ReturnCfg (Label := Label) input k.
Proof.
  intros Label start sim input k hlt hlast.
  unfold initThenTM0WriteCfg, initThenTM0ReturnCfg,
    initThenTM0ToTypedRado, BB.TypedMachine.step.
  simpl.
  destruct (Nat.ltb_spec0 (S k) (length input)) as [hbad | _]; [lia | ].
  unfold BB.move_apply.
  replace (Z.of_nat k + 1)%Z with (Z.of_nat (S k)) by lia.
  assert (S k = length input) as hlen by lia.
  rewrite <- hlen.
  reflexivity.
Qed.

Lemma initThenTM0_return_step_zero : forall Label start
    (sim : BB.typed_machine (TM0RadoState Label)) input,
  BB.TypedMachine.step (initThenTM0ToTypedRado start sim input)
    (initThenTM0ReturnCfg (Label := Label) input 0) =
  initThenTM0SimInitCfg (Label := Label) start input.
Proof.
  intros Label start sim input.
  unfold initThenTM0ReturnCfg, initThenTM0SimInitCfg, liftSimCfg,
    initThenTM0ToTypedRado, BB.TypedMachine.step.
  simpl.
  rewrite BB.Tape.write_read_self.
  unfold BB.move_apply.
  replace (1 - 1)%Z with 0%Z by lia.
  reflexivity.
Qed.

Lemma initThenTM0_return_step_succ : forall Label start
    (sim : BB.typed_machine (TM0RadoState Label)) input k,
  BB.TypedMachine.step (initThenTM0ToTypedRado start sim input)
    (initThenTM0ReturnCfg (Label := Label) input (S k)) =
  initThenTM0ReturnCfg (Label := Label) input k.
Proof.
  intros Label start sim input k.
  destruct k as [|k].
  - unfold initThenTM0ReturnCfg, initThenTM0ToTypedRado, BB.TypedMachine.step.
    simpl. rewrite BB.Tape.write_read_self. reflexivity.
  - unfold initThenTM0ReturnCfg, initThenTM0ToTypedRado, BB.TypedMachine.step.
    simpl. rewrite BB.Tape.write_read_self.
    unfold BB.move_apply.
    f_equal.
    change (Z.of_nat (S (S (S k))) - 1 = Z.of_nat (S (S k)))%Z.
    lia.
Qed.

Theorem initThenTM0_write_reaches : forall Label start
    (sim : BB.typed_machine (TM0RadoState Label)) input,
  0 < length input ->
  forall k, k < length input ->
  TypedMachineReaches (initThenTM0ToTypedRado start sim input)
    (initThenTM0Start (Label := Label) input)
    (initThenTM0WriteCfg (Label := Label) input k).
Proof.
  intros Label start sim input hInput k hk.
  induction k as [|k IH].
  - apply typedMachineReaches_refl.
  - assert (hkPrev : k < length input) by lia.
    destruct (IH hkPrev) as [t ht].
    exists (S t).
    simpl. rewrite ht.
    apply initThenTM0_write_step.
    exact hk.
Qed.

Theorem initThenTM0_return_reaches : forall Label start
    (sim : BB.typed_machine (TM0RadoState Label)) input k,
  k < length input ->
  TypedMachineReaches (initThenTM0ToTypedRado start sim input)
    (initThenTM0ReturnCfg (Label := Label) input k)
    (initThenTM0SimInitCfg (Label := Label) start input).
Proof.
  intros Label start sim input k hk.
  induction k as [|k IH].
  - apply typedMachineReaches_step_eq.
    apply initThenTM0_return_step_zero.
  - assert (hkPrev : k < length input) by lia.
    eapply typedMachineReaches_trans.
    + apply typedMachineReaches_step_eq.
      apply initThenTM0_return_step_succ.
    + exact (IH hkPrev).
Qed.

Theorem initThenTM0_reaches_sim_init : forall Label start
    (sim : BB.typed_machine (TM0RadoState Label)) input,
  0 < length input ->
  TypedMachineReaches (initThenTM0ToTypedRado start sim input)
    (initThenTM0Start (Label := Label) input)
    (initThenTM0SimInitCfg (Label := Label) start input).
Proof.
  intros Label start sim input hInput.
  set (last := length input - 1).
  assert (hLast : last < length input) by (unfold last; lia).
  assert (hNoNext : ~ S last < length input) by (unfold last; lia).
  eapply typedMachineReaches_trans.
  - exact (initThenTM0_write_reaches Label start sim input hInput last hLast).
  - eapply typedMachineReaches_trans.
    + apply typedMachineReaches_step_eq.
      apply initThenTM0_last_write_step; assumption.
    + exact (initThenTM0_return_reaches Label start sim input last hLast).
Qed.

Definition tm0RadoState_card (label_card : nat) : nat :=
  2 * label_card.

Theorem initThenTM0State_card : forall label_card (input : list bool),
  2 * length input + tm0RadoState_card label_card =
  2 * length input + 2 * label_card.
Proof.
  reflexivity.
Qed.

Lemma typedMachine_step_tape_nodup : forall State
    (M : BB.typed_machine State) cfg,
  NoDup (BB.typed_cfg_tape _ cfg) ->
  NoDup (BB.typed_cfg_tape _ (BB.TypedMachine.step M cfg)).
Proof.
  intros State M [state head tape] hNodup.
  destruct state as [state | ]; [| exact hNodup].
  unfold BB.TypedMachine.step.
  simpl.
  destruct (BB.typed_transition State M state (BB.Tape.read tape head))
    as [[write mv] next].
  simpl.
  apply BB.Tape.write_nodup.
  exact hNodup.
Qed.

Lemma typedMachine_runFrom_tape_nodup : forall State
    (M : BB.typed_machine State) cfg t,
  NoDup (BB.typed_cfg_tape _ cfg) ->
  NoDup (BB.typed_cfg_tape _ (BB.TypedMachine.runFrom M cfg t)).
Proof.
  intros State M cfg t hNodup.
  induction t as [|t IH].
  - exact hNodup.
  - simpl. apply typedMachine_step_tape_nodup. exact IH.
Qed.

Theorem tm0_eval_to_init_wrapper_lowerBound : forall Label start
    (sim : BB.typed_machine (TM0RadoState Label)) input haltCfg offsets,
  TypedMachineReaches (initThenTM0ToTypedRado start sim input)
    (initThenTM0Start (Label := Label) input) haltCfg ->
  BB.typed_cfg_state _ haltCfg = None ->
  NoDup offsets ->
  (forall n, In n offsets ->
    BB.Tape.read (BB.typed_cfg_tape _ haltCfg) (Z.of_nat n) = true) ->
  exists score,
    length offsets <= score /\
    BB.TypedMachine.HaltsWithScore
      (initThenTM0ToTypedRado start sim input) (initWrite 0) score.
Proof.
  intros Label start sim input haltCfg offsets [t ht] hState hOffsets hRead.
  pose (positions := rado_positions_of_nat_offsets 0 offsets).
  assert (hPositions : NoDup positions).
  {
    unfold positions.
    apply rado_positions_of_nat_offsets_nodup.
    exact hOffsets.
  }
  assert (hTapeNodup : NoDup (BB.typed_cfg_tape _ haltCfg)).
  {
    rewrite <- ht.
    apply typedMachine_runFrom_tape_nodup.
    constructor.
  }
  assert (hReadPositions : forall pos, In pos positions ->
    BB.Tape.read (BB.typed_cfg_tape _ haltCfg) pos = true).
  {
    unfold positions.
    apply rado_positions_of_nat_offsets_read_true.
    intros n hn.
    change (BB.Tape.read (BB.typed_cfg_tape _ haltCfg) (0 + Z.of_nat n)%Z = true).
    rewrite Z.add_0_l.
    exact (hRead n hn).
  }
  exists (length (BB.typed_cfg_tape _ haltCfg)).
  split.
  - rewrite <- (rado_positions_of_nat_offsets_length 0 offsets).
    exact (positions_length_le_tape_length_of_read_true
      positions (BB.typed_cfg_tape _ haltCfg)
      hPositions hTapeNodup hReadPositions).
  - exists t.
    unfold BB.TypedMachine.run.
    change (BB.typed_cfg_state _ (BB.TypedMachine.runFrom
      (initThenTM0ToTypedRado start sim input)
      (initThenTM0Start (Label := Label) input) t) = None /\
      length (BB.typed_cfg_tape _ (BB.TypedMachine.runFrom
        (initThenTM0ToTypedRado start sim input)
        (initThenTM0Start (Label := Label) input) t)) =
      length (BB.typed_cfg_tape _ haltCfg)).
    rewrite ht.
    split.
    + exact hState.
    + reflexivity.
Qed.

Definition TM1to1EncodedInput {Gamma : Type}
    (enc : Gamma -> list bool) (input : list Gamma) : list bool :=
  flat_map enc input.

Theorem TM1to1EncodedInput_length : forall Gamma width
    (enc : Gamma -> list bool) input,
  (forall a, length (enc a) = width) ->
  length (TM1to1EncodedInput enc input) = length input * width.
Proof.
  intros Gamma width enc input hWidth.
  induction input as [|a rest IH].
  - reflexivity.
  - simpl. rewrite length_app, hWidth, IH. lia.
Qed.

Theorem partrecToTM1Encoding_width_pos : forall width witness,
  witness < width -> 0 < width.
Proof.
  intros width witness h.
  lia.
Qed.

Definition trPosNum_length (p : nat) : nat := S p.
Definition trNum_length (n : nat) : nat := S n.
Definition trNat_length (n : nat) : nat := S n.
Definition trList_singleton_length (n : nat) : nat := S (S n).

Theorem tm2to1_trInit_length_pos : forall input_length,
  0 < S input_length.
Proof.
  intros input_length. lia.
Qed.

Theorem encoded_partrec_input_length_pos : forall input_length width,
  0 < input_length -> 0 < width -> 0 < input_length * width.
Proof.
  intros input_length width hInput hWidth.
  apply Nat.mul_pos_pos; assumption.
Qed.

Theorem tm2to1_trInit_length_le_succ : forall input_length,
  S input_length <= input_length + 1.
Proof.
  intros input_length. lia.
Qed.

Theorem encoded_partrec_input_length_le : forall width n,
  width * (S n) <= width * (n + 2).
Proof.
  intros width n.
  apply Nat.mul_le_mono_l.
  lia.
Qed.

(* --------------------------------------------------------------------- *)
(*  Encoded-input budget arithmetic.                                      *)
(*                                                                        *)
(*  Coq counterparts of the Lean theorems                                 *)
(*  `linear_mul_le_two_pow_pred_of_large`,                                *)
(*  `nat_size_linear_le_self_of_large`,                                   *)
(*  `init_wrapper_state_count_le_linear`, and                             *)
(*  `init_wrapper_state_count_le_linear_size` from                        *)
(*  `lean/SetTheory/BusyBeaverMathlib.lean`, proved here from plain nat   *)
(*  arithmetic.  `nat_size` below is the Coq analogue of Lean's           *)
(*  `Nat.size` (binary bit length).                                       *)
(* --------------------------------------------------------------------- *)

Definition nat_size (n : nat) : nat :=
  match n with
  | O => O
  | S _ => S (Nat.log2 n)
  end.

Lemma lt_nat_size : forall m n, 2 ^ m <= n -> m < nat_size n.
Proof.
  intros m n h.
  assert (hpow : 2 ^ m <> 0) by (apply Nat.pow_nonzero; lia).
  destruct n as [|n']; [lia | ].
  assert (hm : m <= Nat.log2 (S n')).
  {
    rewrite <- (Nat.log2_pow2 m) by lia.
    apply Nat.log2_le_mono.
    exact h.
  }
  simpl. lia.
Qed.

Lemma pow_pred_nat_size_le : forall n, 0 < n -> 2 ^ (nat_size n - 1) <= n.
Proof.
  intros [|n'] h; [lia | ].
  replace (nat_size (S n') - 1) with (Nat.log2 (S n')) by (simpl; lia).
  destruct (Nat.log2_spec (S n')) as [hlow _]; [lia | exact hlow].
Qed.

(* Lean: `Nat.two_mul_sq_add_one_le_two_pow_two_mul`. *)
Lemma two_mul_sq_add_one_le_two_pow_two_mul :
  forall k, 2 * (k * k) + 1 <= 2 ^ (2 * k).
Proof.
  induction k as [|k IH].
  - simpl. lia.
  - replace (2 * S k) with (S (S (2 * k))) by lia.
    rewrite !Nat.pow_succ_r'.
    nia.
Qed.

Theorem linear_mul_le_two_pow_pred_of_large :
  forall D m, 2 * (D + 1) + 1 <= m -> D * m <= 2 ^ (m - 1).
Proof.
  intros D m hm.
  induction hm as [|m hm IH].
  - replace (2 * (D + 1) + 1 - 1) with (2 * (D + 1)) by lia.
    pose proof (two_mul_sq_add_one_le_two_pow_two_mul (D + 1)) as hbase.
    nia.
  - replace (S m - 1) with (S (m - 1)) by lia.
    rewrite Nat.pow_succ_r'.
    nia.
Qed.

Theorem nat_size_linear_le_self_of_large :
  forall D n, 2 ^ (2 * (D + 1) + 1) <= n -> D * nat_size n <= n.
Proof.
  intros D n hn.
  assert (hlt : 2 * (D + 1) + 1 < nat_size n) by (apply lt_nat_size; exact hn).
  assert (hDsize : D * nat_size n <= 2 ^ (nat_size n - 1))
    by (apply linear_mul_le_two_pow_pred_of_large; lia).
  assert (hpow : 2 ^ (2 * (D + 1) + 1) <> 0) by (apply Nat.pow_nonzero; lia).
  apply Nat.le_trans with (2 ^ (nat_size n - 1)); [exact hDsize | ].
  apply pow_pred_nat_size_le.
  lia.
Qed.

Theorem init_wrapper_state_count_le_linear :
  forall width C inputLen s,
    inputLen <= width * (s + 2) -> 0 < s ->
    2 * inputLen + C <= (2 * width + (4 * width + C) + 1) * s.
Proof.
  intros width C inputLen s hInput hs.
  nia.
Qed.

(* Lean's version bounds `Fintype.card (InitThenTM0State Label input)`; the
   Coq development carries that cardinality numerically (see
   `initThenTM0State_card`), so the bound is stated on
   `2 * length input + tm0RadoState_card label_card` directly. *)
Theorem init_wrapper_state_count_le_linear_size :
  forall width label_card (input : list bool) (n : nat),
    length input <= width * (nat_size n + 2) ->
    0 < nat_size n ->
    2 * length input + tm0RadoState_card label_card <=
      (2 * width + (4 * width + tm0RadoState_card label_card) + 1) *
        nat_size n.
Proof.
  intros width label_card input n hInput hSize.
  apply init_wrapper_state_count_le_linear; assumption.
Qed.

Record SupportedCompilerBridge
    (TotalRecursive : (nat -> nat) -> Prop) : Type := {
  bridge_threshold : forall f, TotalRecursive f -> nat;
  bridge_realizes_lower_bound :
    forall f (hf : TotalRecursive f) n,
      bridge_threshold f hf <= n ->
      exists score, f n <= score /\ BB.AttainableScoreAtMost n score
}.

Record TotalRecursiveMathlibBridge
    (TotalRecursiveMathlib : (nat -> nat) -> Prop) : Type := {
  totalRecursiveMathlib_init_wrapper_attainable_lowerBound_with_encoding :
    forall f, TotalRecursiveMathlib f ->
      exists threshold, forall n,
        threshold <= n ->
        exists score, f n <= score /\ BB.AttainableScoreAtMost n score
}.

Theorem totalRecursiveMathlib_hasEventuallyAtMostLowerBoundCompiler :
  forall TotalRecursiveMathlib,
    TotalRecursiveMathlibBridge TotalRecursiveMathlib ->
    BB.HasEventuallyAtMostLowerBoundCompiler TotalRecursiveMathlib.
Proof. exact totalRecursiveMathlib_init_wrapper_attainable_lowerBound_with_encoding. Qed.

Theorem supportedCompilerBridge_has_lowerBoundCompiler :
  forall TotalRecursive,
    SupportedCompilerBridge TotalRecursive ->
    BB.HasEventuallyAtMostLowerBoundCompiler TotalRecursive.
Proof.
  intros TotalRecursive hBridge f hf.
  exists (bridge_threshold TotalRecursive hBridge f hf).
  exact (bridge_realizes_lower_bound TotalRecursive hBridge f hf).
Qed.

Theorem sigma_eventually_dominates_every_supported_total_recursive :
  forall Sigma,
    BB.IsSigma Sigma ->
    forall TotalRecursive,
      SupportedCompilerBridge TotalRecursive ->
      forall f, TotalRecursive f -> BB.EventuallyDominates Sigma f.
Proof.
  intros Sigma hSigma TotalRecursive hBridge f hf.
  exact (BB.eventuallyDominates_of_hasEventuallyAtMostLowerBoundCompiler
    Sigma hSigma TotalRecursive
    (supportedCompilerBridge_has_lowerBoundCompiler TotalRecursive hBridge)
    f hf).
Qed.

Theorem sigma_eventually_dominates_every_totalRecursiveMathlib :
  forall Sigma,
    BB.IsSigma Sigma ->
    forall TotalRecursiveMathlib,
      TotalRecursiveMathlibBridge TotalRecursiveMathlib ->
      forall f, TotalRecursiveMathlib f -> BB.EventuallyDominates Sigma f.
Proof.
  intros Sigma hSigma TotalRecursiveMathlib hBridge f hf.
  exact (BB.eventuallyDominates_of_hasEventuallyAtMostLowerBoundCompiler
    Sigma hSigma TotalRecursiveMathlib
    (totalRecursiveMathlib_hasEventuallyAtMostLowerBoundCompiler
      TotalRecursiveMathlib hBridge) f hf).
Qed.

End BusyBeaverMathlib.
