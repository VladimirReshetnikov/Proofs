(* ===================================================================== *)
(*  BusyBeaver.v                                                         *)
(*                                                                       *)
(*  Coq counterpart of the standalone Lean SetTheory.BusyBeaver module.  *)
(*  It keeps the Rado-style machine interface and the domination theorem *)
(*  independent of any particular computability library.                 *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Bool.Bool Lia List ZArith.
Import ListNotations.

Module BusyBeaver.

Inductive move : Type :=
| left
| right.

Definition move_apply (m : move) (pos : Z) : Z :=
  match m with
  | left => (pos - 1)%Z
  | right => (pos + 1)%Z
  end.

Record action := {
  action_write : bool;
  action_move : move;
  action_next : option nat
}.

Record machine (states : nat) := {
  transition : nat -> bool -> action;
  transition_next_lt : forall q bit next,
    action_next (transition q bit) = Some next -> next < states
}.

Definition typed_action (stateType : Type) := (bool * move * option stateType)%type.

Record typed_machine (stateType : Type) := {
  typed_transition : stateType -> bool -> typed_action stateType
}.

Definition tape : Type := list Z.

Module Tape.

Definition read (t : tape) (pos : Z) : bool :=
  if in_dec Z.eq_dec pos t then true else false.

Definition write (t : tape) (pos : Z) (bit : bool) : tape :=
  if bit then
    if in_dec Z.eq_dec pos t then t else pos :: t
  else
    filter (fun q => negb (Z.eqb q pos)) t.

Lemma read_write_same : forall t pos bit,
  read (write t pos bit) pos = bit.
Proof.
  intros t pos bit.
  destruct bit.
  - unfold read, write.
    destruct (in_dec Z.eq_dec pos t) as [hin | hnot].
    + destruct (in_dec Z.eq_dec pos t); [reflexivity | contradiction].
    + destruct (in_dec Z.eq_dec pos (pos :: t)).
      * reflexivity.
      * exfalso. apply n. left. reflexivity.
  - unfold read, write.
    destruct (in_dec Z.eq_dec pos (filter (fun q => negb (Z.eqb q pos)) t))
      as [hin | hnot].
    + apply filter_In in hin.
      destruct hin as [_ hneq].
      rewrite Z.eqb_refl in hneq. discriminate.
    + reflexivity.
Qed.

Lemma read_write_of_ne : forall t pos q,
  q <> pos -> forall bit, read (write t pos bit) q = read t q.
Proof.
  intros t pos q hne bit.
  destruct bit.
  - unfold read, write.
    destruct (in_dec Z.eq_dec pos t) as [hpos | hnpos].
    + reflexivity.
    + destruct (in_dec Z.eq_dec q (pos :: t)) as [hq | hnq];
        destruct (in_dec Z.eq_dec q t) as [hqt | hnqt];
        try reflexivity.
      * destruct hq as [hq | hq]; [congruence | contradiction].
      * exfalso. apply hnq. right. exact hqt.
  - unfold read, write.
    destruct (in_dec Z.eq_dec q (filter (fun x => negb (Z.eqb x pos)) t))
      as [hqf | hnqf];
      destruct (in_dec Z.eq_dec q t) as [hqt | hnqt].
    + reflexivity.
    + exfalso. apply hnqt. apply filter_In in hqf. exact (proj1 hqf).
    + exfalso. apply hnqf. apply filter_In. split; [exact hqt | ].
      apply negb_true_iff. apply Z.eqb_neq. exact hne.
    + reflexivity.
Qed.

Lemma filter_ne_nodup : forall t pos,
  NoDup t -> NoDup (filter (fun q => negb (Z.eqb q pos)) t).
Proof.
  intros t pos h.
  apply NoDup_filter.
  exact h.
Qed.

Lemma write_nodup : forall t pos bit,
  NoDup t -> NoDup (write t pos bit).
Proof.
  intros t pos bit h.
  destruct bit.
  - unfold write.
    destruct (in_dec Z.eq_dec pos t) as [hin | hnot].
    + exact h.
    + constructor; exact hnot || exact h.
  - unfold write.
    apply filter_ne_nodup.
    exact h.
Qed.

Lemma filter_absent_eq : forall t pos,
  ~ In pos t -> filter (fun q => negb (Z.eqb q pos)) t = t.
Proof.
  induction t as [|x xs IH]; intros pos hnot.
  - reflexivity.
  - simpl.
    destruct (Z.eqb x pos) eqn:heq.
    + apply Z.eqb_eq in heq.
      exfalso. apply hnot. left. exact heq.
    + simpl.
      f_equal.
      apply IH.
      intro hx. apply hnot. right. exact hx.
Qed.

Lemma write_read_self : forall t pos,
  write t pos (read t pos) = t.
Proof.
  intros t pos.
  unfold read.
  destruct (in_dec Z.eq_dec pos t) as [hin | hnot].
  - unfold write.
    destruct (in_dec Z.eq_dec pos t) as [_ | hbad].
    + reflexivity.
    + contradiction.
  - unfold write.
    apply filter_absent_eq.
    exact hnot.
Qed.

Definition shift (t : tape) (delta : Z) : tape :=
  map (fun pos => (pos + delta)%Z) t.

Lemma mem_shift_add_iff : forall t pos delta,
  In (pos + delta)%Z (shift t delta) <-> In pos t.
Proof.
  intros t pos delta.
  unfold shift.
  split.
  - intro h.
    apply in_map_iff in h.
    destruct h as [q [heq hq]].
    assert (q = pos)%Z by lia.
    subst q. exact hq.
  - intro h.
    apply in_map_iff.
    exists pos. split; [reflexivity | exact h].
Qed.

Lemma read_shift_add : forall t pos delta,
  read (shift t delta) (pos + delta)%Z = read t pos.
Proof.
  intros t pos delta.
  unfold read.
  destruct (in_dec Z.eq_dec (pos + delta)%Z (shift t delta)) as [hs | hs];
    destruct (in_dec Z.eq_dec pos t) as [ht | ht]; try reflexivity.
  - exfalso. apply ht. apply (proj1 (mem_shift_add_iff t pos delta)). exact hs.
  - exfalso. apply hs. apply (proj2 (mem_shift_add_iff t pos delta)). exact ht.
Qed.

Lemma shift_filter_ne : forall t pos delta,
  shift (filter (fun q => negb (Z.eqb q pos)) t) delta =
    filter (fun q => negb (Z.eqb q (pos + delta)%Z)) (shift t delta).
Proof.
  induction t as [|a rest IH]; intros pos delta; [reflexivity |].
  unfold shift in *.
  simpl.
  assert (heq : Z.eqb (a + delta) (pos + delta) = Z.eqb a pos).
  {
    destruct (Z.eqb a pos) eqn:hap.
    - apply Z.eqb_eq in hap. subst a. rewrite Z.eqb_refl. reflexivity.
    - apply Z.eqb_neq in hap.
      apply Z.eqb_neq. lia.
  }
  rewrite heq.
  destruct (Z.eqb a pos); simpl; [exact (IH pos delta) |].
  rewrite (IH pos delta). reflexivity.
Qed.

Lemma write_shift_add : forall t pos delta bit,
  write (shift t delta) (pos + delta)%Z bit =
    shift (write t pos bit) delta.
Proof.
  intros t pos delta bit.
  destruct bit.
  - unfold write.
    destruct (in_dec Z.eq_dec (pos + delta)%Z (shift t delta)) as [hs | hs];
      destruct (in_dec Z.eq_dec pos t) as [ht | ht]; try reflexivity.
    + exfalso. apply ht. apply (proj1 (mem_shift_add_iff t pos delta)). exact hs.
    + exfalso. apply hs. apply (proj2 (mem_shift_add_iff t pos delta)). exact ht.
  - unfold write.
    symmetry. apply shift_filter_ne.
Qed.

End Tape.

Definition start_state (states : nat) : option nat :=
  match states with
  | O => None
  | S _ => Some O
  end.

Record config (states : nat) := {
  cfg_state : option nat;
  cfg_head : Z;
  cfg_tape : tape
}.

Record typed_config (stateType : Type) := {
  typed_cfg_state : option stateType;
  typed_cfg_head : Z;
  typed_cfg_tape : tape
}.

Definition config_shift {states : nat} (cfg : config states)
    (delta : Z) : config states :=
  {| cfg_state := cfg_state _ cfg;
     cfg_head := (cfg_head _ cfg + delta)%Z;
     cfg_tape := Tape.shift (cfg_tape _ cfg) delta |}.

Definition config_castLE {states larger : nat}
    (_ : states <= larger) (cfg : config states) : config larger :=
  {| cfg_state := cfg_state _ cfg;
     cfg_head := cfg_head _ cfg;
     cfg_tape := cfg_tape _ cfg |}.

Definition initial (states : nat) : config states :=
  {| cfg_state := start_state states; cfg_head := 0%Z; cfg_tape := [] |}.

Module Machine.

Definition castLE {states larger : nat}
    (h : states <= larger) (M : machine states) : machine larger :=
  {| transition := transition states M;
     transition_next_lt := fun q bit next hnext =>
       Nat.lt_le_trans _ _ _
         (transition_next_lt states M q bit next hnext) h |}.

Definition step {states : nat} (M : machine states)
    (cfg : config states) : config states :=
  match cfg_state _ cfg with
  | None => cfg
  | Some q =>
      let a := transition states M q (Tape.read (cfg_tape _ cfg) (cfg_head _ cfg)) in
      {| cfg_state := action_next a;
         cfg_head := move_apply (action_move a) (cfg_head _ cfg);
         cfg_tape := Tape.write (cfg_tape _ cfg) (cfg_head _ cfg)
           (action_write a) |}
  end.

Lemma move_apply_add : forall mv pos delta,
  move_apply mv (pos + delta)%Z = (move_apply mv pos + delta)%Z.
Proof.
  intros [|] pos delta; unfold move_apply; lia.
Qed.

Lemma step_shift : forall states (M : machine states) cfg delta,
  step M (config_shift cfg delta) = config_shift (step M cfg) delta.
Proof.
  intros states M [st head tp] delta.
  destruct st as [q|]; [|reflexivity].
  unfold step, config_shift. simpl.
  rewrite Tape.read_shift_add.
  destruct (transition states M q (Tape.read tp head)) as [write mv next].
  simpl.
  rewrite move_apply_add, Tape.write_shift_add.
  reflexivity.
Qed.

Lemma step_of_halted : forall states (M : machine states) cfg,
  cfg_state _ cfg = None -> step M cfg = cfg.
Proof.
  intros states M [st head tp] h.
  simpl in h. subst st.
  reflexivity.
Qed.

Fixpoint run {states : nat} (M : machine states) (t : nat) : config states :=
  match t with
  | O => initial states
  | S k => step M (run M k)
  end.

Fixpoint runFrom {states : nat} (M : machine states)
    (cfg : config states) (t : nat) : config states :=
  match t with
  | O => cfg
  | S k => step M (runFrom M cfg k)
  end.

Lemma runFrom_shift : forall states (M : machine states) cfg delta t,
  runFrom M (config_shift cfg delta) t =
    config_shift (runFrom M cfg t) delta.
Proof.
  intros states M cfg delta t.
  induction t as [|t IH]; [reflexivity |].
  simpl. rewrite IH. apply step_shift.
Qed.

Lemma run_add_eq_runFrom : forall states (M : machine states) i k,
  run M (i + k) = runFrom M (run M i) k.
Proof.
  intros states M i k.
  induction k as [|k IH].
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite Nat.add_succ_r. simpl. rewrite IH. reflexivity.
Qed.

Lemma runFrom_add : forall states (M : machine states) cfg i k,
  runFrom M cfg (i + k) = runFrom M (runFrom M cfg i) k.
Proof.
  intros states M cfg i k.
  induction k as [|k IH].
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite Nat.add_succ_r. simpl. rewrite IH. reflexivity.
Qed.

(* Lean: Machine.runFrom_ne_none_of_shift_loop *)
Lemma runFrom_ne_none_of_shift_loop :
  forall states (M : machine states) cfg period delta,
  0 < period ->
  runFrom M cfg period = config_shift cfg delta ->
  (forall r, r < period -> cfg_state _ (runFrom M cfg r) <> None) ->
  forall t, cfg_state _ (runFrom M cfg t) <> None.
Proof.
  intros states M cfg period delta hperiod hloop hactive t.
  induction t as [t IH] using lt_wf_ind.
  destruct (lt_dec t period) as [hlt | hnlt].
  - exact (hactive t hlt).
  - assert (hle : period <= t) by lia.
    set (k := t - period).
    assert (hklt : k < t) by (unfold k; lia).
    assert (hteq : period + k = t) by (unfold k; lia).
    assert (hstate :
        cfg_state _ (runFrom M cfg t) =
        cfg_state _ (runFrom M cfg k)).
    {
      rewrite <- hteq.
      rewrite runFrom_add.
      rewrite hloop.
      rewrite runFrom_shift.
      reflexivity.
    }
    intro hnone.
    apply (IH k hklt).
    rewrite <- hstate.
    exact hnone.
Qed.

Lemma castLE_step : forall states larger (h : states <= larger)
    (M : machine states) cfg,
  step (castLE h M) (config_castLE h cfg) =
    config_castLE h (step M cfg).
Proof.
  intros states larger h M [st head tp].
  destruct st; reflexivity.
Qed.

Lemma start_state_castLE : forall states larger (h : states <= larger),
  0 < states -> start_state larger = start_state states.
Proof.
  intros states larger h hpos.
  destruct states as [|states]; [lia | ].
  destruct larger as [|larger]; [lia | reflexivity].
Qed.

Lemma initial_castLE : forall states larger (h : states <= larger),
  0 < states -> initial larger = config_castLE h (initial states).
Proof.
  intros states larger h hpos.
  unfold initial, config_castLE.
  rewrite (start_state_castLE states larger h hpos).
  reflexivity.
Qed.

Lemma castLE_run : forall states larger (h : states <= larger)
    (M : machine states) t,
  0 < states ->
  run (castLE h M) t = config_castLE h (run M t).
Proof.
  intros states larger h M t hpos.
  induction t as [|t IH].
  - apply initial_castLE. exact hpos.
  - simpl. rewrite IH. apply castLE_step.
Qed.

Definition HaltsWithScore {states : nat} (M : machine states)
    (score : nat) : Prop :=
  exists t, cfg_state _ (run M t) = None /\
    length (cfg_tape _ (run M t)) = score.

(* Lean: Machine.not_haltsWithScore_of_shift_loop_from_run *)
Lemma not_haltsWithScore_of_shift_loop_from_run :
  forall states score (M : machine states) start period delta,
  0 < period ->
  runFrom M (run M start) period = config_shift (run M start) delta ->
  (forall r, r < period ->
    cfg_state _ (runFrom M (run M start) r) <> None) ->
  (forall t, t < start -> cfg_state _ (run M t) <> None) ->
  ~ HaltsWithScore M score.
Proof.
  intros states score M start period delta hperiod hloop
    hactiveLoop hactivePrefix [t [hstate _]].
  destruct (lt_dec t start) as [hlt | hnlt].
  - exact (hactivePrefix t hlt hstate).
  - assert (hstart : start <= t) by lia.
    set (k := t - start).
    assert (hteq : start + k = t) by (unfold k; lia).
    pose proof (runFrom_ne_none_of_shift_loop states M (run M start)
      period delta hperiod hloop hactiveLoop k) as hnever.
    assert (hrunstate :
        cfg_state _ (run M t) =
        cfg_state _ (runFrom M (run M start) k)).
    {
      rewrite <- hteq.
      rewrite run_add_eq_runFrom.
      reflexivity.
    }
    apply hnever.
    rewrite <- hrunstate.
    exact hstate.
Qed.

Lemma castLE_haltsWithScore : forall states larger score
    (h : states <= larger) (M : machine states),
  0 < states ->
  HaltsWithScore M score ->
  HaltsWithScore (castLE h M) score.
Proof.
  intros states larger score h M hpos [t [hhalt hscore]].
  exists t.
  rewrite castLE_run by exact hpos.
  split; exact hhalt || exact hscore.
Qed.

Lemma run_zero_states : forall (M : machine 0) t,
  run M t = initial 0.
Proof.
  intros M t.
  induction t as [|t IH]; [reflexivity | ].
  simpl. rewrite IH. reflexivity.
Qed.

Lemma zero_states_haltsWithScore_eq_zero : forall score (M : machine 0),
  HaltsWithScore M score -> score = 0%nat.
Proof.
  intros score M [t [_ hscore]].
  rewrite run_zero_states in hscore.
  simpl in hscore.
  symmetry. exact hscore.
Qed.

End Machine.

Module TypedMachine.

Definition step {stateType : Type} (M : typed_machine stateType)
    (cfg : typed_config stateType) : typed_config stateType :=
  match typed_cfg_state _ cfg with
  | None => cfg
  | Some q =>
      let '(write, mv, next) :=
        typed_transition stateType M q
          (Tape.read (typed_cfg_tape _ cfg) (typed_cfg_head _ cfg)) in
      {| typed_cfg_state := next;
         typed_cfg_head := move_apply mv (typed_cfg_head _ cfg);
         typed_cfg_tape := Tape.write (typed_cfg_tape _ cfg)
           (typed_cfg_head _ cfg) write |}
  end.

Fixpoint runFrom {stateType : Type} (M : typed_machine stateType)
    (cfg : typed_config stateType) (t : nat) : typed_config stateType :=
  match t with
  | O => cfg
  | S k => step M (runFrom M cfg k)
  end.

Definition run {stateType : Type} (M : typed_machine stateType)
    (start : stateType) (t : nat) : typed_config stateType :=
  runFrom M {| typed_cfg_state := Some start;
               typed_cfg_head := 0%Z;
               typed_cfg_tape := [] |} t.

Definition HaltsWithScore {stateType : Type} (M : typed_machine stateType)
    (start : stateType) (score : nat) : Prop :=
  exists t, typed_cfg_state _ (run M start t) = None /\
    length (typed_cfg_tape _ (run M start t)) = score.

End TypedMachine.

Definition AttainableScore (states score : nat) : Prop :=
  exists M : machine states, Machine.HaltsWithScore M score.

Definition AttainableScoreAtMost (states score : nat) : Prop :=
  exists used, used <= states /\ AttainableScore used score.

Lemma attainableScore_castLE : forall states larger score,
  0 < states -> states <= larger ->
  AttainableScore states score -> AttainableScore larger score.
Proof.
  intros states larger score hpos hle [M hM].
  exists (Machine.castLE hle M).
  exact (Machine.castLE_haltsWithScore states larger score hle M hpos hM).
Qed.

Record IsSigma (Sigma : nat -> nat) : Prop := {
  sigma_upper : forall states score,
    AttainableScore states score -> score <= Sigma states;
  sigma_attained : forall states,
    0 < states -> AttainableScore states (Sigma states)
}.

Definition EventuallyDominates (g f : nat -> nat) : Prop :=
  exists N, forall n, N <= n -> f n <= g n.

Definition HasLinearOverheadBlankCompiler
    (TotalRecursive : (nat -> nat) -> Prop) : Prop :=
  forall f, TotalRecursive f ->
    exists overhead, forall k,
      AttainableScore (k + overhead) (f (k + overhead)).

Definition HasEventuallyAtMostBlankCompiler
    (TotalRecursive : (nat -> nat) -> Prop) : Prop :=
  forall f, TotalRecursive f ->
    exists threshold, forall n,
      threshold <= n -> AttainableScoreAtMost n (f n).

Definition HasEventuallyAtMostLowerBoundCompiler
    (TotalRecursive : (nat -> nat) -> Prop) : Prop :=
  forall f, TotalRecursive f ->
    exists threshold, forall n,
      threshold <= n ->
      exists score, f n <= score /\ AttainableScoreAtMost n score.

Definition TotalRecursiveInRadoModel (f : nat -> nat) : Prop :=
  exists overhead, forall k,
    AttainableScore (k + overhead) (f (k + overhead)).

Definition TotalRecursiveEventuallyInRadoModel (f : nat -> nat) : Prop :=
  exists threshold, forall n,
    threshold <= n -> AttainableScoreAtMost n (f n).

Definition TotalRecursiveEventuallyLowerBoundInRadoModel
    (f : nat -> nat) : Prop :=
  exists threshold, forall n,
    threshold <= n ->
    exists score, f n <= score /\ AttainableScoreAtMost n score.

Theorem score_le_sigma : forall Sigma,
  IsSigma Sigma -> forall states score,
    AttainableScore states score -> score <= Sigma states.
Proof.
  intros Sigma hSigma states score h.
  exact (sigma_upper Sigma hSigma states score h).
Qed.

Theorem sigma_mono_of_pos : forall Sigma,
  IsSigma Sigma -> forall states larger,
    0 < states -> states <= larger -> Sigma states <= Sigma larger.
Proof.
  intros Sigma hSigma states larger hpos hle.
  apply (sigma_upper Sigma hSigma larger).
  apply attainableScore_castLE with (states := states); try assumption.
  apply sigma_attained; assumption.
Qed.

Theorem score_le_sigma_of_atMost : forall Sigma,
  IsSigma Sigma -> forall states score,
    AttainableScoreAtMost states score -> score <= Sigma states.
Proof.
  intros Sigma hSigma states score [used [hused hscore]].
  destruct used as [|used].
  - assert (score = 0%nat) as ->.
    {
      destruct hscore as [M hM].
      exact (Machine.zero_states_haltsWithScore_eq_zero score M hM).
    }
    lia.
  - apply Nat.le_trans with (m := Sigma (S used)).
    + exact (sigma_upper Sigma hSigma (S used) score hscore).
    + exact (sigma_mono_of_pos Sigma hSigma (S used) states
        (Nat.lt_0_succ used) hused).
Qed.

Theorem eventuallyDominates_of_hasLinearOverheadBlankCompiler :
  forall Sigma, IsSigma Sigma ->
  forall TotalRecursive,
    HasLinearOverheadBlankCompiler TotalRecursive ->
  forall f, TotalRecursive f -> EventuallyDominates Sigma f.
Proof.
  intros Sigma hSigma TotalRecursive hCompiler f hf.
  destruct (hCompiler f hf) as [overhead hRealize].
  exists overhead.
  intros n hn.
  replace n with ((n - overhead) + overhead)%nat by lia.
  apply (sigma_upper Sigma hSigma).
  apply hRealize.
Qed.

Theorem eventuallyDominates_of_hasEventuallyAtMostBlankCompiler :
  forall Sigma, IsSigma Sigma ->
  forall TotalRecursive,
    HasEventuallyAtMostBlankCompiler TotalRecursive ->
  forall f, TotalRecursive f -> EventuallyDominates Sigma f.
Proof.
  intros Sigma hSigma TotalRecursive hCompiler f hf.
  destruct (hCompiler f hf) as [threshold hRealize].
  exists threshold.
  intros n hn.
  apply (score_le_sigma_of_atMost Sigma hSigma).
  exact (hRealize n hn).
Qed.

Theorem hasEventuallyAtMostLowerBoundCompiler_of_exact :
  forall TotalRecursive,
    HasEventuallyAtMostBlankCompiler TotalRecursive ->
    HasEventuallyAtMostLowerBoundCompiler TotalRecursive.
Proof.
  intros TotalRecursive hCompiler f hf.
  destruct (hCompiler f hf) as [threshold hRealize].
  exists threshold.
  intros n hn.
  exists (f n).
  split; [lia | exact (hRealize n hn)].
Qed.

Theorem eventuallyDominates_of_hasEventuallyAtMostLowerBoundCompiler :
  forall Sigma, IsSigma Sigma ->
  forall TotalRecursive,
    HasEventuallyAtMostLowerBoundCompiler TotalRecursive ->
  forall f, TotalRecursive f -> EventuallyDominates Sigma f.
Proof.
  intros Sigma hSigma TotalRecursive hCompiler f hf.
  destruct (hCompiler f hf) as [threshold hRealize].
  exists threshold.
  intros n hn.
  destruct (hRealize n hn) as [score [hlower hscore]].
  apply Nat.le_trans with (m := score).
  - exact hlower.
  - apply (score_le_sigma_of_atMost Sigma hSigma); exact hscore.
Qed.

Theorem eventuallyDominates_totalRecursiveInRadoModel :
  forall Sigma, IsSigma Sigma ->
  forall f, TotalRecursiveInRadoModel f -> EventuallyDominates Sigma f.
Proof.
  intros Sigma hSigma f hf.
  eapply eventuallyDominates_of_hasLinearOverheadBlankCompiler.
  - exact hSigma.
  - intros g hg. exact hg.
  - exact hf.
Qed.

Theorem eventuallyDominates_totalRecursiveEventuallyInRadoModel :
  forall Sigma, IsSigma Sigma ->
  forall f, TotalRecursiveEventuallyInRadoModel f ->
    EventuallyDominates Sigma f.
Proof.
  intros Sigma hSigma f hf.
  eapply eventuallyDominates_of_hasEventuallyAtMostBlankCompiler.
  - exact hSigma.
  - intros g hg. exact hg.
  - exact hf.
Qed.

Theorem eventuallyDominates_totalRecursiveEventuallyLowerBoundInRadoModel :
  forall Sigma, IsSigma Sigma ->
  forall f, TotalRecursiveEventuallyLowerBoundInRadoModel f ->
    EventuallyDominates Sigma f.
Proof.
  intros Sigma hSigma f hf.
  eapply eventuallyDominates_of_hasEventuallyAtMostLowerBoundCompiler.
  - exact hSigma.
  - intros g hg. exact hg.
  - exact hf.
Qed.

Theorem sigma_eventually_dominates_every_total_recursive :
  forall Sigma, IsSigma Sigma ->
  forall TotalRecursive,
    HasLinearOverheadBlankCompiler TotalRecursive ->
  forall f, TotalRecursive f -> EventuallyDominates Sigma f.
Proof.
  exact eventuallyDominates_of_hasLinearOverheadBlankCompiler.
Qed.

Theorem sigma_eventually_dominates_every_totalRecursiveInRadoModel :
  forall Sigma, IsSigma Sigma ->
  forall f, TotalRecursiveInRadoModel f -> EventuallyDominates Sigma f.
Proof.
  exact eventuallyDominates_totalRecursiveInRadoModel.
Qed.

Theorem sigma_eventually_dominates_every_totalRecursiveEventuallyInRadoModel :
  forall Sigma, IsSigma Sigma ->
  forall f, TotalRecursiveEventuallyInRadoModel f ->
    EventuallyDominates Sigma f.
Proof.
  exact eventuallyDominates_totalRecursiveEventuallyInRadoModel.
Qed.

Theorem sigma_eventually_dominates_every_totalRecursiveEventuallyLowerBoundInRadoModel :
  forall Sigma, IsSigma Sigma ->
  forall f, TotalRecursiveEventuallyLowerBoundInRadoModel f ->
    EventuallyDominates Sigma f.
Proof.
  exact eventuallyDominates_totalRecursiveEventuallyLowerBoundInRadoModel.
Qed.

End BusyBeaver.
