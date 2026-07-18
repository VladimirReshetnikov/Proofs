(** Canonical, explicit Minsky-machine trace formula for the restricted PA
    proof checker.  This avoids the epsilon-selected graph formula, whose
    behavior is specified only in the standard model. *)

From Stdlib Require Import List Arith Lia Vector
  Logic.FunctionalExtensionality.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import HierarchyReduction.
From BoundedPAConsistency Require Import
  CodedProof CodedCheckerComputability CodedCheckerStructuralComputability
  CodedCheckerDecisionComputability.
From PAListCoding Require Import ComputableFormula.

From Undecidability Require Import
  L.L L.Tactics.Computable
  MinskyMachines.MMA
  MinskyMachines.Reductions.L_computable_closed_to_MMA_computable.
From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import LBool LNat.

Import ListNotations.

Module PABoundedCanonicalCheckerTrace.

Import PA.
Import PAHierarchyReduction.
Import PABoundedCodedProof.
Import PABoundedCodedCheckerDecisionComputability.
Import GenEncode.

(** The characteristic function is repeated here so that its extracted
    lambda term is available as data.  Unlike [chosenGraphFormula], both the
    extracted term and the Minsky program compiled from it live in [Type]. *)
Definition canonicalRestrictedProofFlag (n p : nat) : nat :=
  if checkRestrictedPAProofCode n p then 1 else 0.

#[local] Instance term_canonicalRestrictedProofFlag :
    computable canonicalRestrictedProofFlag.
Proof.
  extract.
Qed.

Definition canonicalCheckerLProgram : L.term :=
  @ext _ (!nat ~> !nat ~> !nat) canonicalRestrictedProofFlag
    term_canonicalRestrictedProofFlag.

Definition canonicalCheckerCounterCount : nat := 1 + 2 + 6.

(** [Argument.COMPUTE] is the constructive compiler used by the upstream
    closed-L-to-Minsky reduction.  Offset one is the conventional entry
    program counter. *)
Definition canonicalCheckerMMAProgram :
    list (MM.mm_instr (Fin.t canonicalCheckerCounterCount)) :=
  @Argument.COMPUTE 2 canonicalCheckerLProgram 1.

Definition canonicalCheckerMMAEnd : nat :=
  @Argument.COMPUTE_len 2 canonicalCheckerLProgram + 1.

Lemma canonicalCheckerMMAEnd_eq_length :
  canonicalCheckerMMAEnd = 1 + length canonicalCheckerMMAProgram.
Proof.
  unfold canonicalCheckerMMAEnd.
  change (@Argument.COMPUTE_len 2 canonicalCheckerLProgram + 1 =
    1 + length (@Argument.COMPUTE 2 canonicalCheckerLProgram 1)).
  rewrite (@Argument.COMPUTE_len_spec 2 canonicalCheckerLProgram 1).
  lia.
Qed.

(** Small syntax-building combinators.  All are transparent, so raw-model
    semantics can later be proved by ordinary induction and simplification. *)
Fixpoint traceConjunction (fs : list PA.formula) : PA.formula :=
  match fs with
  | [] => pEq tZero tZero
  | f :: rest => pAnd f (traceConjunction rest)
  end.

Fixpoint traceDisjunction (fs : list PA.formula) : PA.formula :=
  match fs with
  | [] => pBot
  | f :: rest => pOr f (traceDisjunction rest)
  end.

Fixpoint traceExistsN (n : nat) (f : PA.formula) : PA.formula :=
  match n with
  | 0 => f
  | S k => pEx (traceExistsN k f)
  end.

Definition traceLiftTerm (n : nat) (t : PA.term) : PA.term :=
  Term.rename (fun i => i + n) t.

Definition finIndexNat {n : nat} (i : Fin.t n) : nat :=
  proj1_sig (Fin.to_nat i).

(** A machine state consists of its program counter followed by all nine
    counters.  The local transition block binds old/new values alternately. *)
Definition machineSequenceCount : nat := S canonicalCheckerCounterCount.
Definition localStateSlotCount : nat := 2 * machineSequenceCount.

Definition localCurrent (sequence : nat) : PA.term :=
  tVar (2 * sequence).

Definition localNext (sequence : nat) : PA.term :=
  tVar (S (2 * sequence)).

Definition localPC : PA.term := localCurrent 0.
Definition localNextPC : PA.term := localNext 0.
Definition localRegister (r : nat) : PA.term := localCurrent (S r).
Definition localNextRegister (r : nat) : PA.term := localNext (S r).

Definition registersEqualExcept (except : option nat) : list PA.formula :=
  map (fun r =>
    match except with
    | Some x =>
        if Nat.eq_dec r x then pEq tZero tZero
        else pEq (localNextRegister r) (localRegister r)
    | None => pEq (localNextRegister r) (localRegister r)
    end)
    (seq 0 canonicalCheckerCounterCount).

Definition incTransition (x : nat) : PA.formula :=
  traceConjunction
    ([pEq localNextPC (tSucc localPC);
      pEq (localNextRegister x) (tSucc (localRegister x))] ++
      registersEqualExcept (Some x)).

Definition decTransition (x jump : nat) : PA.formula :=
  pOr
    (traceConjunction
      ([pEq (localRegister x) tZero;
        pEq localNextPC (tSucc localPC)] ++
        registersEqualExcept None))
    (traceConjunction
      ([pEq (localRegister x) (tSucc (localNextRegister x));
        pEq localNextPC (Term.numeral jump)] ++
        registersEqualExcept (Some x))).

Definition instructionTransition
    (entry : nat * MM.mm_instr (Fin.t canonicalCheckerCounterCount))
    : PA.formula :=
  let '(offset, instruction) := entry in
  pAnd (pEq localPC (Term.numeral (S offset)))
    match instruction with
    | MM.mm_inc x => incTransition (finIndexNat x)
    | MM.mm_dec x jump => decTransition (finIndexNat x) jump
    end.

Definition canonicalMachineTransition : PA.formula :=
  traceDisjunction
    (map instructionTransition
      (combine (seq 0 (length canonicalCheckerMMAProgram))
        canonicalCheckerMMAProgram)).

(** The outer trace certificate contains a length followed by one beta
    code/step pair for each state component. *)
Definition outerTraceSlotCount : nat := 1 + 2 * machineSequenceCount.
Definition outerSteps : PA.term := tVar 0.
Definition outerSequenceCode (s : nat) : PA.term := tVar (1 + 2 * s).
Definition outerSequenceStep (s : nat) : PA.term := tVar (2 + 2 * s).

Definition outerEntry (sequence : nat) (index value : PA.term) : PA.formula :=
  Formula.betaTermTermAt value
    (outerSequenceCode sequence) (outerSequenceStep sequence) index.

Definition initialRegisterValue
    (bound certificate : PA.term) (r : nat) : PA.term :=
  match r with
  | 0 => tZero
  | 1 => traceLiftTerm outerTraceSlotCount bound
  | 2 => traceLiftTerm outerTraceSlotCount certificate
  | _ => tZero
  end.

Definition initialTraceConditions
    (bound certificate : PA.term) : list PA.formula :=
  outerEntry 0 tZero (Term.numeral 1) ::
  map (fun r => outerEntry (S r) tZero
      (initialRegisterValue bound certificate r))
    (seq 0 canonicalCheckerCounterCount).

Definition outsideCanonicalProgram (pc : PA.term) : PA.formula :=
  pOr (Formula.ltTermAt pc (Term.numeral 1))
    (Formula.leTermAt (Term.numeral canonicalCheckerMMAEnd) pc).

Definition finalPCCondition : PA.formula :=
  pEx (pAnd
    (Formula.betaTermTermAt (tVar 0)
      (traceLiftTerm 1 (outerSequenceCode 0))
      (traceLiftTerm 1 (outerSequenceStep 0))
      (traceLiftTerm 1 outerSteps))
    (outsideCanonicalProgram (tVar 0))).

Definition finalOutputOneCondition : PA.formula :=
  outerEntry 1 outerSteps (Term.numeral 1).

(** Inside the step block, twenty local state variables precede the bounded
    time index; the outer trace slots begin immediately after it. *)
Definition localTime : PA.term := tVar localStateSlotCount.
Definition localOuterSlot (slot : nat) : PA.term :=
  tVar (S localStateSlotCount + slot).
Definition localSequenceCode (s : nat) : PA.term :=
  localOuterSlot (1 + 2 * s).
Definition localSequenceStep (s : nat) : PA.term :=
  localOuterSlot (2 + 2 * s).

Definition localTraceConditions : list PA.formula :=
  flat_map (fun s =>
    [Formula.betaTermTermAt (localCurrent s)
      (localSequenceCode s) (localSequenceStep s) localTime;
     Formula.betaTermTermAt (localNext s)
      (localSequenceCode s) (localSequenceStep s) (tSucc localTime)])
    (seq 0 machineSequenceCount).

Definition everyTraceStepCondition : PA.formula :=
  pAll (pImp
    (Formula.ltTermAt (tVar 0) (traceLiftTerm 1 outerSteps))
    (traceExistsN localStateSlotCount
      (traceConjunction
        (localTraceConditions ++ [canonicalMachineTransition])))).

(** The canonical graph formula: free variable zero is the hierarchy bound,
    and free variable one is the candidate restricted-proof code.  It says
    that the concrete compiled checker has a finite accepting run. *)
Definition canonicalRestrictedPAProofTermAt
    (bound certificate : PA.term) : PA.formula :=
  traceExistsN outerTraceSlotCount
    (traceConjunction
      (initialTraceConditions bound certificate ++
       [finalPCCondition;
        finalOutputOneCondition;
        everyTraceStepCondition])).

Definition CanonicalRestrictedPAProofFormula : PA.formula :=
  canonicalRestrictedPAProofTermAt (tVar 0) (tVar 1).

(** The explicit formula is definitionally independent of classical epsilon.
    The theorem is useful in audits and prevents accidental regression to the
    old selected graph. *)
Theorem CanonicalRestrictedPAProofFormula_unfold :
  CanonicalRestrictedPAProofFormula =
    canonicalRestrictedPAProofTermAt (tVar 0) (tVar 1).
Proof. reflexivity. Qed.

(** ------------------------------------------------------------------
    Raw semantics of the transparent certificate shell. *)

Lemma raw_traceConjunction : forall (M : RawPAModel)
    (e : nat -> M) fs,
  raw_formula_sat M e (traceConjunction fs) <->
  forall f, In f fs -> raw_formula_sat M e f.
Proof.
  intros M e fs. induction fs as [|f fs IH]; cbn.
  - split.
    + intros _ g hg. contradiction.
    + intros _. reflexivity.
  - rewrite IH. split.
    + intros [hf hrest] g [hg | hg].
      * now subst g.
      * exact (hrest g hg).
    + intro hall. split.
      * apply (hall f). now left.
      * intros g hg. apply (hall g). now right.
Qed.

Lemma raw_traceDisjunction : forall (M : RawPAModel)
    (e : nat -> M) fs,
  raw_formula_sat M e (traceDisjunction fs) <->
  exists f, In f fs /\ raw_formula_sat M e f.
Proof.
  intros M e fs. induction fs as [|f fs IH]; cbn.
  - split; [contradiction | intros [g [[] _]]].
  - rewrite IH. split.
    + intros [hf | hrest].
      * exists f. split; [now left | exact hf].
      * destruct hrest as [g [hg hsat]].
        exists g. split; [now right | exact hsat].
    + intros [g [[hg | hg] hsat]].
      * left. now subst g.
      * right. exists g. split; assumption.
Qed.

Definition traceSlotEnv (M : RawPAModel) (n : nat)
    (slots e : nat -> M) (i : nat) : M :=
  if i <? n then slots i else e (i - n).

Arguments traceSlotEnv M n slots e i : clear implicits.

Lemma traceSlotEnv_of_lt : forall (M : RawPAModel) n slots e i,
  i < n -> traceSlotEnv M n slots e i = slots i.
Proof.
  intros M n slots e i hi. unfold traceSlotEnv.
  assert ((i <? n) = true) by (apply Nat.ltb_lt; exact hi).
  now rewrite H.
Qed.

Arguments traceSlotEnv_of_lt M n slots e i _ : clear implicits.

Lemma traceSlotEnv_of_ge : forall (M : RawPAModel) n slots e i,
  n <= i -> traceSlotEnv M n slots e i = e (i - n).
Proof.
  intros M n slots e i hi. unfold traceSlotEnv.
  assert ((i <? n) = false) by (apply Nat.ltb_ge; exact hi).
  now rewrite H.
Qed.

Arguments traceSlotEnv_of_ge M n slots e i _ : clear implicits.

Lemma traceSlotEnv_succ : forall (M : RawPAModel) n slots e,
  traceSlotEnv M n slots (scons M (slots n) e) =
  traceSlotEnv M (S n) slots e.
Proof.
  intros M n slots e. apply functional_extensionality. intro i.
  destruct (Nat.lt_trichotomy i n) as [hlt | [heq | hgt]].
  - rewrite !traceSlotEnv_of_lt by lia. reflexivity.
  - subst i.
    rewrite traceSlotEnv_of_ge by lia.
    rewrite traceSlotEnv_of_lt by lia.
    rewrite Nat.sub_diag. reflexivity.
  - rewrite !traceSlotEnv_of_ge by lia.
    replace (i - n) with (S (i - S n)) by lia.
    reflexivity.
Qed.

Arguments traceSlotEnv_succ M n slots e : clear implicits.

Lemma raw_traceExistsN_of_slots : forall (M : RawPAModel) n f slots e,
  raw_formula_sat M (traceSlotEnv M n slots e) f ->
  raw_formula_sat M e (traceExistsN n f).
Proof.
  intros M n. induction n as [|n IH]; intros f slots e h.
  - cbn in *.
    apply (proj1 (raw_formula_sat_ext M f
      (traceSlotEnv M 0 slots e) e
      (fun i => eq_trans
        (traceSlotEnv_of_ge M 0 slots e i (Nat.le_0_l i))
        (f_equal e (Nat.sub_0_r i))))).
    exact h.
  - cbn. exists (slots n).
    apply (IH f slots (scons M (slots n) e)).
    rewrite traceSlotEnv_succ. exact h.
Qed.

Lemma raw_traceExistsN_iff_slots : forall (M : RawPAModel) n f e,
  raw_formula_sat M e (traceExistsN n f) <->
  exists slots : nat -> M,
    raw_formula_sat M (traceSlotEnv M n slots e) f.
Proof.
  intros M n. induction n as [|n IH]; intros f e.
  - cbn. split; intro h.
    + exists (fun _ => raw_zero M).
      apply (proj1 (raw_formula_sat_ext M f e
        (traceSlotEnv M 0 (fun _ => raw_zero M) e)
        (fun i => eq_sym (eq_trans
          (traceSlotEnv_of_ge M 0 (fun _ => raw_zero M) e i
            (Nat.le_0_l i))
          (f_equal e (Nat.sub_0_r i)))))).
      exact h.
    + destruct h as [slots h].
      apply (proj1 (raw_formula_sat_ext M f
        (traceSlotEnv M 0 slots e) e
        (fun i => eq_trans
          (traceSlotEnv_of_ge M 0 slots e i (Nat.le_0_l i))
          (f_equal e (Nat.sub_0_r i))))).
      exact h.
  - cbn. split.
    + intros [last hlast].
      destruct (proj1 (IH f (scons M last e)) hlast)
        as [slots hslots].
      set (extended := fun i => if i <? n then slots i else last).
      exists extended.
      assert (henv : forall i,
        traceSlotEnv M n slots (scons M last e) i =
        traceSlotEnv M (S n) extended e i).
      {
        intro i. destruct (Nat.lt_trichotomy i n)
          as [hi | [hi | hi]].
        - rewrite !traceSlotEnv_of_lt by lia.
          unfold extended.
          assert ((i <? n) = true) by (apply Nat.ltb_lt; exact hi).
          now rewrite H.
        - subst i. rewrite traceSlotEnv_of_ge by lia.
          rewrite traceSlotEnv_of_lt by lia.
          unfold extended.
          assert ((n <? n) = false) by (apply Nat.ltb_ge; lia).
          rewrite H, Nat.sub_diag. reflexivity.
        - rewrite !traceSlotEnv_of_ge by lia.
          replace (i - n) with (S (i - S n)) by lia.
          reflexivity.
      }
      apply (proj1 (raw_formula_sat_ext M f
        (traceSlotEnv M n slots (scons M last e))
        (traceSlotEnv M (S n) extended e) henv)).
      exact hslots.
    + intros [slots hslots].
      exact (@raw_traceExistsN_of_slots M (S n) f slots e hslots).
Qed.

Theorem raw_CanonicalRestrictedPAProofFormula_certificate : forall
    (M : RawPAModel) (e : nat -> M),
  raw_formula_sat M e CanonicalRestrictedPAProofFormula <->
  exists slots : nat -> M,
    forall f,
      In f
        (initialTraceConditions (tVar 0) (tVar 1) ++
         [finalPCCondition;
          finalOutputOneCondition;
          everyTraceStepCondition]) ->
      raw_formula_sat M
        (traceSlotEnv M outerTraceSlotCount slots e) f.
Proof.
  intros M e.
  unfold CanonicalRestrictedPAProofFormula,
    canonicalRestrictedPAProofTermAt.
  rewrite raw_traceExistsN_iff_slots.
  split.
  - intros [slots h]. exists slots.
    apply (proj1 (@raw_traceConjunction M
      (traceSlotEnv M outerTraceSlotCount slots e) _) h).
  - intros [slots h]. exists slots.
    apply (proj2 (@raw_traceConjunction M
      (traceSlotEnv M outerTraceSlotCount slots e) _)). exact h.
Qed.

(** ------------------------------------------------------------------
    Standard computation agreement for the concrete compiled program. *)

Definition canonicalCheckerInputVector (n p : nat) : Vector.t nat 2 :=
  Vector.cons nat n 1 (Vector.cons nat p 0 (Vector.nil nat)).

Lemma canonicalCheckerLProgram_closed : L.closed canonicalCheckerLProgram.
Proof.
  unfold canonicalCheckerLProgram.
  exact (proj1 (@proc_ext _ (!nat ~> !nat ~> !nat)
    canonicalRestrictedProofFlag term_canonicalRestrictedProofFlag)).
Qed.

Lemma canonicalCheckerLProgram_eval : forall n p,
  L.eval
    (L.app (L.app canonicalCheckerLProgram (L.nat_enc n))
      (L.nat_enc p))
    (L.nat_enc (canonicalRestrictedProofFlag n p)).
Proof.
  intros n p. unfold canonicalCheckerLProgram.
  exact (extracted_binary_eval term_canonicalRestrictedProofFlag n p).
Qed.

Theorem canonicalCheckerMMAProgram_computes : forall n p,
  sss.sss_compute (@mma_sss canonicalCheckerCounterCount)
    (1, canonicalCheckerMMAProgram)
    (1, Vector.append
      (Vector.cons nat 0 2 (canonicalCheckerInputVector n p))
      vec.vec_zero)
    (canonicalCheckerMMAEnd,
      Vector.cons nat (canonicalRestrictedProofFlag n p) (2 + 6)
        vec.vec_zero).
Proof.
  intros n p.
  pose proof (canonicalCheckerLProgram_eval n p) as heval.
  assert (hclosed : L.closed
      (L.app (L.app canonicalCheckerLProgram (L.nat_enc n))
        (L.nat_enc p))).
  {
    apply L_facts.app_closed.
    - apply L_facts.app_closed.
      + apply canonicalCheckerLProgram_closed.
      + apply L_facts.closed_nat_enc.
    - apply L_facts.closed_nat_enc.
  }
  destruct (proj1 (@wCBV.machine_correctness _ _ hclosed) heval)
    as [y [hflatten hmachine]].
  pose proof (@Argument.simulation 2 canonicalCheckerLProgram 1 y
    (canonicalRestrictedProofFlag n p)
    (canonicalCheckerInputVector n p) hmachine hflatten) as hrun.
  unfold canonicalCheckerCounterCount, canonicalCheckerMMAProgram,
    canonicalCheckerMMAEnd.
  exact hrun.
Qed.

End PABoundedCanonicalCheckerTrace.
