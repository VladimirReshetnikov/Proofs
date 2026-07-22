(**
  The conventional three-argument natural hyperoperator is Diophantine.

  We use ranks

      0 successor, 1 addition, 2 multiplication, 3 exponentiation,
      4 tetration, 5 pentation, ...

  The uniform hierarchy beginning at exponentiation is evaluated by a small
  deterministic stack machine.  Every machine-state constructor is a
  polynomial, and the only non-polynomial expression in a transition is the
  rank-zero exponentiation branch.  Matiyasevich's exponentiation theorem
  therefore makes the step relation Diophantine.  The generic Diophantine
  reflexive-transitive-closure theorem encodes an arbitrary finite run, while
  determinism and terminality prove that such a run has the intended value.
*)

From Stdlib Require Import Arith Lia Vector.
From PAListCoding Require Import
  ExponentiationDiophantine TetrationDiophantine.
From Undecidability.Shared.Libs.DLW.Utils Require Import rel_iter sums.
From Undecidability.H10 Require Import H10.
From Undecidability.H10.Dio
  Require Import dio_logic dio_expo dio_rt_closure dio_single.

Module PAListHyperoperationDiophantine.

Import PAListExponentiationDiophantine.
Import PAListTetrationDiophantine.

(** Iterate a unary function from one.  Consequently every operation above
    exponentiation sends ordinary argument zero to one. *)
Fixpoint iterateFromOne (f : nat -> nat) (n : nat) : nat :=
  match n with
  | 0 => 1
  | S n => f (iterateFromOne f n)
  end.

(** The uniform hierarchy: level zero is exponentiation, level one is
    tetration, level two is pentation, and so on. *)
Fixpoint hyperoperationCore (rank : nat) : nat -> nat -> nat :=
  match rank with
  | 0 => Nat.pow
  | S rank => fun base argument =>
      iterateFromOne (hyperoperationCore rank base) argument
  end.

Lemma hyperoperationCore_zero : forall base argument,
  hyperoperationCore 0 base argument = Nat.pow base argument.
Proof. reflexivity. Qed.

Lemma hyperoperationCore_succ_zero : forall rank base,
  hyperoperationCore (S rank) base 0 = 1.
Proof. reflexivity. Qed.

Lemma hyperoperationCore_succ_succ : forall rank base argument,
  hyperoperationCore (S rank) base (S argument) =
  hyperoperationCore rank base
    (hyperoperationCore (S rank) base argument).
Proof. reflexivity. Qed.

(** Pentation is named separately only to state the familiar rank-five
    specialization of the general hierarchy. *)
Fixpoint pentation (base argument : nat) : nat :=
  match argument with
  | 0 => 1
  | S argument => tetration base (pentation base argument)
  end.

Lemma hyperoperationCore_one_tetration : forall base argument,
  hyperoperationCore 1 base argument = tetration base argument.
Proof.
  intros base argument; induction argument as [|argument IH].
  - reflexivity.
  - change (Nat.pow base (hyperoperationCore 1 base argument) =
      Nat.pow base (tetration base argument)).
    now rewrite IH.
Qed.

Lemma hyperoperationCore_two_pentation : forall base argument,
  hyperoperationCore 2 base argument = pentation base argument.
Proof.
  intros base argument; induction argument as [|argument IH].
  - reflexivity.
  - change (hyperoperationCore 1 base
      (hyperoperationCore 2 base argument) =
      tetration base (pentation base argument)).
    now rewrite IH, hyperoperationCore_one_tetration.
Qed.

(** Public conventional numbering.  Its arguments are rank, base, and the
    ordinary right-hand argument, in that order. *)
Definition hyperoperator (rank base argument : nat) : nat :=
  match rank with
  | 0 => S argument
  | 1 => base + argument
  | 2 => base * argument
  | S (S (S coreRank)) => hyperoperationCore coreRank base argument
  end.

Lemma hyperoperator_rank_zero : forall base argument,
  hyperoperator 0 base argument = S argument.
Proof. reflexivity. Qed.

Lemma hyperoperator_rank_one : forall base argument,
  hyperoperator 1 base argument = base + argument.
Proof. reflexivity. Qed.

Lemma hyperoperator_rank_two : forall base argument,
  hyperoperator 2 base argument = base * argument.
Proof. reflexivity. Qed.

Lemma hyperoperator_rank_three : forall base argument,
  hyperoperator 3 base argument = Nat.pow base argument.
Proof. reflexivity. Qed.

Lemma hyperoperator_rank_four : forall base argument,
  hyperoperator 4 base argument = tetration base argument.
Proof. exact hyperoperationCore_one_tetration. Qed.

Lemma hyperoperator_rank_five : forall base argument,
  hyperoperator 5 base argument = pentation base argument.
Proof. exact hyperoperationCore_two_pentation. Qed.

(** The injective polynomial pair [(x+y)^2+y]. *)
Definition hyperPair (x y : nat) : nat :=
  (x + y) * (x + y) + y.

Lemma hyperPair_injective : forall x y x' y',
  hyperPair x y = hyperPair x' y' -> x = x' /\ y = y'.
Proof.
  intros x y x' y' Hcode.
  unfold hyperPair in Hcode.
  destruct (Nat.eq_dec (x + y) (x' + y')) as [Hsum | Hsum].
  - split; nia.
  - exfalso; apply Hsum; nia.
Qed.

(** Zero is the empty stack.  A positive stack stores the pending rank and
    the rest of the stack in one injective polynomial code. *)
Definition hyperStackCons (rank stack : nat) : nat :=
  S (hyperPair rank stack).

Lemma hyperStackCons_injective : forall rank stack rank' stack',
  hyperStackCons rank stack = hyperStackCons rank' stack' ->
  rank = rank' /\ stack = stack'.
Proof.
  intros rank stack rank' stack' Hcode.
  apply hyperPair_injective.
  unfold hyperStackCons in Hcode; now injection Hcode.
Qed.

Lemma hyperStackCons_ne_zero : forall rank stack,
  hyperStackCons rank stack <> 0.
Proof. intros; unfold hyperStackCons; discriminate. Qed.

(** Evaluation and return modes use distinct polynomial tags zero and one.
    Both modes retain the fixed base. *)
Definition hyperEvalCode (base rank argument stack : nat) : nat :=
  hyperPair base (hyperPair 0 (hyperPair rank (hyperPair argument stack))).

Definition hyperReturnCode (base value stack : nat) : nat :=
  hyperPair base (hyperPair 1 (hyperPair value stack)).

(** Compositional Diophantine-function rules for the polynomial state
    constructors.  Keeping these constructors opaque prevents the automation
    depth from being consumed by the deliberately nested state layout. *)
Lemma hyperPair_dio_fun (x y : (nat -> nat) -> nat) :
  dio_fun x -> dio_fun y ->
  dio_fun (fun nu => hyperPair (x nu) (y nu)).
Proof. intros; unfold hyperPair; dio auto. Defined.

#[local] Hint Resolve hyperPair_dio_fun : dio_fun_db.

Lemma succ_dio_fun (x : (nat -> nat) -> nat) :
  dio_fun x -> dio_fun (fun nu => S (x nu)).
Proof.
  intro Hx.
  apply dio_fun_equiv with (r := fun nu => 1 + x nu).
  - intro nu; lia.
  - dio auto.
Defined.

#[local] Hint Resolve succ_dio_fun : dio_fun_db.

Lemma hyperStackCons_dio_fun (rank stack : (nat -> nat) -> nat) :
  dio_fun rank -> dio_fun stack ->
  dio_fun (fun nu => hyperStackCons (rank nu) (stack nu)).
Proof.
  intros; unfold hyperStackCons.
  change (dio_fun (fun nu => 1 + hyperPair (rank nu) (stack nu))).
  dio auto.
Defined.

#[local] Hint Resolve hyperStackCons_dio_fun : dio_fun_db.

Lemma hyperEvalCode_dio_fun
    (base rank argument stack : (nat -> nat) -> nat) :
  dio_fun base -> dio_fun rank -> dio_fun argument -> dio_fun stack ->
  dio_fun (fun nu =>
    hyperEvalCode (base nu) (rank nu) (argument nu) (stack nu)).
Proof.
  intros; unfold hyperEvalCode; repeat apply hyperPair_dio_fun; dio auto.
Defined.

#[local] Hint Resolve hyperEvalCode_dio_fun : dio_fun_db.

Lemma hyperReturnCode_dio_fun
    (base value stack : (nat -> nat) -> nat) :
  dio_fun base -> dio_fun value -> dio_fun stack ->
  dio_fun (fun nu => hyperReturnCode (base nu) (value nu) (stack nu)).
Proof.
  intros; unfold hyperReturnCode; repeat apply hyperPair_dio_fun; dio auto.
Defined.

#[local] Hint Resolve hyperReturnCode_dio_fun : dio_fun_db.

Lemma hyperEvalCode_injective : forall
    base rank argument stack base' rank' argument' stack',
  hyperEvalCode base rank argument stack =
    hyperEvalCode base' rank' argument' stack' ->
  base = base' /\ rank = rank' /\ argument = argument' /\ stack = stack'.
Proof.
  intros base rank argument stack base' rank' argument' stack' Hcode.
  unfold hyperEvalCode in Hcode.
  destruct (hyperPair_injective _ _ _ _ Hcode) as [Hbase Hpayload].
  destruct (hyperPair_injective _ _ _ _ Hpayload) as [_ Hwork].
  destruct (hyperPair_injective _ _ _ _ Hwork) as [Hrank Hrest].
  destruct (hyperPair_injective _ _ _ _ Hrest) as [Hargument Hstack].
  auto.
Qed.

Lemma hyperReturnCode_injective : forall
    base value stack base' value' stack',
  hyperReturnCode base value stack = hyperReturnCode base' value' stack' ->
  base = base' /\ value = value' /\ stack = stack'.
Proof.
  intros base value stack base' value' stack' Hcode.
  unfold hyperReturnCode in Hcode.
  destruct (hyperPair_injective _ _ _ _ Hcode) as [Hbase Hpayload].
  destruct (hyperPair_injective _ _ _ _ Hpayload) as [_ Hrest].
  destruct (hyperPair_injective _ _ _ _ Hrest) as [Hvalue Hstack].
  auto.
Qed.

Lemma hyperEvalCode_ne_returnCode : forall
    base rank argument stack base' value stack',
  hyperEvalCode base rank argument stack <>
    hyperReturnCode base' value stack'.
Proof.
  intros base rank argument stack base' value stack' Hcode.
  unfold hyperEvalCode, hyperReturnCode in Hcode.
  destruct (hyperPair_injective _ _ _ _ Hcode) as [_ Hpayload].
  destruct (hyperPair_injective _ _ _ _ Hpayload) as [Htag _].
  discriminate Htag.
Qed.

(** One deterministic evaluator transition.  A positive rank and positive
    argument pushes the lower rank, evaluates the preceding argument at the
    current rank, then return mode evaluates the pending lower-rank call. *)
Definition HyperStep (source target : nat) : Prop :=
  (exists base argument stack,
      source = hyperEvalCode base 0 argument stack /\
      target = hyperReturnCode base (Nat.pow base argument) stack) \/
  (exists rank base stack,
      source = hyperEvalCode base (S rank) 0 stack /\
      target = hyperReturnCode base 1 stack) \/
  (exists rank base argument stack,
      source = hyperEvalCode base (S rank) (S argument) stack /\
      target = hyperEvalCode base (S rank) argument
        (hyperStackCons rank stack)) \/
  (exists rank base value stack,
      source = hyperReturnCode base value (hyperStackCons rank stack) /\
      target = hyperEvalCode base rank value stack).

Lemma HyperStep_eval_rank_zero : forall base argument stack target,
  HyperStep (hyperEvalCode base 0 argument stack) target <->
  target = hyperReturnCode base (Nat.pow base argument) stack.
Proof.
  intros base argument stack target; split.
  - intros [Hpower | [Hzero | [Hsucc | Hreturn]]].
    + destruct Hpower as (base' & argument' & stack' & Hsource & Htarget).
      assert (Hcode : hyperEvalCode base 0 argument stack =
          hyperEvalCode base' 0 argument' stack') by congruence.
      destruct (hyperEvalCode_injective _ _ _ _ _ _ _ _ Hcode)
        as [Hbase [_ [Hargument Hstack]]].
      subst base'; subst argument'; subst stack'; exact Htarget.
    + destruct Hzero as (rank' & base' & stack' & Hsource & _).
      assert (Hcode : hyperEvalCode base 0 argument stack =
          hyperEvalCode base' (S rank') 0 stack') by congruence.
      destruct (hyperEvalCode_injective _ _ _ _ _ _ _ _ Hcode)
        as [_ [Hrank _]].
      discriminate Hrank.
    + destruct Hsucc as (rank' & base' & argument' & stack' & Hsource & _).
      assert (Hcode : hyperEvalCode base 0 argument stack =
          hyperEvalCode base' (S rank') (S argument') stack') by congruence.
      destruct (hyperEvalCode_injective _ _ _ _ _ _ _ _ Hcode)
        as [_ [Hrank _]].
      discriminate Hrank.
    + destruct Hreturn as (rank' & base' & value' & stack' & Hsource & _).
      exfalso; eapply (hyperEvalCode_ne_returnCode
        base 0 argument stack base' value' (hyperStackCons rank' stack')).
      congruence.
  - intro Htarget; left; exists base, argument, stack; auto.
Qed.

Lemma HyperStep_eval_succ_zero : forall rank base stack target,
  HyperStep (hyperEvalCode base (S rank) 0 stack) target <->
  target = hyperReturnCode base 1 stack.
Proof.
  intros rank base stack target; split.
  - intros [Hpower | [Hzero | [Hsucc | Hreturn]]].
    + destruct Hpower as (base' & argument' & stack' & Hsource & _).
      assert (Hcode : hyperEvalCode base (S rank) 0 stack =
          hyperEvalCode base' 0 argument' stack') by congruence.
      destruct (hyperEvalCode_injective _ _ _ _ _ _ _ _ Hcode)
        as [_ [Hrank _]].
      discriminate Hrank.
    + destruct Hzero as (rank' & base' & stack' & Hsource & Htarget).
      assert (Hcode : hyperEvalCode base (S rank) 0 stack =
          hyperEvalCode base' (S rank') 0 stack') by congruence.
      destruct (hyperEvalCode_injective _ _ _ _ _ _ _ _ Hcode)
        as [Hbase [Hrank [_ Hstack]]].
      injection Hrank as Hrank.
      subst base'; subst rank'; subst stack'; exact Htarget.
    + destruct Hsucc as (rank' & base' & argument' & stack' & Hsource & _).
      assert (Hcode : hyperEvalCode base (S rank) 0 stack =
          hyperEvalCode base' (S rank') (S argument') stack') by congruence.
      destruct (hyperEvalCode_injective _ _ _ _ _ _ _ _ Hcode)
        as [_ [_ [Hargument _]]].
      discriminate Hargument.
    + destruct Hreturn as (rank' & base' & value' & stack' & Hsource & _).
      exfalso; eapply (hyperEvalCode_ne_returnCode
        base (S rank) 0 stack base' value' (hyperStackCons rank' stack')).
      congruence.
  - intro Htarget; right; left; exists rank, base, stack; auto.
Qed.

Lemma HyperStep_eval_succ_succ : forall rank base argument stack target,
  HyperStep (hyperEvalCode base (S rank) (S argument) stack) target <->
  target = hyperEvalCode base (S rank) argument
    (hyperStackCons rank stack).
Proof.
  intros rank base argument stack target; split.
  - intros [Hpower | [Hzero | [Hsucc | Hreturn]]].
    + destruct Hpower as (base' & argument' & stack' & Hsource & _).
      assert (Hcode : hyperEvalCode base (S rank) (S argument) stack =
          hyperEvalCode base' 0 argument' stack') by congruence.
      destruct (hyperEvalCode_injective _ _ _ _ _ _ _ _ Hcode)
        as [_ [Hrank _]].
      discriminate Hrank.
    + destruct Hzero as (rank' & base' & stack' & Hsource & _).
      assert (Hcode : hyperEvalCode base (S rank) (S argument) stack =
          hyperEvalCode base' (S rank') 0 stack') by congruence.
      destruct (hyperEvalCode_injective _ _ _ _ _ _ _ _ Hcode)
        as [_ [_ [Hargument _]]].
      discriminate Hargument.
    + destruct Hsucc as (rank' & base' & argument' & stack' & Hsource & Htarget).
      assert (Hcode : hyperEvalCode base (S rank) (S argument) stack =
          hyperEvalCode base' (S rank') (S argument') stack') by congruence.
      destruct (hyperEvalCode_injective _ _ _ _ _ _ _ _ Hcode)
        as [Hbase [Hrank [Hargument Hstack]]].
      injection Hrank as Hrank; injection Hargument as Hargument.
      subst base'; subst rank'; subst argument'; subst stack'; exact Htarget.
    + destruct Hreturn as (rank' & base' & value' & stack' & Hsource & _).
      exfalso; eapply (hyperEvalCode_ne_returnCode
        base (S rank) (S argument) stack base' value'
        (hyperStackCons rank' stack')).
      congruence.
  - intro Htarget; right; right; left.
    exists rank, base, argument, stack; auto.
Qed.

Lemma HyperStep_from_return : forall base value stack target,
  HyperStep (hyperReturnCode base value stack) target <->
  exists rank tail,
    stack = hyperStackCons rank tail /\
    target = hyperEvalCode base rank value tail.
Proof.
  intros base value stack target; split.
  - intros [Hpower | [Hzero | [Hsucc | Hreturn]]].
    + destruct Hpower as (base' & argument' & stack' & Hsource & _).
      exfalso; eapply (hyperEvalCode_ne_returnCode
        base' 0 argument' stack' base value stack); congruence.
    + destruct Hzero as (rank' & base' & stack' & Hsource & _).
      exfalso; eapply (hyperEvalCode_ne_returnCode
        base' (S rank') 0 stack' base value stack); congruence.
    + destruct Hsucc as (rank' & base' & argument' & stack' & Hsource & _).
      exfalso; eapply (hyperEvalCode_ne_returnCode
        base' (S rank') (S argument') stack' base value stack); congruence.
    + destruct Hreturn as (rank' & base' & value' & stack' & Hsource & Htarget).
      assert (Hcode : hyperReturnCode base value stack =
          hyperReturnCode base' value' (hyperStackCons rank' stack'))
        by congruence.
      destruct (hyperReturnCode_injective _ _ _ _ _ _ Hcode)
        as [Hbase [Hvalue Hstack]].
      subst base'; subst value'; subst stack.
      exists rank', stack'; auto.
  - intros (rank & tail & Hstack & Htarget).
    right; right; right; exists rank, base, value, tail; subst stack; auto.
Qed.

Lemma HyperStep_return_cons : forall rank base value stack target,
  HyperStep (hyperReturnCode base value (hyperStackCons rank stack)) target <->
  target = hyperEvalCode base rank value stack.
Proof.
  intros rank base value stack target.
  rewrite HyperStep_from_return; split.
  - intros (rank' & tail & Hstack & Htarget).
    destruct (hyperStackCons_injective _ _ _ _ Hstack) as [Hrank Htail].
    subst rank'; subst tail; exact Htarget.
  - intro Htarget; exists rank, stack; auto.
Qed.

Lemma hyperReturnCode_empty_terminal : forall base value target,
  ~ HyperStep (hyperReturnCode base value 0) target.
Proof.
  intros base value target Hstep.
  apply HyperStep_from_return in Hstep.
  destruct Hstep as (rank & stack & Hstack & _).
  eapply hyperStackCons_ne_zero; symmetry; exact Hstack.
Qed.

Lemma HyperStep_deterministic : forall source left right,
  HyperStep source left -> HyperStep source right -> left = right.
Proof.
  intros source left right Hleft Hright.
  destruct Hleft as [Hpower | [Hzero | [Hsucc | Hreturn]]].
  - destruct Hpower as (base & argument & stack & Hsource & Htarget).
    subst source left.
    symmetry; exact (proj1
      (HyperStep_eval_rank_zero base argument stack right) Hright).
  - destruct Hzero as (rank & base & stack & Hsource & Htarget).
    subst source left.
    symmetry; exact (proj1
      (HyperStep_eval_succ_zero rank base stack right) Hright).
  - destruct Hsucc as (rank & base & argument & stack & Hsource & Htarget).
    subst source left.
    symmetry; exact (proj1
      (HyperStep_eval_succ_succ rank base argument stack right) Hright).
  - destruct Hreturn as (rank & base & value & stack & Hsource & Htarget).
    subst source left.
    symmetry; exact (proj1
      (HyperStep_return_cons rank base value stack right) Hright).
Qed.

(** The step relation itself is Diophantine.  Replacing [Nat.pow] with the
    library's scalar-iteration presentation is the only semantic conversion;
    all remaining terms are polynomial. *)
Theorem HyperStep_dio_rel :
  dio_rel (fun nu => HyperStep (nu 1) (nu 0)).
Proof.
  apply dio_rel_equiv with
      (R := fun nu =>
        (exists base argument stack,
            nu 1 = hyperEvalCode base 0 argument stack /\
            nu 0 = hyperReturnCode base (mscal mult 1 argument base) stack) \/
        (exists rank base stack,
            nu 1 = hyperEvalCode base (S rank) 0 stack /\
            nu 0 = hyperReturnCode base 1 stack) \/
        (exists rank base argument stack,
            nu 1 = hyperEvalCode base (S rank) (S argument) stack /\
            nu 0 = hyperEvalCode base (S rank) argument
              (hyperStackCons rank stack)) \/
        (exists rank base value stack,
            nu 1 = hyperReturnCode base value (hyperStackCons rank stack) /\
            nu 0 = hyperEvalCode base rank value stack)).
  - intro nu; unfold HyperStep; split.
    + intros [Hpower | [Hzero | [Hsucc | Hreturn]]].
      * destruct Hpower as (base & argument & stack & Hsource & Htarget).
        left; exists base, argument, stack; split; [exact Hsource |].
        now rewrite <- nat_pow_eq_mscal.
      * right; left; exact Hzero.
      * right; right; left; exact Hsucc.
      * right; right; right; exact Hreturn.
    + intros [Hpower | [Hzero | [Hsucc | Hreturn]]].
      * destruct Hpower as (base & argument & stack & Hsource & Htarget).
        left; exists base, argument, stack; split; [exact Hsource |].
        now rewrite nat_pow_eq_mscal.
      * right; left; exact Hzero.
      * right; right; left; exact Hsucc.
      * right; right; right; exact Hreturn.
  - dio auto.
Defined.

(** Concatenation of two exact runs. *)
Lemma rel_iter_trans : forall (R : nat -> nat -> Prop) firstSteps secondSteps
    source middle target,
  rel_iter R firstSteps source middle ->
  rel_iter R secondSteps middle target ->
  rel_iter R (firstSteps + secondSteps) source target.
Proof.
  intros R firstSteps secondSteps source middle target Hfirst Hsecond.
  apply rel_iter_plus; exists middle; auto.
Qed.

(** Any two terminating runs of a deterministic relation from the same state
    have the same terminal state, even when their lengths differ. *)
Lemma rel_iter_terminal_unique : forall (R : nat -> nat -> Prop),
  (forall source left right, R source left -> R source right -> left = right) ->
  forall leftSteps rightSteps source left right,
    (forall target, ~ R left target) ->
    (forall target, ~ R right target) ->
    rel_iter R leftSteps source left ->
    rel_iter R rightSteps source right ->
    left = right.
Proof.
  intros R Hdet leftSteps.
  induction leftSteps as [|leftSteps IH];
    intros rightSteps source left right HleftTerminal HrightTerminal
      Hleft Hright.
  - cbn [rel_iter] in Hleft; subst left.
    destruct rightSteps as [|rightSteps].
    + cbn [rel_iter] in Hright; exact Hright.
    + cbn [rel_iter] in Hright.
      destruct Hright as (next & Hstep & _).
      exfalso; exact (HleftTerminal next Hstep).
  - cbn [rel_iter] in Hleft.
    destruct Hleft as (leftNext & HleftStep & HleftRest).
    destruct rightSteps as [|rightSteps].
    + cbn [rel_iter] in Hright; subst right.
      exfalso; exact (HrightTerminal leftNext HleftStep).
    + cbn [rel_iter] in Hright.
      destruct Hright as (rightNext & HrightStep & HrightRest).
      assert (Hnext : leftNext = rightNext) by
        (eapply Hdet; eassumption).
      subst rightNext.
      eapply IH; eassumption.
Qed.

(** Evaluation always reaches the correct return state and preserves the
    caller's pending stack.  The nested induction follows the two recursive
    calls in the definition of a positive-rank hyperoperation. *)
Lemma hyperoperationCore_rel_iter : forall rank base argument stack,
  exists steps,
    rel_iter HyperStep steps
      (hyperEvalCode base rank argument stack)
      (hyperReturnCode base (hyperoperationCore rank base argument) stack).
Proof.
  induction rank as [|rank IHrank]; intros base argument stack.
  - exists 1; apply rel_iter_1.
    left; exists base, argument, stack; auto.
  - induction argument as [|argument IHargument] in stack |- *.
    + exists 1; apply rel_iter_1.
      right; left; exists rank, base, stack; auto.
    + destruct (IHargument (hyperStackCons rank stack))
        as [firstSteps Hfirst].
      destruct (IHrank base
        (hyperoperationCore (S rank) base argument) stack)
        as [lastSteps Hlast].
      assert (Hpush : rel_iter HyperStep 1
          (hyperEvalCode base (S rank) (S argument) stack)
          (hyperEvalCode base (S rank) argument
            (hyperStackCons rank stack))).
      { apply rel_iter_1; right; right; left.
        exists rank, base, argument, stack; auto. }
      assert (Hpop : rel_iter HyperStep 1
          (hyperReturnCode base
            (hyperoperationCore (S rank) base argument)
            (hyperStackCons rank stack))
          (hyperEvalCode base rank
            (hyperoperationCore (S rank) base argument) stack)).
      { apply rel_iter_1; right; right; right.
        exists rank, base,
          (hyperoperationCore (S rank) base argument), stack; auto. }
      assert (HpushFirst : rel_iter HyperStep (1 + firstSteps)
          (hyperEvalCode base (S rank) (S argument) stack)
          (hyperReturnCode base
            (hyperoperationCore (S rank) base argument)
            (hyperStackCons rank stack))).
      { eapply rel_iter_trans; [exact Hpush | exact Hfirst]. }
      assert (HthroughPop : rel_iter HyperStep ((1 + firstSteps) + 1)
          (hyperEvalCode base (S rank) (S argument) stack)
          (hyperEvalCode base rank
            (hyperoperationCore (S rank) base argument) stack)).
      { eapply rel_iter_trans; [exact HpushFirst | exact Hpop]. }
      exists (((1 + firstSteps) + 1) + lastSteps).
      eapply rel_iter_trans; [exact HthroughPop |].
      cbn [hyperoperationCore iterateFromOne].
      exact Hlast.
Qed.

(** Correctness and completeness of arbitrary terminating reachability. *)
Lemma hyperoperationCore_rel_iter_iff : forall result rank base argument,
  result = hyperoperationCore rank base argument <->
  exists steps,
    rel_iter HyperStep steps
      (hyperEvalCode base rank argument 0)
      (hyperReturnCode base result 0).
Proof.
  intros result rank base argument; split.
  - intro Hresult; subst result.
    apply hyperoperationCore_rel_iter.
  - intros (resultSteps & Hresult).
    destruct (hyperoperationCore_rel_iter rank base argument 0)
      as (correctSteps & Hcorrect).
    assert (Hcodes :
        hyperReturnCode base (hyperoperationCore rank base argument) 0 =
        hyperReturnCode base result 0).
    { eapply rel_iter_terminal_unique with
          (R := HyperStep)
          (leftSteps := correctSteps) (rightSteps := resultSteps)
          (source := hyperEvalCode base rank argument 0).
      - exact HyperStep_deterministic.
      - apply hyperReturnCode_empty_terminal.
      - apply hyperReturnCode_empty_terminal.
      - exact Hcorrect.
      - exact Hresult. }
    destruct (hyperReturnCode_injective _ _ _ _ _ _ Hcodes)
      as [_ [Hvalue _]].
    symmetry; exact Hvalue.
Qed.

(** Result-first infinite-valuation graph for the uniform hierarchy. *)
Theorem HyperoperationCore_dio_rel :
  dio_rel (fun nu =>
    nu 0 = hyperoperationCore (nu 1) (nu 2) (nu 3)).
Proof.
  apply dio_rel_equiv with
      (R := fun nu => exists steps,
        rel_iter HyperStep steps
          (hyperEvalCode (nu 2) (nu 1) (nu 3) 0)
          (hyperReturnCode (nu 2) (nu 0) 0)).
  - intro nu; apply hyperoperationCore_rel_iter_iff.
  - eapply dio_rel_rt.
    + exact HyperStep_dio_rel.
    + dio auto.
    + dio auto.
Defined.

(** Arithmetic case split matching the conventional public ranks. *)
Definition HyperoperatorCases (result rank base argument : nat) : Prop :=
  (rank = 0 /\ result = S argument) \/
  (rank = 1 /\ result = base + argument) \/
  (rank = 2 /\ result = base * argument) \/
  exists coreRank,
    rank = coreRank + 3 /\
    result = hyperoperationCore coreRank base argument.

Lemma hyperoperator_cases_iff : forall result rank base argument,
  result = hyperoperator rank base argument <->
  HyperoperatorCases result rank base argument.
Proof.
  intros result rank base argument.
  destruct rank as [|rank].
  - cbn [hyperoperator HyperoperatorCases].
    split; intro H.
    + left; auto.
    + destruct H as [[_ Hresult] | [[Hfalse _] | [[Hfalse _] | Hhigh]]].
      * exact Hresult.
      * discriminate Hfalse.
      * discriminate Hfalse.
      * destruct Hhigh as (rank' & Hrank & _); lia.
  - destruct rank as [|rank].
    + cbn [hyperoperator HyperoperatorCases].
      split; intro H.
      * right; left; auto.
      * destruct H as [[Hfalse _] | [[_ Hresult] | [[Hfalse _] | Hhigh]]].
        -- discriminate Hfalse.
        -- exact Hresult.
        -- discriminate Hfalse.
        -- destruct Hhigh as (rank' & Hrank & _); lia.
    + destruct rank as [|coreRank].
      * cbn [hyperoperator HyperoperatorCases].
        split; intro H.
        -- right; right; left; auto.
        -- destruct H as [[Hfalse _] | [[Hfalse _] | [[_ Hresult] | Hhigh]]].
           ++ discriminate Hfalse.
           ++ discriminate Hfalse.
           ++ exact Hresult.
           ++ destruct Hhigh as (rank' & Hrank & _); lia.
      * cbn [hyperoperator HyperoperatorCases].
        split; intro H.
        -- right; right; right; exists coreRank; split; [lia | exact H].
        -- destruct H as [[Hfalse _] | [[Hfalse _] | [[Hfalse _] | Hhigh]]].
           ++ discriminate Hfalse.
           ++ discriminate Hfalse.
           ++ discriminate Hfalse.
           ++ destruct Hhigh as (rank' & Hrank & Hresult).
              assert (rank' = coreRank) by lia.
              subst rank'; exact Hresult.
Qed.

(** A renaming of the uniform graph used under the existential high-rank
    witness.  In the extended valuation, coordinates 1,0,3,4 are result,
    core rank, base, and argument respectively. *)
Definition highCoreRenaming (n : nat) : nat :=
  match n with
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | _ => 4
  end.

Lemma HighCoreBody_dio_rel :
  dio_rel (fun nu =>
    nu 1 = hyperoperationCore (nu 0) (nu 3) (nu 4)).
Proof.
  change (dio_rel (fun nu =>
    (fun n => nu (highCoreRenaming n)) 0 =
      hyperoperationCore
        ((fun n => nu (highCoreRenaming n)) 1)
        ((fun n => nu (highCoreRenaming n)) 2)
        ((fun n => nu (highCoreRenaming n)) 3))).
  exact (@dio_rel_ren
    (fun nu => nu 0 = hyperoperationCore (nu 1) (nu 2) (nu 3))
    highCoreRenaming HyperoperationCore_dio_rel).
Defined.

(** Result-first graph of the conventional rank-numbered hyperoperator. *)
Theorem Hyperoperator_dio_rel :
  dio_rel (fun nu => nu 0 = hyperoperator (nu 1) (nu 2) (nu 3)).
Proof.
  apply dio_rel_equiv with
      (R := fun nu => HyperoperatorCases (nu 0) (nu 1) (nu 2) (nu 3)).
  - intro nu; apply hyperoperator_cases_iff.
  - unfold HyperoperatorCases.
    apply dio_rel_disj; [dio auto |].
    apply dio_rel_disj; [dio auto |].
    apply dio_rel_disj; [dio auto |].
    apply dio_rel_exst.
    apply dio_rel_conj.
    + dio auto.
    + exact HighCoreBody_dio_rel.
Defined.

(** Inspectable formula and single-polynomial witnesses. *)
Definition hyperoperatorDiophantineFormula : dio_formula :=
  proj1_sig Hyperoperator_dio_rel.

Theorem hyperoperatorDiophantineFormula_spec : forall nu,
  df_pred hyperoperatorDiophantineFormula nu <->
  nu 0 = hyperoperator (nu 1) (nu 2) (nu 3).
Proof. exact (proj2_sig Hyperoperator_dio_rel). Qed.

Definition hyperoperatorDiophantineEquation :
  { E : dio_single nat nat |
    forall nu,
      nu 0 = hyperoperator (nu 1) (nu 2) (nu 3) <->
      dio_single_pred E nu } :=
  dio_rel_single Hyperoperator_dio_rel.

(** Official four-parameter H10 graph, ordered result, rank, base, argument. *)
Definition HyperoperatorVector (v : Vector.t nat 4) : Prop :=
  Vector.nth v Fin.F1 =
  hyperoperator
    (Vector.nth v (Fin.FS Fin.F1))
    (Vector.nth v (Fin.FS (Fin.FS Fin.F1)))
    (Vector.nth v (Fin.FS (Fin.FS (Fin.FS Fin.F1)))).

Theorem Hyperoperator_Diophantine :
  Diophantine HyperoperatorVector.
Proof.
  unfold HyperoperatorVector.
  change (Diophantine
    (fun v : Vector.t nat 4 =>
      finiteEnv v 0 =
      hyperoperator (finiteEnv v 1) (finiteEnv v 2) (finiteEnv v 3))).
  apply (@dio_rel_Diophantine 4
    (fun nu => nu 0 = hyperoperator (nu 1) (nu 2) (nu 3))).
  exact Hyperoperator_dio_rel.
Qed.

End PAListHyperoperationDiophantine.
