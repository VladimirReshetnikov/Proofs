(** Canonical genuine/default rows selected by the total program decoder. *)

From Stdlib Require Import List Arith Lia Bool Classical
  Logic.FunctionalExtensionality.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import HierarchyReduction
  FiniteSkolemHull CanonicalSelector CanonicalSelectorPA
  SkolemProgramCode FiniteBetaCoding ProgramTrace TotalProgramRows
  EvaluatorCutContract StandardTraceRows.

Import ListNotations.
Import PAHierarchyReduction.
Import PAFiniteSkolemHull.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PASkolemProgramCode.
Import PAFiniteBetaCoding.
Import PAProgramTrace.
Import PATotalProgramRows.
Import PAEvaluatorCutContract.
Import PAStandardTraceRows.

Module PACanonicalTotalRows.

(** Exact external shape of every non-default scheduled instruction. *)
Definition ScheduledCodeShape (target : nat) : Prop :=
  match scheduleSkolemCode target with
  | siSeed => target = polynomialNode tagSeed 0
  | siZero => True
  | siSucc child => target = polynomialNode tagSucc child
  | siAdd lhs rhs =>
      target = polynomialNode tagAdd (polynomialPair lhs rhs)
  | siMul lhs rhs =>
      target = polynomialNode tagMul (polynomialPair lhs rhs)
  | siChoose formulaIndex argsCode =>
      target = polynomialNode tagChoose
        (polynomialPair formulaIndex argsCode)
  | siArgsNil => target = polynomialNode tagArgsNil 0
  | siArgsCons child rest =>
      target = polynomialNode tagArgsCons (polynomialPair child rest)
  end.

Lemma scheduleSkolemCode_shape : forall target,
  ScheduledCodeShape target.
Proof.
  intro target. unfold ScheduledCodeShape, scheduleSkolemCode.
  destruct (polynomialUnnode target) as [[tag payload] |] eqn:hnode;
    [| exact I].
  pose proof (polynomialUnnode_sound target tag payload hnode) as hshape.
  destruct tag as [|[|[|[|[|[|[|[|tag]]]]]]]]; simpl.
  - destruct (payload =? 0) eqn:hzero; [|exact I].
    apply Nat.eqb_eq in hzero. subst payload. symmetry. exact hshape.
  - exact I.
  - symmetry. exact hshape.
  - destruct (polynomialSplit payload) as [[left right] |] eqn:hsplit;
      [|exact I].
    pose proof (polynomialSplit_sound payload left right hsplit) as hpayload.
    rewrite <- hpayload in hshape. symmetry. exact hshape.
  - destruct (polynomialSplit payload) as [[left right] |] eqn:hsplit;
      [|exact I].
    pose proof (polynomialSplit_sound payload left right hsplit) as hpayload.
    rewrite <- hpayload in hshape. symmetry. exact hshape.
  - destruct (polynomialSplit payload) as [[index args] |] eqn:hsplit;
      [|exact I].
    pose proof (polynomialSplit_sound payload index args hsplit) as hpayload.
    rewrite <- hpayload in hshape. symmetry. exact hshape.
  - destruct (payload =? 0) eqn:hzero; [|exact I].
    apply Nat.eqb_eq in hzero. subst payload. symmetry. exact hshape.
  - destruct (polynomialSplit payload) as [[child rest] |] eqn:hsplit;
      [|exact I].
    pose proof (polynomialSplit_sound payload child rest hsplit) as hpayload.
    rewrite <- hpayload in hshape. symmetry. exact hshape.
  - exact I.
Qed.

Lemma decodeFixedArgsFuel_sound : forall fuel width code codes,
  decodeFixedArgsFuel fuel width code = Some codes ->
  argsCodeOfCodes codes = code.
Proof.
  intros fuel width. revert fuel.
  induction width as [|width IH]; intros fuel code codes hdecode.
  - destruct fuel as [|fuel];
      change
        ((match scheduleSkolemCode code with
          | siArgsNil => Some []
          | _ => None
          end) = Some codes) in hdecode;
      destruct (scheduleSkolemCode code)
        as [| |child|lhs rhs|lhs rhs|index args| |child rest]
        eqn:hschedule; simpl in hdecode; try (discriminate hdecode).
    all: inversion hdecode; subst.
    all: pose proof (scheduleSkolemCode_shape code) as hshape.
    all: unfold ScheduledCodeShape in hshape; rewrite hschedule in hshape.
    all: simpl; symmetry; exact hshape.
  - destruct fuel as [|fuel]; [discriminate |].
    change
      ((match scheduleSkolemCode code with
        | siArgsCons child rest =>
            match decodeFixedArgsFuel fuel width rest with
            | Some children => Some (child :: children)
            | None => None
            end
        | _ => None
        end) = Some codes) in hdecode.
    destruct (scheduleSkolemCode code)
      as [| |child|lhs rhs|lhs rhs|index args| |child rest]
      eqn:hschedule; simpl in hdecode; try (discriminate hdecode).
    destruct (decodeFixedArgsFuel fuel width rest)
      as [children |] eqn:hrest; simpl in hdecode;
      try (discriminate hdecode).
    inversion hdecode; subst.
    pose proof (scheduleSkolemCode_shape code) as hshape.
    unfold ScheduledCodeShape in hshape. rewrite hschedule in hshape.
    cbn [argsCodeOfCodes]. rewrite (IH fuel rest children hrest).
    symmetry. exact hshape.
Qed.

Corollary decodeFixedArgs_sound : forall width code codes,
  decodeFixedArgs width code = Some codes ->
  argsCodeOfCodes codes = code.
Proof.
  intros width code codes hdecode.
  exact (decodeFixedArgsFuel_sound (S code) width code codes hdecode).
Qed.

Lemma standardCodeList_nth : forall codes,
  standardCodeList 0 (length codes) (fun i => nth i codes 0) = codes.
Proof.
  induction codes as [|head rest IH]; [reflexivity |].
  unfold standardCodeList in *.
  simpl. rewrite <- (seq_shift (length rest) 0), map_map. simpl.
  now rewrite IH.
Qed.

Lemma rowArgsFromCodes_length : forall target previous codes,
  skolemProgramArgsLength (rowArgsFromCodes target previous codes) =
    length codes.
Proof.
  intros target previous codes. induction codes; simpl; congruence.
Qed.

Lemma skolemHullProgramArgsEnv_out_of_range : forall
    (M : RawPAModel) seed rank selector args i,
  skolemProgramArgsLength args <= i ->
  skolemHullProgramArgsEnv M seed rank selector args i =
    raw_zero (skolemHullRawModel M seed rank selector).
Proof.
  intros M seed rank selector args.
  induction args as [|p rest IH]; intros [|i] hi; simpl in *.
  - apply skolemHullProgramValue_zero.
  - apply skolemHullProgramValue_zero.
  - lia.
  - apply IH. lia.
Qed.

Lemma rowArgsFromCodes_env_nth : forall
    (M : RawPAModel) seed rank target codes i,
  i < length codes ->
  (forall child, In child codes -> child < target) ->
  skolemHullProgramArgsEnv M seed rank (rawCanonicalSelector M)
    (rowArgsFromCodes target
      (fun child _ => totalRowProgram rank child) codes) i =
  skolemHullProgramValue M seed rank (rawCanonicalSelector M)
    (totalRowProgram rank (nth i codes 0)).
Proof.
  intros M seed rank target codes.
  induction codes as [|head rest IH]; intros [|i] hi hchildren;
    simpl in *; try lia.
  - unfold belowProgram.
    destruct (lt_dec head target) as [hlt | hnlt].
    + reflexivity.
    + exfalso. apply hnlt. apply hchildren. now left.
  - apply IH; [lia |].
    intros child hin. apply hchildren. now right.
Qed.

Lemma boundedEnv_rowArgsFromCodes : forall
    (M : RawPAModel) seed rank target codes,
  length codes = rank ->
  (forall child, In child codes -> child < target) ->
  boundedEnv
    (skolemHullRawModel M seed rank (rawCanonicalSelector M)) rank
    (fun i => skolemHullProgramValue M seed rank
      (rawCanonicalSelector M) (totalRowProgram rank (nth i codes 0))) =
  skolemHullProgramArgsEnv M seed rank (rawCanonicalSelector M)
    (rowArgsFromCodes target
      (fun child _ => totalRowProgram rank child) codes).
Proof.
  intros M seed rank target codes hlength hchildren.
  apply functional_extensionality. intro i.
  unfold boundedEnv. destruct (i <? rank) eqn:hi.
  - apply Nat.ltb_lt in hi.
    symmetry. apply rowArgsFromCodes_env_nth; [lia | exact hchildren].
  - apply Nat.ltb_ge in hi.
    symmetry. apply skolemHullProgramArgsEnv_out_of_range.
    rewrite rowArgsFromCodes_length, hlength. exact hi.
Qed.

(** At every standard code, the total decoder either has a canonical genuine
    row descriptor or denotes zero. *)
Theorem canonicalStandardRowWitness_or_zero : forall
    (M : RawPAModel) seed rank,
  RawPASatisfies M ->
  formula_rank hullLtFormula <= rank ->
  forall betaCode betaStep target,
  (forall child, child < target ->
    RawBetaEntry
      (skolemHullRawModel M seed rank (rawCanonicalSelector M))
      (skolemHullProgramValue M seed rank (rawCanonicalSelector M)
        (totalRowProgram rank child))
      betaCode betaStep
      (rawNumeralValue
        (skolemHullRawModel M seed rank (rawCanonicalSelector M)) child)) ->
  StandardRowWitness
    (skolemHullRawModel M seed rank (rawCanonicalSelector M))
    rank target betaCode betaStep
    (skolemHullSeed M seed rank (rawCanonicalSelector M))
    (skolemHullProgramValue M seed rank (rawCanonicalSelector M)
      (totalRowProgram rank target)) \/
  totalRowProgram rank target = spZero.
Proof.
  intros M seed rank hPA hLtRank betaCode betaStep target htable.
  set (K := skolemHullRawModel M seed rank (rawCanonicalSelector M)).
  remember (scheduleSkolemCode target) as instruction eqn:hschedule.
  symmetry in hschedule.
  destruct instruction as
    [| |child|lhs rhs|lhs rhs|formulaIndex argsCode| |child rest].
  - left.
    pose proof (scheduleSkolemCode_shape target) as hshape.
    unfold ScheduledCodeShape in hshape. rewrite hschedule in hshape.
    apply standardRowSeed.
    + exact hshape.
    + rewrite (totalRowProgram_of_seed rank target hschedule).
      apply skolemHullProgramValue_seed.
  - right. apply totalRowProgram_of_zero. exact hschedule.
  - left.
    pose proof (scheduleSkolemCode_shape target) as hshape.
    unfold ScheduledCodeShape in hshape. rewrite hschedule in hshape.
    apply standardRowSucc with
      (childCode := child)
      (childValue := skolemHullProgramValue M seed rank
        (rawCanonicalSelector M) (totalRowProgram rank child)).
    + exact hshape.
    + apply htable.
      apply (scheduled_children_smaller target child).
      rewrite hschedule. now left.
    + rewrite (totalRowProgram_of_succ rank target child hschedule).
      * apply skolemHullProgramValue_succ.
      * apply (scheduled_children_smaller target child).
        rewrite hschedule. now left.
  - left.
    pose proof (scheduleSkolemCode_shape target) as hshape.
    unfold ScheduledCodeShape in hshape. rewrite hschedule in hshape.
    apply standardRowAdd with
      (leftCode := lhs) (rightCode := rhs)
      (leftValue := skolemHullProgramValue M seed rank
        (rawCanonicalSelector M) (totalRowProgram rank lhs))
      (rightValue := skolemHullProgramValue M seed rank
        (rawCanonicalSelector M) (totalRowProgram rank rhs)).
    + exact hshape.
    + apply htable. apply (scheduled_children_smaller target lhs).
      rewrite hschedule. now left.
    + apply htable. apply (scheduled_children_smaller target rhs).
      rewrite hschedule. now right; left.
    + rewrite (totalRowProgram_of_add rank target lhs rhs hschedule).
      * apply skolemHullProgramValue_add.
      * apply (scheduled_children_smaller target lhs).
        rewrite hschedule. now left.
      * apply (scheduled_children_smaller target rhs).
        rewrite hschedule. now right; left.
  - left.
    pose proof (scheduleSkolemCode_shape target) as hshape.
    unfold ScheduledCodeShape in hshape. rewrite hschedule in hshape.
    apply standardRowMul with
      (leftCode := lhs) (rightCode := rhs)
      (leftValue := skolemHullProgramValue M seed rank
        (rawCanonicalSelector M) (totalRowProgram rank lhs))
      (rightValue := skolemHullProgramValue M seed rank
        (rawCanonicalSelector M) (totalRowProgram rank rhs)).
    + exact hshape.
    + apply htable. apply (scheduled_children_smaller target lhs).
      rewrite hschedule. now left.
    + apply htable. apply (scheduled_children_smaller target rhs).
      rewrite hschedule. now right; left.
    + rewrite (totalRowProgram_of_mul rank target lhs rhs hschedule).
      * apply skolemHullProgramValue_mul.
      * apply (scheduled_children_smaller target lhs).
        rewrite hschedule. now left.
      * apply (scheduled_children_smaller target rhs).
        rewrite hschedule. now right; left.
  - destruct (lt_dec formulaIndex (length (formula_rank_enum rank)))
      as [hindex | hindex].
    + destruct (decodeFixedArgs rank argsCode) as [childCodes |]
        eqn:hdecode.
      * left.
        pose proof (scheduleSkolemCode_shape target) as hshape.
        unfold ScheduledCodeShape in hshape. rewrite hschedule in hshape.
        pose proof (decodeFixedArgs_length rank argsCode childCodes hdecode)
          as hlength.
        pose proof (decoded_choose_children_smaller target formulaIndex
          argsCode rank childCodes hschedule hdecode) as hchildren.
        set (codes := fun i => nth i childCodes 0).
        set (args := rowArgsFromCodes target
          (fun child _ => totalRowProgram rank child) childCodes).
        set (values := fun i => skolemHullProgramValue M seed rank
          (rawCanonicalSelector M) (totalRowProgram rank (codes i))).
        apply standardRowChoose with
          (formulaIndex := formulaIndex) (codes := codes) (values := values).
        -- exact hindex.
        -- rewrite hshape.
           rewrite <- (decodeFixedArgs_sound rank argsCode childCodes hdecode).
           unfold codes. rewrite <- hlength.
           rewrite (standardCodeList_nth childCodes). reflexivity.
        -- intros i hi. unfold values, codes.
           apply htable.
           apply hchildren.
           apply nth_In. lia.
        -- assert (hrow : totalRowProgram rank target =
             spChoose formulaIndex args).
           {
             unfold args.
             apply totalRowProgram_of_choose with
               (argsCode := argsCode) (childCodes := childCodes);
               assumption.
           }
           rewrite hrow.
           pose proof (skolemHullProgramValue_choose_graph
             M seed rank hPA hLtRank formulaIndex args
             (selectorBody_rank_of_index rank formulaIndex hindex)) as hgraph.
           unfold values, codes, args.
           rewrite (boundedEnv_rowArgsFromCodes M seed rank target childCodes
             hlength hchildren).
           exact hgraph.
      * right. apply totalRowProgram_of_default_choose_args with
          (formulaIndex := formulaIndex) (argsCode := argsCode);
          [exact hschedule | exact hindex | exact hdecode].
    + right. apply totalRowProgram_of_default_choose_index with
        (formulaIndex := formulaIndex) (argsCode := argsCode).
      * exact hschedule.
      * lia.
  - right. apply totalRowProgram_of_args_instruction. now left.
  - right. apply totalRowProgram_of_args_instruction.
    right. exists child, rest. exact hschedule.
Qed.

End PACanonicalTotalRows.
