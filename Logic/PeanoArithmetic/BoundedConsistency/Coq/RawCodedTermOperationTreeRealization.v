(**
  Finite realization of a carrier-valued term-operation tree.

  Formula-operation equality rows delegate to a represented term operation.
  For a standard term surrounding a nonstandard replacement, the source and
  target syntax still form a finite metatheoretic tree even though one target
  leaf is an arbitrary model element.  This module beta-codes such trees in
  postorder.  The variable row is a parameter; zero, successor, addition, and
  multiplication are handled uniformly by the represented traversal.
*)

From Stdlib Require Import List Arith Lia.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedAssignment RawCodedFormulaOperations
  RawCodedFormulaOperationsStandardRealization.

Import ListNotations.

Module PABoundedRawCodedTermOperationTreeRealization.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaOperationsStandardRealization.

Inductive RawTermOperationBinaryKind : Type :=
| RTOBAdd
| RTOBMul.

Definition rawTermOperationBinaryCode (M : RawPAModel)
    (kind : RawTermOperationBinaryKind) (left right : M) : M :=
  match kind with
  | RTOBAdd => rawTermAddCode M left right
  | RTOBMul => rawTermMulCode M left right
  end.

(** A variable leaf stores its source variable index and its complete target
    code.  In particular, the target need not itself be a variable code. *)
Inductive RawTermOperationTree (M : RawPAModel) : Type :=
| RTOTVar : M -> M -> RawTermOperationTree M
| RTOTZero : RawTermOperationTree M
| RTOTSucc : RawTermOperationTree M -> RawTermOperationTree M
| RTOTBinary : RawTermOperationBinaryKind ->
    RawTermOperationTree M -> RawTermOperationTree M ->
    RawTermOperationTree M.

Arguments RTOTVar M sourceIndex target : clear implicits.
Arguments RTOTZero M : clear implicits.
Arguments RTOTSucc M child : clear implicits.
Arguments RTOTBinary M kind left right : clear implicits.

Fixpoint rawTermOperationTreeSource (M : RawPAModel)
    (tree : RawTermOperationTree M) : M :=
  match tree with
  | RTOTVar _ sourceIndex _ => rawTermVarCode M sourceIndex
  | RTOTZero _ => rawTermZeroCode M
  | RTOTSucc _ child =>
      rawTermSuccCode M (rawTermOperationTreeSource M child)
  | RTOTBinary _ kind leftTree rightTree =>
      rawTermOperationBinaryCode M kind
        (rawTermOperationTreeSource M leftTree)
        (rawTermOperationTreeSource M rightTree)
  end.

Fixpoint rawTermOperationTreeTarget (M : RawPAModel)
    (tree : RawTermOperationTree M) : M :=
  match tree with
  | RTOTVar _ _ target => target
  | RTOTZero _ => rawTermZeroCode M
  | RTOTSucc _ child =>
      rawTermSuccCode M (rawTermOperationTreeTarget M child)
  | RTOTBinary _ kind leftTree rightTree =>
      rawTermOperationBinaryCode M kind
        (rawTermOperationTreeTarget M leftTree)
        (rawTermOperationTreeTarget M rightTree)
  end.

Fixpoint RawTermOperationTreeValid (M : RawPAModel)
    (variableRow : M -> M -> Prop) (tree : RawTermOperationTree M) : Prop :=
  match tree with
  | RTOTVar _ sourceIndex target =>
      variableRow (rawTermVarCode M sourceIndex) target
  | RTOTZero _ => True
  | RTOTSucc _ child => RawTermOperationTreeValid M variableRow child
  | RTOTBinary _ _ leftTree rightTree =>
      RawTermOperationTreeValid M variableRow leftTree /\
      RawTermOperationTreeValid M variableRow rightTree
  end.

Arguments rawTermOperationTreeSource M tree : clear implicits.
Arguments rawTermOperationTreeTarget M tree : clear implicits.
Arguments RawTermOperationTreeValid M variableRow tree : clear implicits.

Fixpoint rawTermOperationTreeSchedule (M : RawPAModel)
    (tree : RawTermOperationTree M) : list (RawTermOperationTree M) :=
  match tree with
  | RTOTVar _ _ _ | RTOTZero _ => [tree]
  | RTOTSucc _ child => rawTermOperationTreeSchedule M child ++ [tree]
  | RTOTBinary _ _ leftTree rightTree =>
      rawTermOperationTreeSchedule M leftTree ++
      rawTermOperationTreeSchedule M rightTree ++ [tree]
  end.

Definition rawTermOperationTreeDefault (M : RawPAModel) :
    RawTermOperationTree M := RTOTZero M.

Definition rawTermOperationTreeSourceAt (M : RawPAModel)
    (schedule : list (RawTermOperationTree M)) (index : nat) : M :=
  rawTermOperationTreeSource M
    (nth index schedule (rawTermOperationTreeDefault M)).

Definition rawTermOperationTreeTargetAt (M : RawPAModel)
    (schedule : list (RawTermOperationTree M)) (index : nat) : M :=
  rawTermOperationTreeTarget M
    (nth index schedule (rawTermOperationTreeDefault M)).

Lemma rawTermOperationTreeSourceAt_nth_error : forall
    M schedule index occurrence,
  nth_error schedule index = Some occurrence ->
  rawTermOperationTreeSourceAt M schedule index =
    rawTermOperationTreeSource M occurrence.
Proof.
  intros M schedule index occurrence hnth.
  unfold rawTermOperationTreeSourceAt.
  now rewrite (nth_error_nth schedule index
    (rawTermOperationTreeDefault M) hnth).
Qed.

Lemma rawTermOperationTreeTargetAt_nth_error : forall
    M schedule index occurrence,
  nth_error schedule index = Some occurrence ->
  rawTermOperationTreeTargetAt M schedule index =
    rawTermOperationTreeTarget M occurrence.
Proof.
  intros M schedule index occurrence hnth.
  unfold rawTermOperationTreeTargetAt.
  now rewrite (nth_error_nth schedule index
    (rawTermOperationTreeDefault M) hnth).
Qed.

Lemma rawTermOperationTreeSchedule_nonempty : forall M tree,
  rawTermOperationTreeSchedule M tree <> [].
Proof.
  intros M tree. destruct tree; intro hempty;
    pose proof (f_equal (@length (RawTermOperationTree M)) hempty)
      as hlength;
    cbn [rawTermOperationTreeSchedule] in hlength;
    repeat rewrite length_app in hlength; cbn in hlength; lia.
Qed.

Lemma rawTermOperationTreeSchedule_length_positive : forall M tree,
  0 < length (rawTermOperationTreeSchedule M tree).
Proof.
  intros M tree.
  pose proof (rawTermOperationTreeSchedule_nonempty M tree).
  destruct (rawTermOperationTreeSchedule M tree); cbn;
    [contradiction | lia].
Qed.

Lemma rawTermOperationTreeSchedule_root : forall M tree,
  nth_error (rawTermOperationTreeSchedule M tree)
    (Nat.pred (length (rawTermOperationTreeSchedule M tree))) = Some tree.
Proof.
  intros M tree. destruct tree; cbn [rawTermOperationTreeSchedule].
  - reflexivity.
  - reflexivity.
  - rewrite length_app. cbn.
    replace (Nat.pred (length (rawTermOperationTreeSchedule M tree) + 1))
      with (length (rawTermOperationTreeSchedule M tree)) by lia.
    apply nth_error_snoc_last.
  - rewrite !length_app. cbn.
    replace
      (Nat.pred
        (length (rawTermOperationTreeSchedule M tree1) +
         (length (rawTermOperationTreeSchedule M tree2) + 1)))
      with
      (length (rawTermOperationTreeSchedule M tree1) +
       length (rawTermOperationTreeSchedule M tree2)) by lia.
    apply nth_error_binary_postorder_root.
Qed.

Definition RawTermOperationTreeSegmentLookup (M : RawPAModel)
    (sourceCode sourceStep targetCode targetStep : M)
    (schedule : list (RawTermOperationTree M)) (offset : nat) : Prop :=
  forall index occurrence,
    nth_error schedule index = Some occurrence ->
    RawCodedTermOperationPairLookup M
      sourceCode sourceStep targetCode targetStep
      (rawNumeralValue M (offset + index))
      (rawTermOperationTreeSource M occurrence)
      (rawTermOperationTreeTarget M occurrence).

Lemma raw_termOperationTree_segment_row : forall
    (M : RawPAModel), RawPASatisfies M -> forall variableRow tree,
  RawTermOperationTreeValid M variableRow tree ->
  forall sourceCode sourceStep targetCode targetStep offset,
  RawTermOperationTreeSegmentLookup M
    sourceCode sourceStep targetCode targetStep
    (rawTermOperationTreeSchedule M tree) offset ->
  forall index occurrence,
  nth_error (rawTermOperationTreeSchedule M tree) index = Some occurrence ->
  RawCodedTermOperationTraversalRow M variableRow
    sourceCode sourceStep targetCode targetStep
    (rawNumeralValue M (offset + index))
    (rawTermOperationTreeSource M occurrence)
    (rawTermOperationTreeTarget M occurrence).
Proof.
  intros M hPA variableRow tree. induction tree as
      [sourceIndex target | | child IHchild | kind left IHleft right IHright];
    intros hvalid sourceCode sourceStep targetCode targetStep offset
      hlookup index occurrence hnth.
  - destruct (nth_error_singleton_inv _ _ _ _ hnth) as [-> ->].
    cbn [RawTermOperationTreeValid rawTermOperationTreeSource
      rawTermOperationTreeTarget] in *.
    left. exact hvalid.
  - destruct (nth_error_singleton_inv _ _ _ _ hnth) as [-> ->].
    right. left. split; reflexivity.
  - cbn [rawTermOperationTreeSchedule] in hnth, hlookup.
    cbn [RawTermOperationTreeValid] in hvalid.
    unfold RawTermOperationTreeSegmentLookup in hlookup.
    destruct (nth_error_unary_postorder_cases _ _ _ _ _ hnth) as
      [[hchild hnthChild] | [-> ->]].
    + apply (IHchild hvalid sourceCode sourceStep targetCode targetStep
        offset).
      * intros local localOccurrence hlocal. apply hlookup.
        apply nth_error_embed_left with
          (right := [RTOTSucc M child]). exact hlocal.
      * exact hnthChild.
    + assert (hchildLookup : RawCodedTermOperationPairLookup M
          sourceCode sourceStep targetCode targetStep
          (rawNumeralValue M
            (offset + Nat.pred
              (length (rawTermOperationTreeSchedule M child))))
          (rawTermOperationTreeSource M child)
          (rawTermOperationTreeTarget M child)).
      {
        apply hlookup.
        apply nth_error_embed_left with (right := [RTOTSucc M child]).
        apply rawTermOperationTreeSchedule_root.
      }
      right. right. left.
      exists
        (rawNumeralValue M
          (offset + Nat.pred
            (length (rawTermOperationTreeSchedule M child)))),
        (rawTermOperationTreeSource M child),
        (rawTermOperationTreeTarget M child).
      split.
      * apply raw_lt_numeralValue_of_lt; [exact hPA |].
        pose proof (rawTermOperationTreeSchedule_length_positive M child).
        lia.
      * split; [exact hchildLookup |]. split; reflexivity.
  - cbn [rawTermOperationTreeSchedule] in hnth, hlookup.
    cbn [RawTermOperationTreeValid] in hvalid.
    destruct hvalid as [hleftValid hrightValid].
    unfold RawTermOperationTreeSegmentLookup in hlookup.
    destruct (nth_error_binary_postorder_cases _ _ _ _ _ _ hnth) as
      [[hleft hnthLeft] |
       [(rightIndex & -> & hright & hnthRight) | [-> ->]]].
    + apply (IHleft hleftValid sourceCode sourceStep targetCode targetStep
        offset).
      * intros local localOccurrence hlocal. apply hlookup.
        apply nth_error_embed_left with
          (right := rawTermOperationTreeSchedule M right ++
            [RTOTBinary M kind left right]). exact hlocal.
      * exact hnthLeft.
    + replace
        (rawNumeralValue M
          (offset +
            (length (rawTermOperationTreeSchedule M left) + rightIndex)))
        with
        (rawNumeralValue M
          ((offset + length (rawTermOperationTreeSchedule M left)) +
            rightIndex)) by (f_equal; lia).
      apply (IHright hrightValid sourceCode sourceStep targetCode targetStep
        (offset + length (rawTermOperationTreeSchedule M left))).
      * intros local localOccurrence hlocal.
        specialize (hlookup
          (length (rawTermOperationTreeSchedule M left) + local)
          localOccurrence).
        assert (hembed :
          nth_error
            (rawTermOperationTreeSchedule M left ++
             rawTermOperationTreeSchedule M right ++
             [RTOTBinary M kind left right])
            (length (rawTermOperationTreeSchedule M left) + local) =
          Some localOccurrence).
        {
          apply nth_error_embed_right.
          apply nth_error_embed_left with
            (right := [RTOTBinary M kind left right]). exact hlocal.
        }
        specialize (hlookup hembed).
        replace
          (offset +
            (length (rawTermOperationTreeSchedule M left) + local))
          with
          ((offset + length (rawTermOperationTreeSchedule M left)) + local)
          in hlookup by lia.
        exact hlookup.
      * exact hnthRight.
    + assert (hleftLookup : RawCodedTermOperationPairLookup M
          sourceCode sourceStep targetCode targetStep
          (rawNumeralValue M
            (offset + Nat.pred
              (length (rawTermOperationTreeSchedule M left))))
          (rawTermOperationTreeSource M left)
          (rawTermOperationTreeTarget M left)).
      {
        apply hlookup.
        apply nth_error_embed_left with
          (right := rawTermOperationTreeSchedule M right ++
            [RTOTBinary M kind left right]).
        apply rawTermOperationTreeSchedule_root.
      }
      assert (hrightLookup : RawCodedTermOperationPairLookup M
          sourceCode sourceStep targetCode targetStep
          (rawNumeralValue M
            (offset +
              (length (rawTermOperationTreeSchedule M left) +
               Nat.pred (length (rawTermOperationTreeSchedule M right)))))
          (rawTermOperationTreeSource M right)
          (rawTermOperationTreeTarget M right)).
      {
        apply hlookup. apply nth_error_embed_right.
        apply nth_error_embed_left with
          (right := [RTOTBinary M kind left right]).
        apply rawTermOperationTreeSchedule_root.
      }
      assert (hbinary : RawCodedTermBinaryOperationRow M
          (rawTermOperationBinaryCode M kind)
          sourceCode sourceStep targetCode targetStep
          (rawNumeralValue M
            (offset +
              (length (rawTermOperationTreeSchedule M left) +
               length (rawTermOperationTreeSchedule M right))))
          (rawTermOperationTreeSource M (RTOTBinary M kind left right))
          (rawTermOperationTreeTarget M (RTOTBinary M kind left right))).
      {
        exists
          (rawNumeralValue M
            (offset + Nat.pred
              (length (rawTermOperationTreeSchedule M left)))),
          (rawTermOperationTreeSource M left),
          (rawTermOperationTreeTarget M left),
          (rawNumeralValue M
            (offset +
              (length (rawTermOperationTreeSchedule M left) +
               Nat.pred (length (rawTermOperationTreeSchedule M right))))),
          (rawTermOperationTreeSource M right),
          (rawTermOperationTreeTarget M right).
        split.
        - apply raw_lt_numeralValue_of_lt; [exact hPA |].
          pose proof (rawTermOperationTreeSchedule_length_positive M left).
          lia.
        - split; [exact hleftLookup |]. split.
          + apply raw_lt_numeralValue_of_lt; [exact hPA |].
            pose proof (rawTermOperationTreeSchedule_length_positive M right).
            lia.
          + split; [exact hrightLookup |]. split; reflexivity.
      }
      destruct kind; cbn [rawTermOperationBinaryCode] in hbinary.
      * right. right. right. left. exact hbinary.
      * right. right. right. right. exact hbinary.
Qed.

(** The generic existential wrapper mirrors the common five fields of term
    shift and opening traces. *)
Definition RawCodedTermOperation (M : RawPAModel)
    (variableRow : M -> M -> Prop) (input output : M) : Prop :=
  exists sourceCode sourceStep targetCode targetStep bound rootIndex : M,
    RawCodedAssignmentDefinedThrough M sourceCode sourceStep bound /\
    RawCodedAssignmentDefinedThrough M targetCode targetStep bound /\
    rawLt M rootIndex bound /\
    RawCodedTermOperationPairLookup M
      sourceCode sourceStep targetCode targetStep rootIndex input output /\
    RawCodedTermOperationRows M
      (RawCodedTermOperationTraversalRow M variableRow
        sourceCode sourceStep targetCode targetStep)
      sourceCode sourceStep targetCode targetStep bound.

Arguments RawCodedTermOperation M variableRow input output
  : clear implicits.

Theorem raw_codedTermOperation_of_valid_tree : forall
    (M : RawPAModel), RawPASatisfies M -> forall variableRow tree,
  RawTermOperationTreeValid M variableRow tree ->
  RawCodedTermOperation M variableRow
    (rawTermOperationTreeSource M tree)
    (rawTermOperationTreeTarget M tree).
Proof.
  intros M hPA variableRow tree hvalid.
  set (schedule := rawTermOperationTreeSchedule M tree).
  set (limit := length schedule).
  assert (hlimitPositive : 0 < limit).
  {
    unfold limit, schedule.
    apply rawTermOperationTreeSchedule_length_positive.
  }
  destruct (finite_vector_beta_code M hPA limit
    (rawTermOperationTreeSourceAt M schedule)) as
    [sourceCode [sourceStep hsource]].
  destruct (finite_vector_beta_code M hPA limit
    (rawTermOperationTreeTargetAt M schedule)) as
    [targetCode [targetStep htarget]].
  assert (hscheduleLookup : forall index occurrence,
    nth_error schedule index = Some occurrence ->
    RawCodedTermOperationPairLookup M
      sourceCode sourceStep targetCode targetStep
      (rawNumeralValue M index)
      (rawTermOperationTreeSource M occurrence)
      (rawTermOperationTreeTarget M occurrence)).
  {
    intros index occurrence hnth.
    assert (hindex : index < limit).
    {
      unfold limit. apply (proj1 (nth_error_Some schedule index)).
      now rewrite hnth.
    }
    split.
    - rewrite <- (rawTermOperationTreeSourceAt_nth_error
        M schedule index occurrence hnth). apply hsource. exact hindex.
    - rewrite <- (rawTermOperationTreeTargetAt_nth_error
        M schedule index occurrence hnth). apply htarget. exact hindex.
  }
  unfold RawCodedTermOperation.
  exists sourceCode, sourceStep, targetCode, targetStep,
    (rawNumeralValue M limit), (rawNumeralValue M (Nat.pred limit)).
  repeat split.
  - intros index hindex.
    destruct (raw_lt_numeralValue_cases M hPA index limit hindex)
      as [k [hk ->]].
    exists (rawTermOperationTreeSourceAt M schedule k).
    apply hsource. exact hk.
  - intros index hindex.
    destruct (raw_lt_numeralValue_cases M hPA index limit hindex)
      as [k [hk ->]].
    exists (rawTermOperationTreeTargetAt M schedule k).
    apply htarget. exact hk.
  - apply raw_lt_numeralValue_of_lt; [exact hPA | lia].
  - assert (hrootNth : nth_error schedule (Nat.pred limit) = Some tree).
    {
      unfold schedule, limit. apply rawTermOperationTreeSchedule_root.
    }
    exact (proj1 (hscheduleLookup _ _ hrootNth)).
  - assert (hrootNth : nth_error schedule (Nat.pred limit) = Some tree).
    {
      unfold schedule, limit. apply rawTermOperationTreeSchedule_root.
    }
    exact (proj2 (hscheduleLookup _ _ hrootNth)).
  - intros index input output hindex hpair.
    destruct (raw_lt_numeralValue_cases M hPA index limit hindex)
      as [k [hk ->]].
    assert (hnonempty : nth_error schedule k <> None).
    { apply (proj2 (nth_error_Some schedule k)). exact hk. }
    destruct (nth_error schedule k) as [occurrence |]
      eqn:hnth; [|contradiction].
    destruct hpair as [hinput houtput].
    pose proof (hscheduleLookup k occurrence hnth) as
      [hsourceCanonical htargetCanonical].
    assert (hinputEq : input = rawTermOperationTreeSource M occurrence).
    {
      exact (raw_codedAssignmentLookup_functional M hPA
        sourceCode sourceStep (rawNumeralValue M k) input
        (rawTermOperationTreeSource M occurrence)
        hinput hsourceCanonical).
    }
    assert (houtputEq : output = rawTermOperationTreeTarget M occurrence).
    {
      exact (raw_codedAssignmentLookup_functional M hPA
        targetCode targetStep (rawNumeralValue M k) output
        (rawTermOperationTreeTarget M occurrence)
        houtput htargetCanonical).
    }
    subst input. subst output.
    apply (raw_termOperationTree_segment_row M hPA variableRow tree
      hvalid sourceCode sourceStep targetCode targetStep 0).
    { unfold RawTermOperationTreeSegmentLookup.
      intros local localOccurrence hlocal.
      cbn. exact (hscheduleLookup _ _ hlocal). }
    exact hnth.
Qed.

Corollary raw_codedTermOpening_of_valid_tree : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    cutoff liftedReplacement tree,
  RawTermOperationTreeValid M
    (RawCodedTermOpeningVariableRow M cutoff liftedReplacement) tree ->
  RawCodedTermOpening M cutoff liftedReplacement
    (rawTermOperationTreeSource M tree)
    (rawTermOperationTreeTarget M tree).
Proof.
  intros M hPA cutoff liftedReplacement tree hvalid.
  pose proof (raw_codedTermOperation_of_valid_tree M hPA
    (RawCodedTermOpeningVariableRow M cutoff liftedReplacement)
    tree hvalid) as hopening.
  unfold RawCodedTermOperation in hopening.
  unfold RawCodedTermOpening.
  destruct hopening as
    (sourceCode & sourceStep & targetCode & targetStep & bound & rootIndex &
     hsource & htarget & hroot & hlookup & hrows).
  exists sourceCode, sourceStep, targetCode, targetStep, bound, rootIndex.
  unfold RawCodedTermOpeningTrace.
  split; [exact hsource |].
  split; [exact htarget |].
  split; [exact hroot |].
  split; [exact hlookup |].
  unfold RawCodedTermOpeningRows,
    RawCodedTermOpeningTraversalRow.
  exact hrows.
Qed.

End PABoundedRawCodedTermOperationTreeRealization.
