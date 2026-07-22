(**
  Finite realization of a raw formula-shift tree.

  Standard quotation is not available for a formula containing a genuinely
  nonstandard numeral-term code.  Its *formula* skeleton is nevertheless a
  finite metatheoretic tree.  The datatype below records that skeleton using
  carrier-valued equality leaves.  Validation asks for the exact term-shift
  certificates at those leaves.  A postorder occurrence schedule then turns
  any validated tree into the beta-coded traversal required by
  [RawCodedFormulaShift].

  This construction is deliberately generic: it neither decodes carrier
  elements nor assumes totality of the raw formula operation.  All recursive
  work is over the explicit finite [RawFormulaShiftTree].
*)

From Stdlib Require Import List Arith Lia.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedAssignment
  RawCodedFormulaOperations RawCodedFormulaOperationsStandardRealization.

Import ListNotations.

Module PABoundedRawCodedFormulaShiftTreeRealization.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaOperationsStandardRealization.

Inductive RawFormulaShiftBinaryKind : Type :=
| RFSBImp
| RFSBAnd
| RFSBOr.

Inductive RawFormulaShiftUnaryKind : Type :=
| RFSUAll
| RFSUEx.

Definition rawFormulaShiftBinaryCode (M : RawPAModel)
    (kind : RawFormulaShiftBinaryKind) (left right : M) : M :=
  match kind with
  | RFSBImp => rawFormulaImpCode M left right
  | RFSBAnd => rawFormulaAndCode M left right
  | RFSBOr => rawFormulaOrCode M left right
  end.

Definition rawFormulaShiftUnaryCode (M : RawPAModel)
    (kind : RawFormulaShiftUnaryKind) (child : M) : M :=
  match kind with
  | RFSUAll => rawFormulaAllCode M child
  | RFSUEx => rawFormulaExCode M child
  end.

(** Equality leaves store source and target term codes explicitly. *)
Inductive RawFormulaShiftTree (M : RawPAModel) : Type :=
| RFSTEq : M -> M -> M -> M -> M -> RawFormulaShiftTree M
| RFSTBot : M -> RawFormulaShiftTree M
| RFSTBinary : RawFormulaShiftBinaryKind -> M ->
    RawFormulaShiftTree M -> RawFormulaShiftTree M ->
    RawFormulaShiftTree M
| RFSTUnary : RawFormulaShiftUnaryKind -> M ->
    RawFormulaShiftTree M -> RawFormulaShiftTree M.

Arguments RFSTEq M depth sourceLeft targetLeft sourceRight targetRight
  : clear implicits.
Arguments RFSTBot M depth : clear implicits.
Arguments RFSTBinary M kind depth left right : clear implicits.
Arguments RFSTUnary M kind depth child : clear implicits.

Definition rawFormulaShiftTreeDepth (M : RawPAModel)
    (tree : RawFormulaShiftTree M) : M :=
  match tree with
  | RFSTEq _ depth _ _ _ _ => depth
  | RFSTBot _ depth => depth
  | RFSTBinary _ _ depth _ _ => depth
  | RFSTUnary _ _ depth _ => depth
  end.

Fixpoint rawFormulaShiftTreeSource (M : RawPAModel)
    (tree : RawFormulaShiftTree M) : M :=
  match tree with
  | RFSTEq _ _ sourceLeft _ sourceRight _ =>
      rawFormulaEqCode M sourceLeft sourceRight
  | RFSTBot _ _ => rawFormulaBotCode M
  | RFSTBinary _ kind _ leftTree rightTree =>
      rawFormulaShiftBinaryCode M kind
        (rawFormulaShiftTreeSource M leftTree)
        (rawFormulaShiftTreeSource M rightTree)
  | RFSTUnary _ kind _ child =>
      rawFormulaShiftUnaryCode M kind
        (rawFormulaShiftTreeSource M child)
  end.

Fixpoint rawFormulaShiftTreeTarget (M : RawPAModel)
    (tree : RawFormulaShiftTree M) : M :=
  match tree with
  | RFSTEq _ _ _ targetLeft _ targetRight =>
      rawFormulaEqCode M targetLeft targetRight
  | RFSTBot _ _ => rawFormulaBotCode M
  | RFSTBinary _ kind _ leftTree rightTree =>
      rawFormulaShiftBinaryCode M kind
        (rawFormulaShiftTreeTarget M leftTree)
        (rawFormulaShiftTreeTarget M rightTree)
  | RFSTUnary _ kind _ child =>
      rawFormulaShiftUnaryCode M kind
        (rawFormulaShiftTreeTarget M child)
  end.

(** Child depths are stated explicitly.  For a binary node they equal the
    parent depth; for a quantified node they are its successor. *)
Fixpoint RawFormulaShiftTreeValid (M : RawPAModel) (amount : M)
    (tree : RawFormulaShiftTree M) : Prop :=
  match tree with
  | RFSTEq _ depth sourceLeft targetLeft sourceRight targetRight =>
      RawCodedTermShift M depth amount sourceLeft targetLeft /\
      RawCodedTermShift M depth amount sourceRight targetRight
  | RFSTBot _ _ => True
  | RFSTBinary _ _ depth leftTree rightTree =>
      rawFormulaShiftTreeDepth M leftTree = depth /\
      rawFormulaShiftTreeDepth M rightTree = depth /\
      RawFormulaShiftTreeValid M amount leftTree /\
      RawFormulaShiftTreeValid M amount rightTree
  | RFSTUnary _ _ depth child =>
      rawFormulaShiftTreeDepth M child = raw_succ M depth /\
      RawFormulaShiftTreeValid M amount child
  end.

Arguments rawFormulaShiftTreeDepth M tree : clear implicits.
Arguments rawFormulaShiftTreeSource M tree : clear implicits.
Arguments rawFormulaShiftTreeTarget M tree : clear implicits.
Arguments RawFormulaShiftTreeValid M amount tree : clear implicits.

(** Postorder makes every child root strictly earlier than its parent. *)
Fixpoint rawFormulaShiftTreeSchedule (M : RawPAModel)
    (tree : RawFormulaShiftTree M) : list (RawFormulaShiftTree M) :=
  match tree with
  | RFSTEq _ _ _ _ _ _ => [tree]
  | RFSTBot _ _ => [tree]
  | RFSTBinary _ _ _ leftTree rightTree =>
      rawFormulaShiftTreeSchedule M leftTree ++
      rawFormulaShiftTreeSchedule M rightTree ++ [tree]
  | RFSTUnary _ _ _ child =>
      rawFormulaShiftTreeSchedule M child ++ [tree]
  end.

Definition rawFormulaShiftTreeDefault (M : RawPAModel)
    : RawFormulaShiftTree M := RFSTBot M (raw_zero M).

Definition rawFormulaShiftTreeSourceAt (M : RawPAModel)
    (schedule : list (RawFormulaShiftTree M)) (index : nat) : M :=
  rawFormulaShiftTreeSource M
    (nth index schedule (rawFormulaShiftTreeDefault M)).

Definition rawFormulaShiftTreeTargetAt (M : RawPAModel)
    (schedule : list (RawFormulaShiftTree M)) (index : nat) : M :=
  rawFormulaShiftTreeTarget M
    (nth index schedule (rawFormulaShiftTreeDefault M)).

Definition rawFormulaShiftTreeDepthAt (M : RawPAModel)
    (schedule : list (RawFormulaShiftTree M)) (index : nat) : M :=
  rawFormulaShiftTreeDepth M
    (nth index schedule (rawFormulaShiftTreeDefault M)).

Lemma rawFormulaShiftTreeSourceAt_nth_error : forall
    M schedule index occurrence,
  nth_error schedule index = Some occurrence ->
  rawFormulaShiftTreeSourceAt M schedule index =
    rawFormulaShiftTreeSource M occurrence.
Proof.
  intros M schedule index occurrence hnth.
  unfold rawFormulaShiftTreeSourceAt.
  now rewrite (nth_error_nth schedule index
    (rawFormulaShiftTreeDefault M) hnth).
Qed.

Lemma rawFormulaShiftTreeTargetAt_nth_error : forall
    M schedule index occurrence,
  nth_error schedule index = Some occurrence ->
  rawFormulaShiftTreeTargetAt M schedule index =
    rawFormulaShiftTreeTarget M occurrence.
Proof.
  intros M schedule index occurrence hnth.
  unfold rawFormulaShiftTreeTargetAt.
  now rewrite (nth_error_nth schedule index
    (rawFormulaShiftTreeDefault M) hnth).
Qed.

Lemma rawFormulaShiftTreeDepthAt_nth_error : forall
    M schedule index occurrence,
  nth_error schedule index = Some occurrence ->
  rawFormulaShiftTreeDepthAt M schedule index =
    rawFormulaShiftTreeDepth M occurrence.
Proof.
  intros M schedule index occurrence hnth.
  unfold rawFormulaShiftTreeDepthAt.
  now rewrite (nth_error_nth schedule index
    (rawFormulaShiftTreeDefault M) hnth).
Qed.

Lemma rawFormulaShiftTreeSchedule_nonempty : forall M tree,
  rawFormulaShiftTreeSchedule M tree <> [].
Proof.
  intros M tree. destruct tree; intro hempty;
    pose proof (f_equal (@length (RawFormulaShiftTree M)) hempty)
      as hlength;
    cbn [rawFormulaShiftTreeSchedule] in hlength;
    repeat rewrite length_app in hlength; cbn in hlength; lia.
Qed.

Lemma rawFormulaShiftTreeSchedule_length_positive : forall M tree,
  0 < length (rawFormulaShiftTreeSchedule M tree).
Proof.
  intros M tree.
  pose proof (rawFormulaShiftTreeSchedule_nonempty M tree).
  destruct (rawFormulaShiftTreeSchedule M tree); cbn;
    [contradiction | lia].
Qed.

Lemma rawFormulaShiftTreeSchedule_root : forall M tree,
  nth_error (rawFormulaShiftTreeSchedule M tree)
    (Nat.pred (length (rawFormulaShiftTreeSchedule M tree))) = Some tree.
Proof.
  intros M tree. destruct tree; cbn [rawFormulaShiftTreeSchedule].
  - reflexivity.
  - reflexivity.
  - rewrite !length_app. cbn.
    replace
      (Nat.pred
        (length (rawFormulaShiftTreeSchedule M tree1) +
         (length (rawFormulaShiftTreeSchedule M tree2) + 1)))
      with
      (length (rawFormulaShiftTreeSchedule M tree1) +
       length (rawFormulaShiftTreeSchedule M tree2)) by lia.
    apply nth_error_binary_postorder_root.
  - rewrite length_app. cbn.
    replace
      (Nat.pred (length (rawFormulaShiftTreeSchedule M tree) + 1))
      with (length (rawFormulaShiftTreeSchedule M tree)) by lia.
    apply nth_error_snoc_last.
Qed.

Definition RawFormulaShiftTreeSegmentLookup (M : RawPAModel)
    (sourceCode sourceStep targetCode targetStep depthCode depthStep : M)
    (schedule : list (RawFormulaShiftTree M)) (offset : nat) : Prop :=
  forall index occurrence,
    nth_error schedule index = Some occurrence ->
    RawCodedFormulaOperationTripleLookup M
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      (rawNumeralValue M (offset + index))
      (rawFormulaShiftTreeSource M occurrence)
      (rawFormulaShiftTreeTarget M occurrence)
      (rawFormulaShiftTreeDepth M occurrence).

(** Every occurrence in a validated tree supplies the corresponding local
    traversal row. *)
Lemma raw_formulaShiftTree_segment_row : forall
    (M : RawPAModel), RawPASatisfies M -> forall amount tree,
  RawFormulaShiftTreeValid M amount tree ->
  forall sourceCode sourceStep targetCode targetStep depthCode depthStep
    offset,
  RawFormulaShiftTreeSegmentLookup M
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    (rawFormulaShiftTreeSchedule M tree) offset ->
  forall index occurrence,
  nth_error (rawFormulaShiftTreeSchedule M tree) index = Some occurrence ->
  RawCodedFormulaOperationTraversalRow M
    (RawCodedFormulaShiftAtom M) amount
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    (rawNumeralValue M (offset + index))
    (rawFormulaShiftTreeSource M occurrence)
    (rawFormulaShiftTreeTarget M occurrence)
    (rawFormulaShiftTreeDepth M occurrence).
Proof.
  intros M hPA amount tree. induction tree as
      [depth sourceLeft targetLeft sourceRight targetRight
      | depth
      | kind depth left IHleft right IHright
      | kind depth child IHchild];
    intros hvalid sourceCode sourceStep targetCode targetStep
      depthCode depthStep offset hlookup index occurrence hnth.
  - destruct (nth_error_singleton_inv _ _ _ _ hnth) as [-> ->].
    cbn [rawFormulaShiftTreeSource rawFormulaShiftTreeTarget
      rawFormulaShiftTreeDepth RawFormulaShiftTreeValid] in *.
    left. exists sourceLeft, targetLeft, sourceRight, targetRight.
    repeat split; try reflexivity; tauto.
  - destruct (nth_error_singleton_inv _ _ _ _ hnth) as [-> ->].
    right. left. split; reflexivity.
  - cbn [rawFormulaShiftTreeSchedule] in hnth, hlookup.
    cbn [RawFormulaShiftTreeValid] in hvalid.
    destruct hvalid as [hleftDepth [hrightDepth [hleftValid hrightValid]]].
    unfold RawFormulaShiftTreeSegmentLookup in hlookup.
    destruct (nth_error_binary_postorder_cases _ _ _ _ _ _ hnth) as
      [[hleft hnthLeft] |
       [(rightIndex & -> & hright & hnthRight) | [-> ->]]].
    + apply (IHleft hleftValid sourceCode sourceStep targetCode targetStep
        depthCode depthStep offset).
      * intros local localOccurrence hlocal.
        apply hlookup.
        apply nth_error_embed_left with
          (right := rawFormulaShiftTreeSchedule M right ++
            [RFSTBinary M kind depth left right]).
        exact hlocal.
      * exact hnthLeft.
    + replace
        (rawNumeralValue M
          (offset +
            (length (rawFormulaShiftTreeSchedule M left) + rightIndex)))
        with
        (rawNumeralValue M
          ((offset + length (rawFormulaShiftTreeSchedule M left)) +
            rightIndex)) by (f_equal; lia).
      apply (IHright hrightValid sourceCode sourceStep targetCode targetStep
        depthCode depthStep
        (offset + length (rawFormulaShiftTreeSchedule M left))).
      * intros local localOccurrence hlocal.
        specialize (hlookup
          (length (rawFormulaShiftTreeSchedule M left) + local)
          localOccurrence).
        assert (hembed :
          nth_error
            (rawFormulaShiftTreeSchedule M left ++
             rawFormulaShiftTreeSchedule M right ++
             [RFSTBinary M kind depth left right])
            (length (rawFormulaShiftTreeSchedule M left) + local) =
          Some localOccurrence).
        {
          apply nth_error_embed_right.
          apply nth_error_embed_left with
            (right := [RFSTBinary M kind depth left right]).
          exact hlocal.
        }
        specialize (hlookup hembed).
        replace
          (offset +
            (length (rawFormulaShiftTreeSchedule M left) + local))
          with
          ((offset + length (rawFormulaShiftTreeSchedule M left)) + local)
          in hlookup by lia.
        exact hlookup.
      * exact hnthRight.
    + assert (hleftLookup :
        RawCodedFormulaOperationTripleLookup M
          sourceCode sourceStep targetCode targetStep depthCode depthStep
          (rawNumeralValue M
            (offset + Nat.pred
              (length (rawFormulaShiftTreeSchedule M left))))
          (rawFormulaShiftTreeSource M left)
          (rawFormulaShiftTreeTarget M left)
          (rawFormulaShiftTreeDepth M left)).
      {
        apply hlookup.
        apply nth_error_embed_left with
          (right := rawFormulaShiftTreeSchedule M right ++
            [RFSTBinary M kind depth left right]).
        apply rawFormulaShiftTreeSchedule_root.
      }
      assert (hrightLookup :
        RawCodedFormulaOperationTripleLookup M
          sourceCode sourceStep targetCode targetStep depthCode depthStep
          (rawNumeralValue M
            (offset +
              (length (rawFormulaShiftTreeSchedule M left) +
               Nat.pred
                 (length (rawFormulaShiftTreeSchedule M right)))))
          (rawFormulaShiftTreeSource M right)
          (rawFormulaShiftTreeTarget M right)
          (rawFormulaShiftTreeDepth M right)).
      {
        apply hlookup.
        apply nth_error_embed_right.
        apply nth_error_embed_left with
          (right := [RFSTBinary M kind depth left right]).
        apply rawFormulaShiftTreeSchedule_root.
      }
      assert (hbinary : RawCodedFormulaBinaryOperationRow M
          (rawFormulaShiftBinaryCode M kind)
          sourceCode sourceStep targetCode targetStep depthCode depthStep
          (rawNumeralValue M
            (offset +
              (length (rawFormulaShiftTreeSchedule M left) +
               length (rawFormulaShiftTreeSchedule M right))))
          (rawFormulaShiftTreeSource M
            (RFSTBinary M kind depth left right))
          (rawFormulaShiftTreeTarget M
            (RFSTBinary M kind depth left right)) depth).
      {
        exists
          (rawNumeralValue M
            (offset + Nat.pred
              (length (rawFormulaShiftTreeSchedule M left)))),
          (rawFormulaShiftTreeSource M left),
          (rawFormulaShiftTreeTarget M left),
          (rawFormulaShiftTreeDepth M left),
          (rawNumeralValue M
            (offset +
              (length (rawFormulaShiftTreeSchedule M left) +
               Nat.pred
                 (length (rawFormulaShiftTreeSchedule M right))))),
          (rawFormulaShiftTreeSource M right),
          (rawFormulaShiftTreeTarget M right),
          (rawFormulaShiftTreeDepth M right).
        split.
        - apply raw_lt_numeralValue_of_lt; [exact hPA |].
          pose proof (rawFormulaShiftTreeSchedule_length_positive M left).
          lia.
        - split; [exact hleftLookup |].
          split; [exact hleftDepth |].
          split.
          + apply raw_lt_numeralValue_of_lt; [exact hPA |].
            pose proof (rawFormulaShiftTreeSchedule_length_positive M right).
            lia.
          + split; [exact hrightLookup |].
            split; [exact hrightDepth |].
            split; reflexivity.
      }
      destruct kind; cbn [rawFormulaShiftBinaryCode] in hbinary.
      * right. right. left. exact hbinary.
      * right. right. right. left. exact hbinary.
      * right. right. right. right. left. exact hbinary.
  - cbn [rawFormulaShiftTreeSchedule] in hnth, hlookup.
    cbn [RawFormulaShiftTreeValid] in hvalid.
    destruct hvalid as [hchildDepth hchildValid].
    unfold RawFormulaShiftTreeSegmentLookup in hlookup.
    destruct (nth_error_unary_postorder_cases _ _ _ _ _ hnth) as
      [[hchild hnthChild] | [-> ->]].
    + apply (IHchild hchildValid sourceCode sourceStep targetCode targetStep
        depthCode depthStep offset).
      * intros local localOccurrence hlocal.
        apply hlookup.
        apply nth_error_embed_left with
          (right := [RFSTUnary M kind depth child]).
        exact hlocal.
      * exact hnthChild.
    + assert (hchildLookup :
        RawCodedFormulaOperationTripleLookup M
          sourceCode sourceStep targetCode targetStep depthCode depthStep
          (rawNumeralValue M
            (offset + Nat.pred
              (length (rawFormulaShiftTreeSchedule M child))))
          (rawFormulaShiftTreeSource M child)
          (rawFormulaShiftTreeTarget M child)
          (rawFormulaShiftTreeDepth M child)).
      {
        apply hlookup.
        apply nth_error_embed_left with
          (right := [RFSTUnary M kind depth child]).
        apply rawFormulaShiftTreeSchedule_root.
      }
      assert (hunary : RawCodedFormulaUnaryOperationRow M
          (rawFormulaShiftUnaryCode M kind)
          sourceCode sourceStep targetCode targetStep depthCode depthStep
          (rawNumeralValue M
            (offset + length (rawFormulaShiftTreeSchedule M child)))
          (rawFormulaShiftTreeSource M
            (RFSTUnary M kind depth child))
          (rawFormulaShiftTreeTarget M
            (RFSTUnary M kind depth child)) depth).
      {
        exists
          (rawNumeralValue M
            (offset + Nat.pred
              (length (rawFormulaShiftTreeSchedule M child)))),
          (rawFormulaShiftTreeSource M child),
          (rawFormulaShiftTreeTarget M child),
          (rawFormulaShiftTreeDepth M child).
        split.
        - apply raw_lt_numeralValue_of_lt; [exact hPA |].
          pose proof (rawFormulaShiftTreeSchedule_length_positive M child).
          lia.
        - split; [exact hchildLookup |].
          split; [exact hchildDepth |].
          split; reflexivity.
      }
      destruct kind; cbn [rawFormulaShiftUnaryCode] in hunary.
      * right. right. right. right. right. left. exact hunary.
      * right. right. right. right. right. right. exact hunary.
Qed.

(** Finite beta realization of the three carrier-valued schedule columns. *)
Theorem raw_codedFormulaShift_of_valid_tree : forall
    (M : RawPAModel), RawPASatisfies M -> forall amount tree,
  RawFormulaShiftTreeValid M amount tree ->
  RawCodedFormulaShift M
    (rawFormulaShiftTreeDepth M tree) amount
    (rawFormulaShiftTreeSource M tree)
    (rawFormulaShiftTreeTarget M tree).
Proof.
  intros M hPA amount tree hvalid.
  set (schedule := rawFormulaShiftTreeSchedule M tree).
  set (limit := length schedule).
  assert (hlimitPositive : 0 < limit).
  {
    unfold limit, schedule.
    apply rawFormulaShiftTreeSchedule_length_positive.
  }
  destruct (finite_vector_beta_code M hPA limit
    (rawFormulaShiftTreeSourceAt M schedule)) as
    [sourceCode [sourceStep hsource]].
  destruct (finite_vector_beta_code M hPA limit
    (rawFormulaShiftTreeTargetAt M schedule)) as
    [targetCode [targetStep htarget]].
  destruct (finite_vector_beta_code M hPA limit
    (rawFormulaShiftTreeDepthAt M schedule)) as
    [depthCode [depthStep hdepth]].
  assert (hscheduleLookup : forall index occurrence,
    nth_error schedule index = Some occurrence ->
    RawCodedFormulaOperationTripleLookup M
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      (rawNumeralValue M index)
      (rawFormulaShiftTreeSource M occurrence)
      (rawFormulaShiftTreeTarget M occurrence)
      (rawFormulaShiftTreeDepth M occurrence)).
  {
    intros index occurrence hnth.
    assert (hindex : index < limit).
    {
      unfold limit. apply (proj1 (nth_error_Some schedule index)).
      now rewrite hnth.
    }
    split.
    - rewrite <- (rawFormulaShiftTreeSourceAt_nth_error
        M schedule index occurrence hnth).
      apply hsource. exact hindex.
    - split.
      + rewrite <- (rawFormulaShiftTreeTargetAt_nth_error
          M schedule index occurrence hnth).
        apply htarget. exact hindex.
      + rewrite <- (rawFormulaShiftTreeDepthAt_nth_error
          M schedule index occurrence hnth).
        apply hdepth. exact hindex.
  }
  unfold RawCodedFormulaShift, RawCodedFormulaOperation.
  exists sourceCode, sourceStep, targetCode, targetStep,
    depthCode, depthStep, (rawNumeralValue M limit),
    (rawNumeralValue M (Nat.pred limit)).
  unfold RawCodedFormulaOperationTrace.
  split.
  - intros index hindex.
    destruct (raw_lt_numeralValue_cases M hPA index limit hindex)
      as [k [hk ->]].
    exists (rawFormulaShiftTreeSourceAt M schedule k).
    apply hsource. exact hk.
  - split.
    + intros index hindex.
      destruct (raw_lt_numeralValue_cases M hPA index limit hindex)
        as [k [hk ->]].
      exists (rawFormulaShiftTreeTargetAt M schedule k).
      apply htarget. exact hk.
    + split.
      * intros index hindex.
        destruct (raw_lt_numeralValue_cases M hPA index limit hindex)
          as [k [hk ->]].
        exists (rawFormulaShiftTreeDepthAt M schedule k).
        apply hdepth. exact hk.
      * split.
        -- apply raw_lt_numeralValue_of_lt; [exact hPA | lia].
        -- split.
           ++ assert (hrootNth :
                nth_error schedule (Nat.pred limit) = Some tree).
              {
                unfold schedule, limit.
                apply rawFormulaShiftTreeSchedule_root.
              }
              exact (hscheduleLookup _ _ hrootNth).
           ++ intros index input output depth hindex htriple.
              destruct (raw_lt_numeralValue_cases M hPA index limit hindex)
                as [k [hk ->]].
              assert (hnonempty : nth_error schedule k <> None).
              {
                apply (proj2 (nth_error_Some schedule k)). exact hk.
              }
              destruct (nth_error schedule k) as [occurrence |]
                eqn:hnth; [|contradiction].
              destruct htriple as [hinput [houtput hrowDepth]].
              pose proof (hscheduleLookup k occurrence hnth) as
                [hsourceCanonical
                  [htargetCanonical hdepthCanonical]].
              assert (hinputEq : input =
                  rawFormulaShiftTreeSource M occurrence).
              {
                exact (raw_codedAssignmentLookup_functional M hPA
                  sourceCode sourceStep (rawNumeralValue M k) input
                  (rawFormulaShiftTreeSource M occurrence)
                  hinput hsourceCanonical).
              }
              assert (houtputEq : output =
                  rawFormulaShiftTreeTarget M occurrence).
              {
                exact (raw_codedAssignmentLookup_functional M hPA
                  targetCode targetStep (rawNumeralValue M k) output
                  (rawFormulaShiftTreeTarget M occurrence)
                  houtput htargetCanonical).
              }
              assert (hdepthEq : depth =
                  rawFormulaShiftTreeDepth M occurrence).
              {
                exact (raw_codedAssignmentLookup_functional M hPA
                  depthCode depthStep (rawNumeralValue M k) depth
                  (rawFormulaShiftTreeDepth M occurrence)
                  hrowDepth hdepthCanonical).
              }
              subst input. subst output. subst depth.
              apply (raw_formulaShiftTree_segment_row M hPA amount tree
                hvalid sourceCode sourceStep targetCode targetStep
                depthCode depthStep 0).
              { unfold RawFormulaShiftTreeSegmentLookup.
                intros local localOccurrence hlocal.
                cbn. exact (hscheduleLookup _ _ hlocal). }
              exact hnth.
Qed.

End PABoundedRawCodedFormulaShiftTreeRealization.
