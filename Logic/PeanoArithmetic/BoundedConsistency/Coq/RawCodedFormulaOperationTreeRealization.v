(**
  Generic finite realization of a carrier-valued formula-operation tree.

  [RawCodedFormulaShiftTreeRealization] introduced the finite formula
  skeleton needed when equality leaves contain genuinely nonstandard carrier
  values.  The beta-table construction itself is independent of shifting.
  This module factors out precisely that parametric argument: a client gives
  an arbitrary four-place atomic relation and validates the two term payloads
  at each equality leaf.  The same postorder schedule then realizes the full
  raw formula operation.

  The main client below is single substitution, whose atomic relation first
  lifts the replacement and then opens a term.  Keeping the realizer generic
  avoids duplicating the delicate child-index arithmetic for each operation.
*)

From Stdlib Require Import List Arith Lia.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedAssignment RawCodedFormulaOperations
  RawCodedFormulaOperationsStandardRealization
  RawCodedFormulaShiftTreeRealization.

Import ListNotations.

Module PABoundedRawCodedFormulaOperationTreeRealization.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaOperationsStandardRealization.
Import PABoundedRawCodedFormulaShiftTreeRealization.

(** Structural validity is parametric only at equality leaves.  All other
    clauses state the depth equations required by the represented traversal
    rows. *)
Fixpoint RawFormulaOperationTreeValid (M : RawPAModel)
    (atom : M -> M -> M -> M -> Prop) (parameter : M)
    (tree : RawFormulaShiftTree M) : Prop :=
  match tree with
  | RFSTEq _ depth sourceLeft targetLeft sourceRight targetRight =>
      atom parameter depth sourceLeft targetLeft /\
      atom parameter depth sourceRight targetRight
  | RFSTBot _ _ => True
  | RFSTBinary _ _ depth leftTree rightTree =>
      rawFormulaShiftTreeDepth M leftTree = depth /\
      rawFormulaShiftTreeDepth M rightTree = depth /\
      RawFormulaOperationTreeValid M atom parameter leftTree /\
      RawFormulaOperationTreeValid M atom parameter rightTree
  | RFSTUnary _ _ depth child =>
      rawFormulaShiftTreeDepth M child = raw_succ M depth /\
      RawFormulaOperationTreeValid M atom parameter child
  end.

Arguments RawFormulaOperationTreeValid M atom parameter tree
  : clear implicits.

(** Every occurrence in a validated tree supplies its local represented row.
    Postorder is essential here: it puts the roots of all child schedules at
    strictly smaller beta-table indices than the parent row. *)
Lemma raw_formulaOperationTree_segment_row : forall
    (M : RawPAModel), RawPASatisfies M -> forall atom parameter tree,
  RawFormulaOperationTreeValid M atom parameter tree ->
  forall sourceCode sourceStep targetCode targetStep depthCode depthStep
    offset,
  RawFormulaShiftTreeSegmentLookup M
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    (rawFormulaShiftTreeSchedule M tree) offset ->
  forall index occurrence,
  nth_error (rawFormulaShiftTreeSchedule M tree) index = Some occurrence ->
  RawCodedFormulaOperationTraversalRow M atom parameter
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    (rawNumeralValue M (offset + index))
    (rawFormulaShiftTreeSource M occurrence)
    (rawFormulaShiftTreeTarget M occurrence)
    (rawFormulaShiftTreeDepth M occurrence).
Proof.
  intros M hPA atom parameter tree. induction tree as
      [depth sourceLeft targetLeft sourceRight targetRight
      | depth
      | kind depth left IHleft right IHright
      | kind depth child IHchild];
    intros hvalid sourceCode sourceStep targetCode targetStep
      depthCode depthStep offset hlookup index occurrence hnth.
  - destruct (nth_error_singleton_inv _ _ _ _ hnth) as [-> ->].
    cbn [rawFormulaShiftTreeSource rawFormulaShiftTreeTarget
      rawFormulaShiftTreeDepth RawFormulaOperationTreeValid] in *.
    left. exists sourceLeft, targetLeft, sourceRight, targetRight.
    repeat split; try reflexivity; tauto.
  - destruct (nth_error_singleton_inv _ _ _ _ hnth) as [-> ->].
    right. left. split; reflexivity.
  - cbn [rawFormulaShiftTreeSchedule] in hnth, hlookup.
    cbn [RawFormulaOperationTreeValid] in hvalid.
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
    cbn [RawFormulaOperationTreeValid] in hvalid.
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

(** Finite beta realization of the source, target, and depth columns. *)
Theorem raw_codedFormulaOperation_of_valid_tree : forall
    (M : RawPAModel), RawPASatisfies M -> forall atom parameter tree,
  RawFormulaOperationTreeValid M atom parameter tree ->
  RawCodedFormulaOperation M atom parameter
    (rawFormulaShiftTreeDepth M tree)
    (rawFormulaShiftTreeSource M tree)
    (rawFormulaShiftTreeTarget M tree).
Proof.
  intros M hPA atom parameter tree hvalid.
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
  unfold RawCodedFormulaOperation.
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
              apply (raw_formulaOperationTree_segment_row M hPA
                atom parameter tree hvalid
                sourceCode sourceStep targetCode targetStep
                depthCode depthStep 0).
              { unfold RawFormulaShiftTreeSegmentLookup.
                intros local localOccurrence hlocal.
                cbn. exact (hscheduleLookup _ _ hlocal). }
              exact hnth.
Qed.

(** Substitution is the principal specialization of the generic theorem. *)
Definition RawFormulaSubstitutionTreeValid (M : RawPAModel)
    (replacement : M) (tree : RawFormulaShiftTree M) : Prop :=
  RawFormulaOperationTreeValid M
    (RawCodedFormulaSubstitutionAtom M) replacement tree.

Arguments RawFormulaSubstitutionTreeValid M replacement tree
  : clear implicits.

Corollary raw_codedFormulaSubstitution_of_valid_tree : forall
    (M : RawPAModel), RawPASatisfies M -> forall replacement tree,
  RawFormulaSubstitutionTreeValid M replacement tree ->
  RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
    replacement (rawFormulaShiftTreeDepth M tree)
    (rawFormulaShiftTreeSource M tree)
    (rawFormulaShiftTreeTarget M tree).
Proof.
  intros M hPA replacement tree hvalid.
  exact (raw_codedFormulaOperation_of_valid_tree M hPA
    (RawCodedFormulaSubstitutionAtom M) replacement tree hvalid).
Qed.

Corollary raw_codedFormulaSingleSubstitution_of_valid_tree : forall
    (M : RawPAModel), RawPASatisfies M -> forall replacement tree,
  rawFormulaShiftTreeDepth M tree = raw_zero M ->
  RawFormulaSubstitutionTreeValid M replacement tree ->
  RawCodedFormulaSingleSubstitution M replacement
    (rawFormulaShiftTreeSource M tree)
    (rawFormulaShiftTreeTarget M tree).
Proof.
  intros M hPA replacement tree hdepth hvalid.
  unfold RawCodedFormulaSingleSubstitution.
  rewrite <- hdepth.
  exact (raw_codedFormulaSubstitution_of_valid_tree
    M hPA replacement tree hvalid).
Qed.

End PABoundedRawCodedFormulaOperationTreeRealization.
