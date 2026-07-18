(**
  Finite occurrence realizations of the standard formula operations.

  A formula code cannot by itself index the operation trace: the same
  syntactic subformula may occur below different numbers of binders and must
  then be transformed at different depths.  We therefore flatten the actual
  syntax tree into a finite postorder list of *occurrences*.  Every list entry
  stores its source formula, its transformed formula, and its binder depth.
  Binary child lists precede their parent, and quantified children are built
  at successor depth.  Thus all recursive references made by a row point to
  strictly smaller occurrence indices, even when two entries have identical
  source formula codes.

  The three projections of this external list are beta-coded independently.
  The proof below is entirely uniform in the ambient model of PA: only the
  finite metatheoretic list is inspected by Rocq.  No carrier element is ever
  decoded.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax RawCodedSyntaxConstructors RawCodedAssignment
  RawCodedFormulaRankStep RawCodedFormulaOperations
  RawCodedTermOperationsStandardAdequacy
  RawCodedFormulaOperationsStandardAdequacy.

Import ListNotations.

Module PABoundedRawCodedFormulaOperationsStandardRealization.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFormulaRankStep.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedTermOperationsStandardAdequacy.
Import PABoundedRawCodedFormulaOperationsStandardAdequacy.

(** One entry in an occurrence-indexed operation schedule. *)
Record StandardFormulaOperationOccurrence : Type := {
  standardOccurrenceSource : formula;
  standardOccurrenceTarget : formula;
  standardOccurrenceDepth : nat
}.

Definition standardFormulaOperationRoot
    (transform : nat -> formula -> formula) (depth : nat) (phi : formula)
    : StandardFormulaOperationOccurrence :=
  {| standardOccurrenceSource := phi;
     standardOccurrenceTarget := transform depth phi;
     standardOccurrenceDepth := depth |}.

(** Postorder is essential here.  In the binary cases the complete left and
    right schedules precede the parent; in the unary cases the complete child
    schedule precedes the parent. *)
Fixpoint standardFormulaOperationSchedule
    (transform : nat -> formula -> formula) (depth : nat) (phi : formula)
    : list StandardFormulaOperationOccurrence :=
  let root := standardFormulaOperationRoot transform depth phi in
  match phi with
  | pEq _ _ => [root]
  | pBot => [root]
  | pImp lhs rhs =>
      standardFormulaOperationSchedule transform depth lhs ++
      standardFormulaOperationSchedule transform depth rhs ++ [root]
  | pAnd lhs rhs =>
      standardFormulaOperationSchedule transform depth lhs ++
      standardFormulaOperationSchedule transform depth rhs ++ [root]
  | pOr lhs rhs =>
      standardFormulaOperationSchedule transform depth lhs ++
      standardFormulaOperationSchedule transform depth rhs ++ [root]
  | pAll child =>
      standardFormulaOperationSchedule transform (S depth) child ++ [root]
  | pEx child =>
      standardFormulaOperationSchedule transform (S depth) child ++ [root]
  end.

Definition standardFormulaOperationDefaultOccurrence
    : StandardFormulaOperationOccurrence :=
  standardFormulaOperationRoot (fun _ phi => phi) 0 pBot.

(** The finite-vector environments.  [nth] is harmless at an out-of-range
    index because finite beta realization only asks for indices below the
    schedule length. *)
Definition rawStandardFormulaOperationSourceAt (M : RawPAModel)
    (schedule : list StandardFormulaOperationOccurrence) (index : nat) : M :=
  rawQuotedFormulaCode M
    (standardOccurrenceSource
      (nth index schedule standardFormulaOperationDefaultOccurrence)).

Definition rawStandardFormulaOperationTargetAt (M : RawPAModel)
    (schedule : list StandardFormulaOperationOccurrence) (index : nat) : M :=
  rawQuotedFormulaCode M
    (standardOccurrenceTarget
      (nth index schedule standardFormulaOperationDefaultOccurrence)).

Definition rawStandardFormulaOperationDepthAt (M : RawPAModel)
    (schedule : list StandardFormulaOperationOccurrence) (index : nat) : M :=
  rawNumeralValue M
    (standardOccurrenceDepth
      (nth index schedule standardFormulaOperationDefaultOccurrence)).

Lemma rawStandardFormulaOperationSourceAt_nth_error : forall
    M schedule index occurrence,
  nth_error schedule index = Some occurrence ->
  rawStandardFormulaOperationSourceAt M schedule index =
    rawQuotedFormulaCode M (standardOccurrenceSource occurrence).
Proof.
  intros M schedule index occurrence hnth.
  unfold rawStandardFormulaOperationSourceAt.
  now rewrite (nth_error_nth schedule index
    standardFormulaOperationDefaultOccurrence hnth).
Qed.

Lemma rawStandardFormulaOperationTargetAt_nth_error : forall
    M schedule index occurrence,
  nth_error schedule index = Some occurrence ->
  rawStandardFormulaOperationTargetAt M schedule index =
    rawQuotedFormulaCode M (standardOccurrenceTarget occurrence).
Proof.
  intros M schedule index occurrence hnth.
  unfold rawStandardFormulaOperationTargetAt.
  now rewrite (nth_error_nth schedule index
    standardFormulaOperationDefaultOccurrence hnth).
Qed.

Lemma rawStandardFormulaOperationDepthAt_nth_error : forall
    M schedule index occurrence,
  nth_error schedule index = Some occurrence ->
  rawStandardFormulaOperationDepthAt M schedule index =
    rawNumeralValue M (standardOccurrenceDepth occurrence).
Proof.
  intros M schedule index occurrence hnth.
  unfold rawStandardFormulaOperationDepthAt.
  now rewrite (nth_error_nth schedule index
    standardFormulaOperationDefaultOccurrence hnth).
Qed.

(** Small list lemmas used to expose the two child blocks and the final root
    without relying on any formula-code ordering. *)
Lemma nth_error_snoc_last : forall
    (A : Type) (xs : list A) (last : A),
  nth_error (xs ++ [last]) (length xs) = Some last.
Proof.
  intros A xs last.
  rewrite nth_error_app2 by lia.
  replace (length xs - length xs) with 0 by lia. reflexivity.
Qed.

Lemma nth_error_embed_left : forall
    (A : Type) (left right : list A) index value,
  nth_error left index = Some value ->
  nth_error (left ++ right) index = Some value.
Proof.
  intros A left right index value hnth.
  rewrite nth_error_app1; [exact hnth |].
  apply (proj1 (nth_error_Some left index)).
  now rewrite hnth.
Qed.

Lemma nth_error_embed_right : forall
    (A : Type) (left right : list A) index value,
  nth_error right index = Some value ->
  nth_error (left ++ right) (length left + index) = Some value.
Proof.
  intros A left right index value hnth.
  rewrite nth_error_app2 by lia.
  replace (length left + index - length left) with index by lia.
  exact hnth.
Qed.

Lemma nth_error_singleton_inv : forall (A : Type) (root value : A) index,
  nth_error [root] index = Some value -> index = 0 /\ value = root.
Proof.
  intros A root value [|index] hnth; cbn in hnth.
  - inversion hnth. tauto.
  - destruct index; discriminate.
Qed.

Lemma nth_error_unary_postorder_cases : forall
    (A : Type) (child : list A) root index value,
  nth_error (child ++ [root]) index = Some value ->
  (index < length child /\ nth_error child index = Some value) \/
  (index = length child /\ value = root).
Proof.
  intros A child root index value hnth.
  destruct (lt_dec index (length child)) as [hchild | hroot].
  - left. split; [exact hchild |].
    rewrite <- (nth_error_app1 child [root] hchild). exact hnth.
  - right.
    assert (hbound : index < length (child ++ [root])).
    {
      apply (proj1 (nth_error_Some (child ++ [root]) index)).
      now rewrite hnth.
    }
    rewrite length_app in hbound. cbn in hbound.
    assert (hindex : index = length child) by lia. subst index.
    split; [reflexivity |].
    rewrite nth_error_snoc_last in hnth. now inversion hnth.
Qed.

Lemma nth_error_binary_postorder_cases : forall
    (A : Type) (left right : list A) root index value,
  nth_error (left ++ right ++ [root]) index = Some value ->
  (index < length left /\ nth_error left index = Some value) \/
  (exists rightIndex,
      index = length left + rightIndex /\
      rightIndex < length right /\
      nth_error right rightIndex = Some value) \/
  (index = length left + length right /\ value = root).
Proof.
  intros A left right root index value hnth.
  destruct (lt_dec index (length left)) as [hleft | hnleft].
  - left. split; [exact hleft |].
    rewrite <- (nth_error_app1 left (right ++ [root]) hleft).
    exact hnth.
  - right.
    set (rightIndex := index - length left).
    destruct (lt_dec rightIndex (length right)) as [hright | hnright].
    + left. exists rightIndex. split; [unfold rightIndex; lia |].
      split; [exact hright |].
      unfold rightIndex in *.
      rewrite <- (nth_error_app1 right [root] hright).
      rewrite <- (nth_error_app2 left (right ++ [root]))
        by lia.
      exact hnth.
    + right.
      assert (hbound : index < length (left ++ right ++ [root])).
      {
        apply (proj1
          (nth_error_Some (left ++ right ++ [root]) index)).
        now rewrite hnth.
      }
      rewrite !length_app in hbound. cbn in hbound.
      assert (hindex : index = length left + length right).
      { unfold rightIndex in hnright. lia. }
      subst index. split; [reflexivity |].
      rewrite nth_error_app2 in hnth by lia.
      replace (length left + length right - length left)
        with (length right) in hnth by lia.
      rewrite nth_error_snoc_last in hnth. now inversion hnth.
Qed.

Lemma nth_error_binary_postorder_root : forall
    (A : Type) (left right : list A) root,
  nth_error (left ++ right ++ [root])
    (length left + length right) = Some root.
Proof.
  intros A left right root.
  rewrite nth_error_app2 by lia.
  replace (length left + length right - length left)
    with (length right) by lia.
  apply nth_error_snoc_last.
Qed.

Lemma standardFormulaOperationSchedule_nonempty : forall transform depth phi,
  standardFormulaOperationSchedule transform depth phi <> [].
Proof.
  intros transform depth phi.
  destruct phi; intro hempty;
    pose proof (f_equal
      (@length StandardFormulaOperationOccurrence) hempty) as hlength;
    cbn [standardFormulaOperationSchedule] in hlength;
    repeat rewrite length_app in hlength; cbn in hlength; lia.
Qed.

Lemma standardFormulaOperationSchedule_length_positive : forall
    transform depth phi,
  0 < length (standardFormulaOperationSchedule transform depth phi).
Proof.
  intros transform depth phi.
  pose proof (standardFormulaOperationSchedule_nonempty transform depth phi).
  destruct (standardFormulaOperationSchedule transform depth phi);
    cbn; [contradiction | lia].
Qed.

Lemma standardFormulaOperationSchedule_root : forall transform depth phi,
  nth_error (standardFormulaOperationSchedule transform depth phi)
    (Nat.pred (length
      (standardFormulaOperationSchedule transform depth phi))) =
  Some (standardFormulaOperationRoot transform depth phi).
Proof.
  intros transform depth phi. destruct phi; cbn [standardFormulaOperationSchedule].
  - reflexivity.
  - reflexivity.
  - rewrite !length_app. cbn.
    replace (Nat.pred
      (length (standardFormulaOperationSchedule transform depth phi1) +
       (length (standardFormulaOperationSchedule transform depth phi2) + 1)))
      with
      (length (standardFormulaOperationSchedule transform depth phi1) +
       length (standardFormulaOperationSchedule transform depth phi2)) by lia.
    apply nth_error_binary_postorder_root.
  - rewrite !length_app. cbn.
    replace (Nat.pred
      (length (standardFormulaOperationSchedule transform depth phi1) +
       (length (standardFormulaOperationSchedule transform depth phi2) + 1)))
      with
      (length (standardFormulaOperationSchedule transform depth phi1) +
       length (standardFormulaOperationSchedule transform depth phi2)) by lia.
    apply nth_error_binary_postorder_root.
  - rewrite !length_app. cbn.
    replace (Nat.pred
      (length (standardFormulaOperationSchedule transform depth phi1) +
       (length (standardFormulaOperationSchedule transform depth phi2) + 1)))
      with
      (length (standardFormulaOperationSchedule transform depth phi1) +
       length (standardFormulaOperationSchedule transform depth phi2)) by lia.
    apply nth_error_binary_postorder_root.
  - rewrite length_app. cbn.
    replace (Nat.pred
      (length (standardFormulaOperationSchedule transform (S depth) phi) + 1))
      with (length
        (standardFormulaOperationSchedule transform (S depth) phi)) by lia.
    apply nth_error_snoc_last.
  - rewrite length_app. cbn.
    replace (Nat.pred
      (length (standardFormulaOperationSchedule transform (S depth) phi) + 1))
      with (length
        (standardFormulaOperationSchedule transform (S depth) phi)) by lia.
    apply nth_error_snoc_last.
Qed.

(** Apart from equality atoms, both operations are homomorphisms for the
    formula constructors.  Keeping these equations in one record makes the
    occurrence argument independent of the particular term operation used
    at equality leaves. *)
Record StandardFormulaOperationShape
    (transform : nat -> formula -> formula) : Prop := {
  standardFormulaOperationShapeBot : forall depth,
    transform depth pBot = pBot;
  standardFormulaOperationShapeImp : forall depth lhs rhs,
    transform depth (pImp lhs rhs) =
      pImp (transform depth lhs) (transform depth rhs);
  standardFormulaOperationShapeAnd : forall depth lhs rhs,
    transform depth (pAnd lhs rhs) =
      pAnd (transform depth lhs) (transform depth rhs);
  standardFormulaOperationShapeOr : forall depth lhs rhs,
    transform depth (pOr lhs rhs) =
      pOr (transform depth lhs) (transform depth rhs);
  standardFormulaOperationShapeAll : forall depth child,
    transform depth (pAll child) =
      pAll (transform (S depth) child);
  standardFormulaOperationShapeEx : forall depth child,
    transform depth (pEx child) =
      pEx (transform (S depth) child)
}.

(** A segment lookup uses global table index [offset + index].  The offset is
    what permits the induction to descend into the right child block of a
    binary node while retaining the indices of the complete schedule. *)
Definition RawStandardFormulaOperationSegmentLookup
    (M : RawPAModel)
    (sourceCode sourceStep targetCode targetStep depthCode depthStep : M)
    (schedule : list StandardFormulaOperationOccurrence)
    (offset : nat) : Prop :=
  forall index occurrence,
    nth_error schedule index = Some occurrence ->
    RawCodedFormulaOperationTripleLookup M
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      (rawNumeralValue M (offset + index))
      (rawQuotedFormulaCode M (standardOccurrenceSource occurrence))
      (rawQuotedFormulaCode M (standardOccurrenceTarget occurrence))
      (rawNumeralValue M (standardOccurrenceDepth occurrence)).

(** Every occurrence in a postorder segment has a valid local traversal row.
    Notice that the induction is on the syntax tree, but its quantified
    [offset] follows the occurrence block through list concatenations. *)
Lemma raw_standardFormulaOperation_segment_row : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall (atom : M -> M -> M -> M -> Prop) parameter transform,
  StandardFormulaOperationShape transform ->
  (forall depth lhs rhs,
    RawCodedFormulaEqOperationRow M atom parameter
      (rawNumeralValue M depth)
      (rawQuotedFormulaCode M (pEq lhs rhs))
      (rawQuotedFormulaCode M (transform depth (pEq lhs rhs)))) ->
  forall sourceCode sourceStep targetCode targetStep depthCode depthStep
    offset depth phi,
  RawStandardFormulaOperationSegmentLookup M
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    (standardFormulaOperationSchedule transform depth phi) offset ->
  forall index occurrence,
  nth_error (standardFormulaOperationSchedule transform depth phi) index =
    Some occurrence ->
  RawCodedFormulaOperationTraversalRow M atom parameter
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    (rawNumeralValue M (offset + index))
    (rawQuotedFormulaCode M (standardOccurrenceSource occurrence))
    (rawQuotedFormulaCode M (standardOccurrenceTarget occurrence))
    (rawNumeralValue M (standardOccurrenceDepth occurrence)).
Proof.
  intros M hPA atom parameter transform
    [hbot himp hand hor hall hex] heq
    sourceCode sourceStep targetCode targetStep depthCode depthStep.
  intros offset depth phi. revert offset depth.
  induction phi as [lhs rhs | | lhs IHl rhs IHr | lhs IHl rhs IHr |
      lhs IHl rhs IHr | child IH | child IH];
    intros offset depth hlookup index occurrence hnth.
  - destruct (nth_error_singleton_inv _ _ _ _ hnth) as [-> ->].
    cbn [standardFormulaOperationRoot]. left. apply heq.
  - destruct (nth_error_singleton_inv _ _ _ _ hnth) as [-> ->].
    right. left. unfold RawCodedFormulaBotOperationRow.
    unfold standardFormulaOperationRoot; cbn.
    rewrite hbot. split; reflexivity.
  - cbn [standardFormulaOperationSchedule] in hnth, hlookup.
    unfold RawStandardFormulaOperationSegmentLookup in hlookup.
    destruct (nth_error_binary_postorder_cases _ _ _ _ _ _ hnth) as
      [[hleft hnthLeft] |
       [(rightIndex & -> & hright & hnthRight) |
        [-> ->]]].
    + apply (IHl offset depth).
      * intros local localOccurrence hlocal.
        apply hlookup.
        apply nth_error_embed_left with
          (right := standardFormulaOperationSchedule transform depth rhs ++
            [standardFormulaOperationRoot transform depth (pImp lhs rhs)]).
        exact hlocal.
      * exact hnthLeft.
    + replace
        (rawNumeralValue M
          (offset +
            (length (standardFormulaOperationSchedule transform depth lhs) +
             rightIndex)))
        with
        (rawNumeralValue M
          ((offset +
            length (standardFormulaOperationSchedule transform depth lhs)) +
           rightIndex)) by (f_equal; lia).
      apply (IHr
        (offset + length
          (standardFormulaOperationSchedule transform depth lhs)) depth).
      * intros local localOccurrence hlocal.
        specialize (hlookup
          (length (standardFormulaOperationSchedule transform depth lhs) +
            local) localOccurrence).
        assert (hembed :
          nth_error
            (standardFormulaOperationSchedule transform depth lhs ++
             standardFormulaOperationSchedule transform depth rhs ++
             [standardFormulaOperationRoot transform depth (pImp lhs rhs)])
            (length (standardFormulaOperationSchedule transform depth lhs) +
              local) = Some localOccurrence).
        {
          apply nth_error_embed_right.
          apply nth_error_embed_left with
            (right :=
              [standardFormulaOperationRoot transform depth (pImp lhs rhs)]).
          exact hlocal.
        }
        specialize (hlookup hembed).
        replace
          (offset +
            (length (standardFormulaOperationSchedule transform depth lhs) +
             local))
          with
          ((offset +
            length (standardFormulaOperationSchedule transform depth lhs)) +
           local) in hlookup by lia.
        exact hlookup.
      * exact hnthRight.
    + assert (hleftLookup :
        RawCodedFormulaOperationTripleLookup M
          sourceCode sourceStep targetCode targetStep depthCode depthStep
          (rawNumeralValue M
            (offset + Nat.pred (length
              (standardFormulaOperationSchedule transform depth lhs))))
          (rawQuotedFormulaCode M lhs)
          (rawQuotedFormulaCode M (transform depth lhs))
          (rawNumeralValue M depth)).
      {
        assert (hlocalNth :
          nth_error
            (standardFormulaOperationSchedule transform depth lhs ++
             standardFormulaOperationSchedule transform depth rhs ++
             [standardFormulaOperationRoot transform depth (pImp lhs rhs)])
            (Nat.pred (length
              (standardFormulaOperationSchedule transform depth lhs))) =
          Some (standardFormulaOperationRoot transform depth lhs)).
        {
          apply nth_error_embed_left with
            (right := standardFormulaOperationSchedule transform depth rhs ++
              [standardFormulaOperationRoot transform depth (pImp lhs rhs)]).
          apply standardFormulaOperationSchedule_root.
        }
        pose proof (hlookup _ _ hlocalNth) as hlocal.
        unfold standardFormulaOperationRoot in hlocal. cbn in hlocal.
        exact hlocal.
      }
      assert (hrightLookup :
        RawCodedFormulaOperationTripleLookup M
          sourceCode sourceStep targetCode targetStep depthCode depthStep
          (rawNumeralValue M
            (offset +
              (length (standardFormulaOperationSchedule transform depth lhs) +
               Nat.pred (length
                 (standardFormulaOperationSchedule transform depth rhs)))))
          (rawQuotedFormulaCode M rhs)
          (rawQuotedFormulaCode M (transform depth rhs))
          (rawNumeralValue M depth)).
      {
        assert (hlocalNth :
          nth_error
            (standardFormulaOperationSchedule transform depth lhs ++
             standardFormulaOperationSchedule transform depth rhs ++
             [standardFormulaOperationRoot transform depth (pImp lhs rhs)])
            (length (standardFormulaOperationSchedule transform depth lhs) +
             Nat.pred (length
               (standardFormulaOperationSchedule transform depth rhs))) =
          Some (standardFormulaOperationRoot transform depth rhs)).
        {
          apply nth_error_embed_right.
          apply nth_error_embed_left with
            (right :=
              [standardFormulaOperationRoot transform depth (pImp lhs rhs)]).
          apply standardFormulaOperationSchedule_root.
        }
        pose proof (hlookup _ _ hlocalNth) as hlocal.
        unfold standardFormulaOperationRoot in hlocal. cbn in hlocal.
        exact hlocal.
      }
      unfold standardFormulaOperationRoot; cbn. rewrite himp.
      right. right. left.
      exists
        (rawNumeralValue M
          (offset + Nat.pred (length
            (standardFormulaOperationSchedule transform depth lhs)))),
        (rawQuotedFormulaCode M lhs),
        (rawQuotedFormulaCode M (transform depth lhs)),
        (rawNumeralValue M depth),
        (rawNumeralValue M
          (offset +
            (length (standardFormulaOperationSchedule transform depth lhs) +
             Nat.pred (length
               (standardFormulaOperationSchedule transform depth rhs))))),
        (rawQuotedFormulaCode M rhs),
        (rawQuotedFormulaCode M (transform depth rhs)),
        (rawNumeralValue M depth).
      split.
      * apply raw_lt_numeralValue_of_lt; [exact hPA |].
        pose proof (standardFormulaOperationSchedule_length_positive
          transform depth lhs). lia.
      * split; [exact hleftLookup |].
        split; [reflexivity |]. split.
        -- apply raw_lt_numeralValue_of_lt; [exact hPA |].
           pose proof (standardFormulaOperationSchedule_length_positive
             transform depth rhs). lia.
        -- split; [exact hrightLookup |].
           repeat split; reflexivity.
  - cbn [standardFormulaOperationSchedule] in hnth, hlookup.
    unfold RawStandardFormulaOperationSegmentLookup in hlookup.
    destruct (nth_error_binary_postorder_cases _ _ _ _ _ _ hnth) as
      [[hleft hnthLeft] |
       [(rightIndex & -> & hright & hnthRight) |
        [-> ->]]].
    + apply (IHl offset depth).
      * intros local localOccurrence hlocal.
        apply hlookup. apply nth_error_embed_left with
          (right := standardFormulaOperationSchedule transform depth rhs ++
            [standardFormulaOperationRoot transform depth (pAnd lhs rhs)]).
        exact hlocal.
      * exact hnthLeft.
    + replace
        (rawNumeralValue M
          (offset +
            (length (standardFormulaOperationSchedule transform depth lhs) +
             rightIndex)))
        with
        (rawNumeralValue M
          ((offset +
            length (standardFormulaOperationSchedule transform depth lhs)) +
           rightIndex)) by (f_equal; lia).
      apply (IHr
        (offset + length
          (standardFormulaOperationSchedule transform depth lhs)) depth).
      * intros local localOccurrence hlocal.
        specialize (hlookup
          (length (standardFormulaOperationSchedule transform depth lhs) +
            local) localOccurrence).
        assert (hembed :
          nth_error
            (standardFormulaOperationSchedule transform depth lhs ++
             standardFormulaOperationSchedule transform depth rhs ++
             [standardFormulaOperationRoot transform depth (pAnd lhs rhs)])
            (length (standardFormulaOperationSchedule transform depth lhs) +
              local) = Some localOccurrence).
        {
          apply nth_error_embed_right.
          apply nth_error_embed_left with
            (right :=
              [standardFormulaOperationRoot transform depth (pAnd lhs rhs)]).
          exact hlocal.
        }
        specialize (hlookup hembed).
        replace
          (offset +
            (length (standardFormulaOperationSchedule transform depth lhs) +
             local))
          with
          ((offset +
            length (standardFormulaOperationSchedule transform depth lhs)) +
           local) in hlookup by lia.
        exact hlookup.
      * exact hnthRight.
    + assert (hleftLookup :
        RawCodedFormulaOperationTripleLookup M
          sourceCode sourceStep targetCode targetStep depthCode depthStep
          (rawNumeralValue M
            (offset + Nat.pred (length
              (standardFormulaOperationSchedule transform depth lhs))))
          (rawQuotedFormulaCode M lhs)
          (rawQuotedFormulaCode M (transform depth lhs))
          (rawNumeralValue M depth)).
      {
        assert (hlocalNth :
          nth_error
            (standardFormulaOperationSchedule transform depth lhs ++
             standardFormulaOperationSchedule transform depth rhs ++
             [standardFormulaOperationRoot transform depth (pAnd lhs rhs)])
            (Nat.pred (length
              (standardFormulaOperationSchedule transform depth lhs))) =
          Some (standardFormulaOperationRoot transform depth lhs)).
        {
          apply nth_error_embed_left with
            (right := standardFormulaOperationSchedule transform depth rhs ++
              [standardFormulaOperationRoot transform depth (pAnd lhs rhs)]).
          apply standardFormulaOperationSchedule_root.
        }
        pose proof (hlookup _ _ hlocalNth) as hlocal.
        unfold standardFormulaOperationRoot in hlocal. cbn in hlocal.
        exact hlocal.
      }
      assert (hrightLookup :
        RawCodedFormulaOperationTripleLookup M
          sourceCode sourceStep targetCode targetStep depthCode depthStep
          (rawNumeralValue M
            (offset +
              (length (standardFormulaOperationSchedule transform depth lhs) +
               Nat.pred (length
                 (standardFormulaOperationSchedule transform depth rhs)))))
          (rawQuotedFormulaCode M rhs)
          (rawQuotedFormulaCode M (transform depth rhs))
          (rawNumeralValue M depth)).
      {
        assert (hlocalNth :
          nth_error
            (standardFormulaOperationSchedule transform depth lhs ++
             standardFormulaOperationSchedule transform depth rhs ++
             [standardFormulaOperationRoot transform depth (pAnd lhs rhs)])
            (length (standardFormulaOperationSchedule transform depth lhs) +
             Nat.pred (length
               (standardFormulaOperationSchedule transform depth rhs))) =
          Some (standardFormulaOperationRoot transform depth rhs)).
        {
          apply nth_error_embed_right.
          apply nth_error_embed_left with
            (right :=
              [standardFormulaOperationRoot transform depth (pAnd lhs rhs)]).
          apply standardFormulaOperationSchedule_root.
        }
        pose proof (hlookup _ _ hlocalNth) as hlocal.
        unfold standardFormulaOperationRoot in hlocal. cbn in hlocal.
        exact hlocal.
      }
      unfold standardFormulaOperationRoot; cbn.
      rewrite hand. right. right. right. left.
      exists
        (rawNumeralValue M
          (offset + Nat.pred (length
            (standardFormulaOperationSchedule transform depth lhs)))),
        (rawQuotedFormulaCode M lhs),
        (rawQuotedFormulaCode M (transform depth lhs)),
        (rawNumeralValue M depth),
        (rawNumeralValue M
          (offset +
            (length (standardFormulaOperationSchedule transform depth lhs) +
             Nat.pred (length
               (standardFormulaOperationSchedule transform depth rhs))))),
        (rawQuotedFormulaCode M rhs),
        (rawQuotedFormulaCode M (transform depth rhs)),
        (rawNumeralValue M depth).
      split.
      * apply raw_lt_numeralValue_of_lt; [exact hPA |].
        pose proof (standardFormulaOperationSchedule_length_positive
          transform depth lhs). lia.
      * split; [exact hleftLookup |].
        split; [reflexivity |]. split.
        -- apply raw_lt_numeralValue_of_lt; [exact hPA |].
           pose proof (standardFormulaOperationSchedule_length_positive
             transform depth rhs). lia.
        -- split; [exact hrightLookup |].
           repeat split; reflexivity.
  - cbn [standardFormulaOperationSchedule] in hnth, hlookup.
    unfold RawStandardFormulaOperationSegmentLookup in hlookup.
    destruct (nth_error_binary_postorder_cases _ _ _ _ _ _ hnth) as
      [[hleft hnthLeft] |
       [(rightIndex & -> & hright & hnthRight) |
        [-> ->]]].
    + apply (IHl offset depth).
      * intros local localOccurrence hlocal.
        apply hlookup. apply nth_error_embed_left with
          (right := standardFormulaOperationSchedule transform depth rhs ++
            [standardFormulaOperationRoot transform depth (pOr lhs rhs)]).
        exact hlocal.
      * exact hnthLeft.
    + replace
        (rawNumeralValue M
          (offset +
            (length (standardFormulaOperationSchedule transform depth lhs) +
             rightIndex)))
        with
        (rawNumeralValue M
          ((offset +
            length (standardFormulaOperationSchedule transform depth lhs)) +
           rightIndex)) by (f_equal; lia).
      apply (IHr
        (offset + length
          (standardFormulaOperationSchedule transform depth lhs)) depth).
      * intros local localOccurrence hlocal.
        specialize (hlookup
          (length (standardFormulaOperationSchedule transform depth lhs) +
            local) localOccurrence).
        assert (hembed :
          nth_error
            (standardFormulaOperationSchedule transform depth lhs ++
             standardFormulaOperationSchedule transform depth rhs ++
             [standardFormulaOperationRoot transform depth (pOr lhs rhs)])
            (length (standardFormulaOperationSchedule transform depth lhs) +
              local) = Some localOccurrence).
        {
          apply nth_error_embed_right.
          apply nth_error_embed_left with
            (right :=
              [standardFormulaOperationRoot transform depth (pOr lhs rhs)]).
          exact hlocal.
        }
        specialize (hlookup hembed).
        replace
          (offset +
            (length (standardFormulaOperationSchedule transform depth lhs) +
             local))
          with
          ((offset +
            length (standardFormulaOperationSchedule transform depth lhs)) +
           local) in hlookup by lia.
        exact hlookup.
      * exact hnthRight.
    + assert (hleftLookup :
        RawCodedFormulaOperationTripleLookup M
          sourceCode sourceStep targetCode targetStep depthCode depthStep
          (rawNumeralValue M
            (offset + Nat.pred (length
              (standardFormulaOperationSchedule transform depth lhs))))
          (rawQuotedFormulaCode M lhs)
          (rawQuotedFormulaCode M (transform depth lhs))
          (rawNumeralValue M depth)).
      {
        assert (hlocalNth :
          nth_error
            (standardFormulaOperationSchedule transform depth lhs ++
             standardFormulaOperationSchedule transform depth rhs ++
             [standardFormulaOperationRoot transform depth (pOr lhs rhs)])
            (Nat.pred (length
              (standardFormulaOperationSchedule transform depth lhs))) =
          Some (standardFormulaOperationRoot transform depth lhs)).
        {
          apply nth_error_embed_left with
            (right := standardFormulaOperationSchedule transform depth rhs ++
              [standardFormulaOperationRoot transform depth (pOr lhs rhs)]).
          apply standardFormulaOperationSchedule_root.
        }
        pose proof (hlookup _ _ hlocalNth) as hlocal.
        unfold standardFormulaOperationRoot in hlocal. cbn in hlocal.
        exact hlocal.
      }
      assert (hrightLookup :
        RawCodedFormulaOperationTripleLookup M
          sourceCode sourceStep targetCode targetStep depthCode depthStep
          (rawNumeralValue M
            (offset +
              (length (standardFormulaOperationSchedule transform depth lhs) +
               Nat.pred (length
                 (standardFormulaOperationSchedule transform depth rhs)))))
          (rawQuotedFormulaCode M rhs)
          (rawQuotedFormulaCode M (transform depth rhs))
          (rawNumeralValue M depth)).
      {
        assert (hlocalNth :
          nth_error
            (standardFormulaOperationSchedule transform depth lhs ++
             standardFormulaOperationSchedule transform depth rhs ++
             [standardFormulaOperationRoot transform depth (pOr lhs rhs)])
            (length (standardFormulaOperationSchedule transform depth lhs) +
             Nat.pred (length
               (standardFormulaOperationSchedule transform depth rhs))) =
          Some (standardFormulaOperationRoot transform depth rhs)).
        {
          apply nth_error_embed_right.
          apply nth_error_embed_left with
            (right :=
              [standardFormulaOperationRoot transform depth (pOr lhs rhs)]).
          apply standardFormulaOperationSchedule_root.
        }
        pose proof (hlookup _ _ hlocalNth) as hlocal.
        unfold standardFormulaOperationRoot in hlocal. cbn in hlocal.
        exact hlocal.
      }
      unfold standardFormulaOperationRoot; cbn.
      rewrite hor. right. right. right. right. left.
      exists
        (rawNumeralValue M
          (offset + Nat.pred (length
            (standardFormulaOperationSchedule transform depth lhs)))),
        (rawQuotedFormulaCode M lhs),
        (rawQuotedFormulaCode M (transform depth lhs)),
        (rawNumeralValue M depth),
        (rawNumeralValue M
          (offset +
            (length (standardFormulaOperationSchedule transform depth lhs) +
             Nat.pred (length
               (standardFormulaOperationSchedule transform depth rhs))))),
        (rawQuotedFormulaCode M rhs),
        (rawQuotedFormulaCode M (transform depth rhs)),
        (rawNumeralValue M depth).
      split.
      * apply raw_lt_numeralValue_of_lt; [exact hPA |].
        pose proof (standardFormulaOperationSchedule_length_positive
          transform depth lhs). lia.
      * split; [exact hleftLookup |].
        split; [reflexivity |]. split.
        -- apply raw_lt_numeralValue_of_lt; [exact hPA |].
           pose proof (standardFormulaOperationSchedule_length_positive
             transform depth rhs). lia.
        -- split; [exact hrightLookup |].
           repeat split; reflexivity.
  - cbn [standardFormulaOperationSchedule] in hnth, hlookup.
    unfold RawStandardFormulaOperationSegmentLookup in hlookup.
    destruct (nth_error_unary_postorder_cases _ _ _ _ _ hnth) as
      [[hchild hnthChild] | [-> ->]].
    + apply (IH offset (S depth)).
      * intros local localOccurrence hlocal.
        apply hlookup.
        apply nth_error_embed_left with
          (right :=
            [standardFormulaOperationRoot transform depth (pAll child)]).
        exact hlocal.
      * exact hnthChild.
    + assert (hchildLookup :
        RawCodedFormulaOperationTripleLookup M
          sourceCode sourceStep targetCode targetStep depthCode depthStep
          (rawNumeralValue M
            (offset + Nat.pred (length
              (standardFormulaOperationSchedule transform (S depth) child))))
          (rawQuotedFormulaCode M child)
          (rawQuotedFormulaCode M (transform (S depth) child))
          (rawNumeralValue M (S depth))).
      {
        assert (hlocalNth :
          nth_error
            (standardFormulaOperationSchedule transform (S depth) child ++
             [standardFormulaOperationRoot transform depth (pAll child)])
            (Nat.pred (length
              (standardFormulaOperationSchedule transform (S depth) child))) =
          Some (standardFormulaOperationRoot transform (S depth) child)).
        {
          apply nth_error_embed_left with
            (right :=
              [standardFormulaOperationRoot transform depth (pAll child)]).
          apply standardFormulaOperationSchedule_root.
        }
        pose proof (hlookup _ _ hlocalNth) as hlocal.
        unfold standardFormulaOperationRoot in hlocal. cbn in hlocal.
        exact hlocal.
      }
      unfold standardFormulaOperationRoot; cbn. rewrite hall.
      right. right. right. right. right. left.
      exists
        (rawNumeralValue M
          (offset + Nat.pred (length
            (standardFormulaOperationSchedule transform (S depth) child)))),
        (rawQuotedFormulaCode M child),
        (rawQuotedFormulaCode M (transform (S depth) child)),
        (rawNumeralValue M (S depth)).
      split.
      * apply raw_lt_numeralValue_of_lt; [exact hPA |].
        pose proof (standardFormulaOperationSchedule_length_positive
          transform (S depth) child). lia.
      * split; [exact hchildLookup |].
        repeat split; reflexivity.
  - cbn [standardFormulaOperationSchedule] in hnth, hlookup.
    unfold RawStandardFormulaOperationSegmentLookup in hlookup.
    destruct (nth_error_unary_postorder_cases _ _ _ _ _ hnth) as
      [[hchild hnthChild] | [-> ->]].
    + apply (IH offset (S depth)).
      * intros local localOccurrence hlocal.
        apply hlookup.
        apply nth_error_embed_left with
          (right :=
            [standardFormulaOperationRoot transform depth (pEx child)]).
        exact hlocal.
      * exact hnthChild.
    + assert (hchildLookup :
        RawCodedFormulaOperationTripleLookup M
          sourceCode sourceStep targetCode targetStep depthCode depthStep
          (rawNumeralValue M
            (offset + Nat.pred (length
              (standardFormulaOperationSchedule transform (S depth) child))))
          (rawQuotedFormulaCode M child)
          (rawQuotedFormulaCode M (transform (S depth) child))
          (rawNumeralValue M (S depth))).
      {
        assert (hlocalNth :
          nth_error
            (standardFormulaOperationSchedule transform (S depth) child ++
             [standardFormulaOperationRoot transform depth (pEx child)])
            (Nat.pred (length
              (standardFormulaOperationSchedule transform (S depth) child))) =
          Some (standardFormulaOperationRoot transform (S depth) child)).
        {
          apply nth_error_embed_left with
            (right :=
              [standardFormulaOperationRoot transform depth (pEx child)]).
          apply standardFormulaOperationSchedule_root.
        }
        pose proof (hlookup _ _ hlocalNth) as hlocal.
        unfold standardFormulaOperationRoot in hlocal. cbn in hlocal.
        exact hlocal.
      }
      unfold standardFormulaOperationRoot; cbn. rewrite hex.
      right. right. right. right. right. right.
      exists
        (rawNumeralValue M
          (offset + Nat.pred (length
            (standardFormulaOperationSchedule transform (S depth) child)))),
        (rawQuotedFormulaCode M child),
        (rawQuotedFormulaCode M (transform (S depth) child)),
        (rawNumeralValue M (S depth)).
      split.
      * apply raw_lt_numeralValue_of_lt; [exact hPA |].
        pose proof (standardFormulaOperationSchedule_length_positive
          transform (S depth) child). lia.
      * split; [exact hchildLookup |].
        repeat split; reflexivity.
Qed.

(** Finite beta realization packages the occurrence-row lemma as an actual
    witness for the public raw operation graph. *)
Theorem raw_standardFormulaOperation_realization : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall (atom : M -> M -> M -> M -> Prop) parameter transform,
  StandardFormulaOperationShape transform ->
  (forall depth lhs rhs,
    RawCodedFormulaEqOperationRow M atom parameter
      (rawNumeralValue M depth)
      (rawQuotedFormulaCode M (pEq lhs rhs))
      (rawQuotedFormulaCode M (transform depth (pEq lhs rhs)))) ->
  forall depth root,
  RawCodedFormulaOperation M atom parameter
    (rawNumeralValue M depth)
    (rawQuotedFormulaCode M root)
    (rawQuotedFormulaCode M (transform depth root)).
Proof.
  intros M hPA atom parameter transform hshape heq depth root.
  set (schedule := standardFormulaOperationSchedule transform depth root).
  set (limit := length schedule).
  assert (hlimitPositive : 0 < limit).
  {
    unfold limit, schedule.
    apply standardFormulaOperationSchedule_length_positive.
  }
  destruct (finite_vector_beta_code M hPA limit
    (rawStandardFormulaOperationSourceAt M schedule)) as
    [sourceCode [sourceStep hsource]].
  destruct (finite_vector_beta_code M hPA limit
    (rawStandardFormulaOperationTargetAt M schedule)) as
    [targetCode [targetStep htarget]].
  destruct (finite_vector_beta_code M hPA limit
    (rawStandardFormulaOperationDepthAt M schedule)) as
    [depthCode [depthStep hdepth]].
  assert (hscheduleLookup : forall index occurrence,
    nth_error schedule index = Some occurrence ->
    RawCodedFormulaOperationTripleLookup M
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      (rawNumeralValue M index)
      (rawQuotedFormulaCode M (standardOccurrenceSource occurrence))
      (rawQuotedFormulaCode M (standardOccurrenceTarget occurrence))
      (rawNumeralValue M (standardOccurrenceDepth occurrence))).
  {
    intros index occurrence hnth.
    assert (hindex : index < limit).
    {
      unfold limit. apply (proj1 (nth_error_Some schedule index)).
      now rewrite hnth.
    }
    split.
    - rewrite <- (rawStandardFormulaOperationSourceAt_nth_error
        M schedule index occurrence hnth).
      apply hsource. exact hindex.
    - split.
      + rewrite <- (rawStandardFormulaOperationTargetAt_nth_error
          M schedule index occurrence hnth).
        apply htarget. exact hindex.
      + rewrite <- (rawStandardFormulaOperationDepthAt_nth_error
          M schedule index occurrence hnth).
        apply hdepth. exact hindex.
  }
  exists sourceCode, sourceStep, targetCode, targetStep,
    depthCode, depthStep, (rawNumeralValue M limit),
    (rawNumeralValue M (Nat.pred limit)).
  unfold RawCodedFormulaOperationTrace.
  split.
  - intros index hindex.
    destruct (raw_lt_numeralValue_cases M hPA index limit hindex)
      as [k [hk ->]].
    exists (rawStandardFormulaOperationSourceAt M schedule k).
    apply hsource. exact hk.
  - split.
    + intros index hindex.
      destruct (raw_lt_numeralValue_cases M hPA index limit hindex)
        as [k [hk ->]].
      exists (rawStandardFormulaOperationTargetAt M schedule k).
      apply htarget. exact hk.
    + split.
      * intros index hindex.
        destruct (raw_lt_numeralValue_cases M hPA index limit hindex)
          as [k [hk ->]].
        exists (rawStandardFormulaOperationDepthAt M schedule k).
        apply hdepth. exact hk.
      * split.
        -- apply raw_lt_numeralValue_of_lt; [exact hPA | lia].
        -- split.
           ++ assert (hrootNth :
                nth_error schedule (Nat.pred limit) =
                  Some (standardFormulaOperationRoot transform depth root)).
              {
                unfold schedule, limit.
                apply standardFormulaOperationSchedule_root.
              }
              pose proof (hscheduleLookup _ _ hrootNth) as hrootLookup.
              unfold standardFormulaOperationRoot in hrootLookup.
              cbn in hrootLookup. exact hrootLookup.
           ++ intros index input output rowDepth hindex htriple.
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
                  rawQuotedFormulaCode M
                    (standardOccurrenceSource occurrence)).
              {
                exact (raw_codedAssignmentLookup_functional M hPA
                  sourceCode sourceStep (rawNumeralValue M k) input
                  (rawQuotedFormulaCode M
                    (standardOccurrenceSource occurrence))
                  hinput hsourceCanonical).
              }
              assert (houtputEq : output =
                  rawQuotedFormulaCode M
                    (standardOccurrenceTarget occurrence)).
              {
                exact (raw_codedAssignmentLookup_functional M hPA
                  targetCode targetStep (rawNumeralValue M k) output
                  (rawQuotedFormulaCode M
                    (standardOccurrenceTarget occurrence))
                  houtput htargetCanonical).
              }
              assert (hdepthEq : rowDepth =
                  rawNumeralValue M
                    (standardOccurrenceDepth occurrence)).
              {
                exact (raw_codedAssignmentLookup_functional M hPA
                  depthCode depthStep (rawNumeralValue M k) rowDepth
                  (rawNumeralValue M
                    (standardOccurrenceDepth occurrence))
                  hrowDepth hdepthCanonical).
              }
              subst input. subst output. subst rowDepth.
              apply (raw_standardFormulaOperation_segment_row M hPA
                atom parameter transform hshape heq
                sourceCode sourceStep targetCode targetStep
                depthCode depthStep 0 depth root).
              { (** The complete schedule is the segment at offset zero. *)
                unfold RawStandardFormulaOperationSegmentLookup.
                intros local localOccurrence hlocal.
                cbn. apply hscheduleLookup. exact hlocal. }
              exact hnth.
Qed.

(** The two concrete transformations satisfy the constructor equations used
    by the generic occurrence proof. *)
Lemma standardFormulaShift_operation_shape : forall amount,
  StandardFormulaOperationShape
    (fun depth phi => standardFormulaShift depth amount phi).
Proof.
  intro amount. constructor; intros; reflexivity.
Qed.

Lemma standardFormulaSingleSubstitution_operation_shape : forall replacement,
  StandardFormulaOperationShape
    (fun depth phi =>
      standardFormulaSingleSubstitution replacement depth phi).
Proof.
  intro replacement. constructor; intros; reflexivity.
Qed.

Lemma raw_standardFormulaShift_eq_row : forall
    (M : RawPAModel), RawPASatisfies M -> forall amount depth lhs rhs,
  RawCodedFormulaEqOperationRow M (RawCodedFormulaShiftAtom M)
    (rawNumeralValue M amount) (rawNumeralValue M depth)
    (rawQuotedFormulaCode M (pEq lhs rhs))
    (rawQuotedFormulaCode M
      (standardFormulaShift depth amount (pEq lhs rhs))).
Proof.
  intros M hPA amount depth lhs rhs.
  exists
    (rawQuotedTermCode M lhs),
    (rawQuotedTermCode M (standardTermShift depth amount lhs)),
    (rawQuotedTermCode M rhs),
    (rawQuotedTermCode M (standardTermShift depth amount rhs)).
  split; [reflexivity |]. split; [reflexivity |]. split.
  - apply raw_standardFormulaShift_atom. exact hPA.
  - apply raw_standardFormulaShift_atom. exact hPA.
Qed.

Lemma raw_standardFormulaSingleSubstitution_eq_row : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall replacement depth lhs rhs,
  RawCodedFormulaEqOperationRow M (RawCodedFormulaSubstitutionAtom M)
    (rawQuotedTermCode M replacement) (rawNumeralValue M depth)
    (rawQuotedFormulaCode M (pEq lhs rhs))
    (rawQuotedFormulaCode M
      (standardFormulaSingleSubstitution replacement depth (pEq lhs rhs))).
Proof.
  intros M hPA replacement depth lhs rhs.
  exists
    (rawQuotedTermCode M lhs),
    (rawQuotedTermCode M
      (standardTermOpening depth
        (standardTermShift 0 depth replacement) lhs)),
    (rawQuotedTermCode M rhs),
    (rawQuotedTermCode M
      (standardTermOpening depth
        (standardTermShift 0 depth replacement) rhs)).
  split; [reflexivity |]. split; [reflexivity |]. split.
  - apply raw_standardFormulaSubstitution_atom. exact hPA.
  - apply raw_standardFormulaSubstitution_atom. exact hPA.
Qed.

(** Full standard quotation theorem for formula shifting. *)
Theorem raw_codedFormulaShift_standard : forall
    (M : RawPAModel), RawPASatisfies M -> forall cutoff amount phi,
  RawCodedFormulaShift M
    (rawNumeralValue M cutoff) (rawNumeralValue M amount)
    (rawQuotedFormulaCode M phi)
    (rawQuotedFormulaCode M (standardFormulaShift cutoff amount phi)).
Proof.
  intros M hPA cutoff amount phi.
  unfold RawCodedFormulaShift.
  apply (raw_standardFormulaOperation_realization M hPA
    (RawCodedFormulaShiftAtom M) (rawNumeralValue M amount)
    (fun depth psi => standardFormulaShift depth amount psi)).
  - apply standardFormulaShift_operation_shape.
  - intros depth lhs rhs.
    apply raw_standardFormulaShift_eq_row. exact hPA.
Qed.

Corollary raw_codedFormulaShift_standard_rename : forall
    (M : RawPAModel), RawPASatisfies M -> forall cutoff amount phi,
  RawCodedFormulaShift M
    (rawNumeralValue M cutoff) (rawNumeralValue M amount)
    (rawQuotedFormulaCode M phi)
    (rawQuotedFormulaCode M
      (Formula.rename (standardShiftRenaming cutoff amount) phi)).
Proof.
  intros M hPA cutoff amount phi.
  rewrite <- standardFormulaShift_as_rename.
  apply raw_codedFormulaShift_standard. exact hPA.
Qed.

Corollary raw_codedFormulaShift_standard_zero_one : forall
    (M : RawPAModel), RawPASatisfies M -> forall phi,
  RawCodedFormulaShift M
    (raw_zero M) (rawNumeralValue M 1)
    (rawQuotedFormulaCode M phi)
    (rawQuotedFormulaCode M (Formula.rename S phi)).
Proof.
  intros M hPA phi.
  change (RawCodedFormulaShift M
    (rawNumeralValue M 0) (rawNumeralValue M 1)
    (rawQuotedFormulaCode M phi)
    (rawQuotedFormulaCode M (Formula.rename S phi))).
  rewrite <- standardFormulaShift_zero_one.
  apply raw_codedFormulaShift_standard. exact hPA.
Qed.

(** The depth-indexed realization is useful independently of the public
    single-substitution graph, whose root depth is fixed to zero. *)
Theorem raw_standardFormulaSingleSubstitution_at : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall replacement depth phi,
  RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
    (rawQuotedTermCode M replacement) (rawNumeralValue M depth)
    (rawQuotedFormulaCode M phi)
    (rawQuotedFormulaCode M
      (standardFormulaSingleSubstitution replacement depth phi)).
Proof.
  intros M hPA replacement depth phi.
  apply (raw_standardFormulaOperation_realization M hPA
    (RawCodedFormulaSubstitutionAtom M)
    (rawQuotedTermCode M replacement)
    (fun current psi =>
      standardFormulaSingleSubstitution replacement current psi)).
  - apply standardFormulaSingleSubstitution_operation_shape.
  - intros current lhs rhs.
    apply raw_standardFormulaSingleSubstitution_eq_row. exact hPA.
Qed.

Corollary raw_codedFormulaSingleSubstitution_standard_recursive : forall
    (M : RawPAModel), RawPASatisfies M -> forall replacement phi,
  RawCodedFormulaSingleSubstitution M
    (rawQuotedTermCode M replacement)
    (rawQuotedFormulaCode M phi)
    (rawQuotedFormulaCode M
      (standardFormulaSingleSubstitution replacement 0 phi)).
Proof.
  intros M hPA replacement phi.
  unfold RawCodedFormulaSingleSubstitution.
  change (RawCodedFormulaOperation M
    (RawCodedFormulaSubstitutionAtom M)
    (rawQuotedTermCode M replacement) (rawNumeralValue M 0)
    (rawQuotedFormulaCode M phi)
    (rawQuotedFormulaCode M
      (standardFormulaSingleSubstitution replacement 0 phi))).
  apply raw_standardFormulaSingleSubstitution_at. exact hPA.
Qed.

(** In the standard syntax library the operation is ordinary capture-avoiding
    substitution by [Formula.instTerm replacement]. *)
Theorem raw_codedFormulaSingleSubstitution_standard : forall
    (M : RawPAModel), RawPASatisfies M -> forall replacement phi,
  RawCodedFormulaSingleSubstitution M
    (rawQuotedTermCode M replacement)
    (rawQuotedFormulaCode M phi)
    (rawQuotedFormulaCode M
      (Formula.subst (Formula.instTerm replacement) phi)).
Proof.
  intros M hPA replacement phi.
  rewrite <- standardFormulaSingleSubstitution_zero.
  apply raw_codedFormulaSingleSubstitution_standard_recursive. exact hPA.
Qed.

End PABoundedRawCodedFormulaOperationsStandardRealization.
