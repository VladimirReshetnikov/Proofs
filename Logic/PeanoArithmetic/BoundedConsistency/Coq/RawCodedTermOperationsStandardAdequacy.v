(**
  Standard-quotation adequacy for the transparent coded term operations.

  [RawCodedFormulaOperations] deliberately defines shifting and opening by
  beta-coded traversals: that definition continues to make sense for a term
  code belonging to a nonstandard PA model.  The present file proves the
  complementary, external quotation theorem.  If the input is the canonical
  code of an ordinary Rocq term, finite beta realization supplies a traversal
  whose output is the canonical code of the expected shifted/opened term.

  The tables below are indexed by *all* standard numbers below the root
  bound.  At malformed or noncanonical slots we put [tZero] in both tables.
  This small choice is important: the operation traversal asks for a closed
  row at every table entry, not merely at entries marked by a separate syntax
  support table.  Zero gives an honest harmless row at every unused slot.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax RawCodedSyntaxConstructors RawCodedAssignment
  RawCodedFormulaRankStep RawCodedTermEvaluationStandardAdequacy
  RawCodedFormulaOperations.

Import ListNotations.

Module PABoundedRawCodedTermOperationsStandardAdequacy.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFormulaRankStep.
Import PABoundedRawCodedTermEvaluationStandardAdequacy.
Import PABoundedRawCodedFormulaOperations.

(** The metatheoretic operations mirrored by the two transparent graphs.
    Both recurse only through an ordinary typed term; no model element is
    decoded here. *)
Fixpoint standardTermShift (cutoff amount : nat) (t : term) : term :=
  match t with
  | tVar index =>
      if index <? cutoff then tVar index else tVar (index + amount)
  | tZero => tZero
  | tSucc child => tSucc (standardTermShift cutoff amount child)
  | tAdd lhs rhs =>
      tAdd (standardTermShift cutoff amount lhs)
        (standardTermShift cutoff amount rhs)
  | tMul lhs rhs =>
      tMul (standardTermShift cutoff amount lhs)
        (standardTermShift cutoff amount rhs)
  end.

Fixpoint standardTermOpening
    (cutoff : nat) (replacement : term) (t : term) : term :=
  match t with
  | tVar index =>
      if index <? cutoff then tVar index
      else if index =? cutoff then replacement else tVar (Nat.pred index)
  | tZero => tZero
  | tSucc child => tSucc (standardTermOpening cutoff replacement child)
  | tAdd lhs rhs =>
      tAdd (standardTermOpening cutoff replacement lhs)
        (standardTermOpening cutoff replacement rhs)
  | tMul lhs rhs =>
      tMul (standardTermOpening cutoff replacement lhs)
        (standardTermOpening cutoff replacement rhs)
  end.

(** At cutoff zero, shifting by one is precisely the ordinary de Bruijn
    renaming used by universal introduction. *)
Lemma standardTermShift_zero_one : forall t,
  standardTermShift 0 1 t = Term.rename S t.
Proof.
  induction t as [index | | child IH | left IHl right IHr |
      left IHl right IHr]; cbn [standardTermShift Term.rename].
  - now rewrite Nat.add_1_r.
  - reflexivity.
  - now rewrite IH.
  - now rewrite IHl, IHr.
  - now rewrite IHl, IHr.
Qed.

(** Canonical standard vectors.  [checkedDecodeTerm] rejects a decoder result
    unless re-encoding gives the table index, preventing a malformed number
    from borrowing the row of some unrelated term. *)
Definition rawStandardTermOperationSourceAt
    (M : RawPAModel) (code : nat) : M :=
  match checkedDecodeTerm code with
  | Some t => rawQuotedTermCode M t
  | None => rawTermZeroCode M
  end.

Definition rawStandardTermShiftTargetAt (M : RawPAModel)
    (cutoff amount code : nat) : M :=
  match checkedDecodeTerm code with
  | Some t => rawQuotedTermCode M (standardTermShift cutoff amount t)
  | None => rawTermZeroCode M
  end.

Definition rawStandardTermOpeningTargetAt (M : RawPAModel)
    (cutoff : nat) (replacement : term) (code : nat) : M :=
  match checkedDecodeTerm code with
  | Some t =>
      rawQuotedTermCode M (standardTermOpening cutoff replacement t)
  | None => rawTermZeroCode M
  end.

Lemma rawStandardTermOperationSourceAt_termCode : forall M t,
  rawStandardTermOperationSourceAt M (termCode t) =
  rawQuotedTermCode M t.
Proof.
  intros M t. unfold rawStandardTermOperationSourceAt.
  now rewrite checkedDecodeTerm_termCode.
Qed.

Lemma rawStandardTermShiftTargetAt_termCode : forall M cutoff amount t,
  rawStandardTermShiftTargetAt M cutoff amount (termCode t) =
  rawQuotedTermCode M (standardTermShift cutoff amount t).
Proof.
  intros M cutoff amount t. unfold rawStandardTermShiftTargetAt.
  now rewrite checkedDecodeTerm_termCode.
Qed.

Lemma rawStandardTermOpeningTargetAt_termCode :
  forall M cutoff replacement t,
  rawStandardTermOpeningTargetAt M cutoff replacement (termCode t) =
  rawQuotedTermCode M (standardTermOpening cutoff replacement t).
Proof.
  intros M cutoff replacement t.
  unfold rawStandardTermOpeningTargetAt.
  now rewrite checkedDecodeTerm_termCode.
Qed.

(** A standard typed term receives the expected local shifting row whenever
    the two supplied tables contain their canonical vector entries. *)
Lemma raw_standardTermShift_closed_step : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    cutoff amount limit sourceCode sourceStep targetCode targetStep,
  (forall code, code < limit ->
    RawCodedAssignmentLookup M sourceCode sourceStep
      (rawNumeralValue M code)
      (rawStandardTermOperationSourceAt M code)) ->
  (forall code, code < limit ->
    RawCodedAssignmentLookup M targetCode targetStep
      (rawNumeralValue M code)
      (rawStandardTermShiftTargetAt M cutoff amount code)) ->
  forall t, termCode t < limit ->
  RawCodedTermShiftTraversalRow M
    (rawNumeralValue M cutoff) (rawNumeralValue M amount)
    sourceCode sourceStep targetCode targetStep
    (rawNumeralValue M (termCode t))
    (rawQuotedTermCode M t)
    (rawQuotedTermCode M (standardTermShift cutoff amount t)).
Proof.
  intros M hPA cutoff amount limit sourceCode sourceStep
    targetCode targetStep hsource htarget t ht.
  destruct t as [index | | child | left right | left right].
  - destruct (index <? cutoff) eqn:hindex.
    + left. exists (rawNumeralValue M index), (rawNumeralValue M index).
      split; [reflexivity |]. split.
      * cbn [standardTermShift]. now rewrite hindex.
      * unfold RawShiftedIndex. left. split; [|reflexivity].
        apply raw_lt_numeralValue_of_lt; [exact hPA |].
        now apply Nat.ltb_lt.
    + left. exists (rawNumeralValue M index),
        (rawNumeralValue M (index + amount)).
      split; [reflexivity |]. split.
      * cbn [standardTermShift]. now rewrite hindex.
      * unfold RawShiftedIndex. right. split.
        -- apply rawLe_numerals_of_le; [exact hPA |].
           apply Nat.ltb_ge in hindex. exact hindex.
        -- rewrite raw_add_numeral_values_syntax by exact hPA.
           reflexivity.
  - right. left. split; reflexivity.
  - right. right. left.
    exists (rawNumeralValue M (termCode child)),
      (rawQuotedTermCode M child),
      (rawQuotedTermCode M (standardTermShift cutoff amount child)).
    split.
    + apply raw_lt_numeralValue_of_lt; [exact hPA |].
      apply termCode_succ_child_lt.
    + split.
      * split.
        -- rewrite <- rawStandardTermOperationSourceAt_termCode.
           apply hsource. pose proof (termCode_succ_child_lt child). lia.
        -- rewrite <- rawStandardTermShiftTargetAt_termCode.
           apply htarget. pose proof (termCode_succ_child_lt child). lia.
      * split; reflexivity.
  - right. right. right. left.
    exists (rawNumeralValue M (termCode left)),
      (rawQuotedTermCode M left),
      (rawQuotedTermCode M (standardTermShift cutoff amount left)),
      (rawNumeralValue M (termCode right)),
      (rawQuotedTermCode M right),
      (rawQuotedTermCode M (standardTermShift cutoff amount right)).
    repeat split.
    + apply raw_lt_numeralValue_of_lt; [exact hPA |].
      apply termCode_add_left_lt.
    + rewrite <- rawStandardTermOperationSourceAt_termCode.
      apply hsource. pose proof (termCode_add_left_lt left right). lia.
    + rewrite <- rawStandardTermShiftTargetAt_termCode.
      apply htarget. pose proof (termCode_add_left_lt left right). lia.
    + apply raw_lt_numeralValue_of_lt; [exact hPA |].
      apply termCode_add_right_lt.
    + rewrite <- rawStandardTermOperationSourceAt_termCode.
      apply hsource. pose proof (termCode_add_right_lt left right). lia.
    + rewrite <- rawStandardTermShiftTargetAt_termCode.
      apply htarget. pose proof (termCode_add_right_lt left right). lia.
  - right. right. right. right.
    exists (rawNumeralValue M (termCode left)),
      (rawQuotedTermCode M left),
      (rawQuotedTermCode M (standardTermShift cutoff amount left)),
      (rawNumeralValue M (termCode right)),
      (rawQuotedTermCode M right),
      (rawQuotedTermCode M (standardTermShift cutoff amount right)).
    repeat split.
    + apply raw_lt_numeralValue_of_lt; [exact hPA |].
      apply termCode_mul_left_lt.
    + rewrite <- rawStandardTermOperationSourceAt_termCode.
      apply hsource. pose proof (termCode_mul_left_lt left right). lia.
    + rewrite <- rawStandardTermShiftTargetAt_termCode.
      apply htarget. pose proof (termCode_mul_left_lt left right). lia.
    + apply raw_lt_numeralValue_of_lt; [exact hPA |].
      apply termCode_mul_right_lt.
    + rewrite <- rawStandardTermOperationSourceAt_termCode.
      apply hsource. pose proof (termCode_mul_right_lt left right). lia.
    + rewrite <- rawStandardTermShiftTargetAt_termCode.
      apply htarget. pose proof (termCode_mul_right_lt left right). lia.
Qed.

(** The analogous local theorem for opening.  The high-variable case records
    the predecessor explicitly, matching the arithmetic graph rather than
    relying on subtraction inside the object language. *)
Lemma raw_standardTermOpening_closed_step : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    cutoff replacement limit sourceCode sourceStep targetCode targetStep,
  (forall code, code < limit ->
    RawCodedAssignmentLookup M sourceCode sourceStep
      (rawNumeralValue M code)
      (rawStandardTermOperationSourceAt M code)) ->
  (forall code, code < limit ->
    RawCodedAssignmentLookup M targetCode targetStep
      (rawNumeralValue M code)
      (rawStandardTermOpeningTargetAt M cutoff replacement code)) ->
  forall t, termCode t < limit ->
  RawCodedTermOpeningTraversalRow M
    (rawNumeralValue M cutoff) (rawQuotedTermCode M replacement)
    sourceCode sourceStep targetCode targetStep
    (rawNumeralValue M (termCode t))
    (rawQuotedTermCode M t)
    (rawQuotedTermCode M
      (standardTermOpening cutoff replacement t)).
Proof.
  intros M hPA cutoff replacement limit sourceCode sourceStep
    targetCode targetStep hsource htarget t ht.
  destruct t as [index | | child | left right | left right].
  - left. exists (rawNumeralValue M index). split; [reflexivity |].
    cbn [standardTermOpening].
    destruct (index <? cutoff) eqn:hlow.
    + left. split.
      * apply raw_lt_numeralValue_of_lt; [exact hPA |].
        now apply Nat.ltb_lt.
      * reflexivity.
    + apply Nat.ltb_ge in hlow.
      destruct (index =? cutoff) eqn:heq.
      * right. left. split.
        -- apply Nat.eqb_eq in heq. subst index. reflexivity.
        -- reflexivity.
      * right. right.
        apply Nat.eqb_neq in heq.
        exists (rawNumeralValue M (Nat.pred index)).
        split.
        -- assert (hpositive : 0 < index) by lia.
           rewrite <- (Nat.succ_pred_pos index hpositive). reflexivity.
        -- split.
           ++ apply raw_lt_numeralValue_of_lt; [exact hPA | lia].
           ++ reflexivity.
  - right. left. split; reflexivity.
  - right. right. left.
    exists (rawNumeralValue M (termCode child)),
      (rawQuotedTermCode M child),
      (rawQuotedTermCode M
        (standardTermOpening cutoff replacement child)).
    split.
    + apply raw_lt_numeralValue_of_lt; [exact hPA |].
      apply termCode_succ_child_lt.
    + split.
      * split.
        -- rewrite <- rawStandardTermOperationSourceAt_termCode.
           apply hsource. pose proof (termCode_succ_child_lt child). lia.
        -- rewrite <- rawStandardTermOpeningTargetAt_termCode.
           apply htarget. pose proof (termCode_succ_child_lt child). lia.
      * split; reflexivity.
  - right. right. right. left.
    exists (rawNumeralValue M (termCode left)),
      (rawQuotedTermCode M left),
      (rawQuotedTermCode M
        (standardTermOpening cutoff replacement left)),
      (rawNumeralValue M (termCode right)),
      (rawQuotedTermCode M right),
      (rawQuotedTermCode M
        (standardTermOpening cutoff replacement right)).
    repeat split.
    + apply raw_lt_numeralValue_of_lt; [exact hPA |].
      apply termCode_add_left_lt.
    + rewrite <- rawStandardTermOperationSourceAt_termCode.
      apply hsource. pose proof (termCode_add_left_lt left right). lia.
    + rewrite <- rawStandardTermOpeningTargetAt_termCode.
      apply htarget. pose proof (termCode_add_left_lt left right). lia.
    + apply raw_lt_numeralValue_of_lt; [exact hPA |].
      apply termCode_add_right_lt.
    + rewrite <- rawStandardTermOperationSourceAt_termCode.
      apply hsource. pose proof (termCode_add_right_lt left right). lia.
    + rewrite <- rawStandardTermOpeningTargetAt_termCode.
      apply htarget. pose proof (termCode_add_right_lt left right). lia.
  - right. right. right. right.
    exists (rawNumeralValue M (termCode left)),
      (rawQuotedTermCode M left),
      (rawQuotedTermCode M
        (standardTermOpening cutoff replacement left)),
      (rawNumeralValue M (termCode right)),
      (rawQuotedTermCode M right),
      (rawQuotedTermCode M
        (standardTermOpening cutoff replacement right)).
    repeat split.
    + apply raw_lt_numeralValue_of_lt; [exact hPA |].
      apply termCode_mul_left_lt.
    + rewrite <- rawStandardTermOperationSourceAt_termCode.
      apply hsource. pose proof (termCode_mul_left_lt left right). lia.
    + rewrite <- rawStandardTermOpeningTargetAt_termCode.
      apply htarget. pose proof (termCode_mul_left_lt left right). lia.
    + apply raw_lt_numeralValue_of_lt; [exact hPA |].
      apply termCode_mul_right_lt.
    + rewrite <- rawStandardTermOperationSourceAt_termCode.
      apply hsource. pose proof (termCode_mul_right_lt left right). lia.
    + rewrite <- rawStandardTermOpeningTargetAt_termCode.
      apply htarget. pose proof (termCode_mul_right_lt left right). lia.
Qed.

(** Finite beta realization of a complete standard shifting trace. *)
Theorem raw_codedTermShift_standard : forall
    (M : RawPAModel), RawPASatisfies M -> forall cutoff amount t,
  RawCodedTermShift M
    (rawNumeralValue M cutoff) (rawNumeralValue M amount)
    (rawQuotedTermCode M t)
    (rawQuotedTermCode M (standardTermShift cutoff amount t)).
Proof.
  intros M hPA cutoff amount root.
  set (limit := S (termCode root)).
  destruct (finite_vector_beta_code M hPA limit
    (rawStandardTermOperationSourceAt M)) as
    [sourceCode [sourceStep hsource]].
  destruct (finite_vector_beta_code M hPA limit
    (rawStandardTermShiftTargetAt M cutoff amount)) as
    [targetCode [targetStep htarget]].
  exists sourceCode, sourceStep, targetCode, targetStep,
    (rawNumeralValue M limit), (rawNumeralValue M (termCode root)).
  unfold RawCodedTermShiftTrace.
  repeat split.
  - intros index hindex.
    destruct (raw_lt_numeralValue_cases M hPA index limit hindex)
      as [k [hk ->]].
    exists (rawStandardTermOperationSourceAt M k). exact (hsource k hk).
  - intros index hindex.
    destruct (raw_lt_numeralValue_cases M hPA index limit hindex)
      as [k [hk ->]].
    exists (rawStandardTermShiftTargetAt M cutoff amount k).
    exact (htarget k hk).
  - apply raw_lt_numeralValue_of_lt; [exact hPA |].
    unfold limit. lia.
  - rewrite <- rawStandardTermOperationSourceAt_termCode.
    apply hsource. unfold limit. lia.
  - rewrite <- rawStandardTermShiftTargetAt_termCode.
    apply htarget. unfold limit. lia.
  - intros index input output hindex [hinput houtput].
    destruct (raw_lt_numeralValue_cases M hPA index limit hindex)
      as [k [hk ->]].
    assert (hsourceCanonical : input =
        rawStandardTermOperationSourceAt M k).
    {
      exact (raw_codedAssignmentLookup_functional M hPA
        sourceCode sourceStep (rawNumeralValue M k) input
        (rawStandardTermOperationSourceAt M k)
        hinput (hsource k hk)).
    }
    assert (htargetCanonical : output =
        rawStandardTermShiftTargetAt M cutoff amount k).
    {
      exact (raw_codedAssignmentLookup_functional M hPA
        targetCode targetStep (rawNumeralValue M k) output
        (rawStandardTermShiftTargetAt M cutoff amount k)
        houtput (htarget k hk)).
    }
    subst input. subst output.
    destruct (checkedDecodeTerm k) as [decoded |] eqn:hdecoded.
    + pose proof (checkedDecodeTerm_sound k decoded hdecoded)
        as [_ hcanonical].
      unfold rawStandardTermOperationSourceAt,
        rawStandardTermShiftTargetAt.
      rewrite hdecoded. rewrite <- hcanonical.
      apply (raw_standardTermShift_closed_step M hPA cutoff amount limit
        sourceCode sourceStep targetCode targetStep hsource htarget).
      now rewrite hcanonical.
    + unfold rawStandardTermOperationSourceAt,
        rawStandardTermShiftTargetAt.
      rewrite hdecoded. right. left. split; reflexivity.
  - change (rawLe M (rawNumeralValue M 0) (rawNumeralValue M cutoff)).
    apply rawLe_numerals_of_le; [exact hPA | lia].
Qed.

(** Finite beta realization of a complete standard opening trace. *)
Theorem raw_codedTermOpening_standard : forall
    (M : RawPAModel), RawPASatisfies M -> forall cutoff replacement t,
  RawCodedTermOpening M
    (rawNumeralValue M cutoff) (rawQuotedTermCode M replacement)
    (rawQuotedTermCode M t)
    (rawQuotedTermCode M
      (standardTermOpening cutoff replacement t)).
Proof.
  intros M hPA cutoff replacement root.
  set (limit := S (termCode root)).
  destruct (finite_vector_beta_code M hPA limit
    (rawStandardTermOperationSourceAt M)) as
    [sourceCode [sourceStep hsource]].
  destruct (finite_vector_beta_code M hPA limit
    (rawStandardTermOpeningTargetAt M cutoff replacement)) as
    [targetCode [targetStep htarget]].
  exists sourceCode, sourceStep, targetCode, targetStep,
    (rawNumeralValue M limit), (rawNumeralValue M (termCode root)).
  unfold RawCodedTermOpeningTrace.
  repeat split.
  - intros index hindex.
    destruct (raw_lt_numeralValue_cases M hPA index limit hindex)
      as [k [hk ->]].
    exists (rawStandardTermOperationSourceAt M k). exact (hsource k hk).
  - intros index hindex.
    destruct (raw_lt_numeralValue_cases M hPA index limit hindex)
      as [k [hk ->]].
    exists (rawStandardTermOpeningTargetAt M cutoff replacement k).
    exact (htarget k hk).
  - apply raw_lt_numeralValue_of_lt; [exact hPA |].
    unfold limit. lia.
  - rewrite <- rawStandardTermOperationSourceAt_termCode.
    apply hsource. unfold limit. lia.
  - rewrite <- rawStandardTermOpeningTargetAt_termCode.
    apply htarget. unfold limit. lia.
  - intros index input output hindex [hinput houtput].
    destruct (raw_lt_numeralValue_cases M hPA index limit hindex)
      as [k [hk ->]].
    assert (hsourceCanonical : input =
        rawStandardTermOperationSourceAt M k).
    {
      exact (raw_codedAssignmentLookup_functional M hPA
        sourceCode sourceStep (rawNumeralValue M k) input
        (rawStandardTermOperationSourceAt M k)
        hinput (hsource k hk)).
    }
    assert (htargetCanonical : output =
        rawStandardTermOpeningTargetAt M cutoff replacement k).
    {
      exact (raw_codedAssignmentLookup_functional M hPA
        targetCode targetStep (rawNumeralValue M k) output
        (rawStandardTermOpeningTargetAt M cutoff replacement k)
        houtput (htarget k hk)).
    }
    subst input. subst output.
    destruct (checkedDecodeTerm k) as [decoded |] eqn:hdecoded.
    + pose proof (checkedDecodeTerm_sound k decoded hdecoded)
        as [_ hcanonical].
      unfold rawStandardTermOperationSourceAt,
        rawStandardTermOpeningTargetAt.
      rewrite hdecoded. rewrite <- hcanonical.
      apply (raw_standardTermOpening_closed_step M hPA cutoff replacement
        limit sourceCode sourceStep targetCode targetStep hsource htarget).
      now rewrite hcanonical.
    + unfold rawStandardTermOperationSourceAt,
        rawStandardTermOpeningTargetAt.
      rewrite hdecoded. right. left. split; reflexivity.
Qed.

End PABoundedRawCodedTermOperationsStandardAdequacy.
