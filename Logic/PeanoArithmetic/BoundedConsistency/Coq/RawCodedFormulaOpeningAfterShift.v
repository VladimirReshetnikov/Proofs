(**
  Represented opening is a left inverse to a one-step standard shift, even
  for a nonstandard replacement numeral.

  The replacement is never selected while opening shifted fixed syntax:
  variables below the cutoff remain below it, and variables at or above the
  cutoff were moved to strict successors.  The explicit term tree records
  this fact row by row.  The formula tree then packages those term traces at
  equality leaves and is suitable for embedding in larger nonstandard
  formula skeletons.
*)

From Stdlib Require Import Arith Lia.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax RawCodedSyntaxConstructors RawCodedFormulaOperations
  RawCodedTermOperationsStandardAdequacy
  RawCodedFormulaOperationsStandardAdequacy
  RawCodedNumeralTermCode RawCodedNumeralTermShift
  RawCodedTermOperationTreeRealization
  RawCodedFormulaShiftTreeRealization
  RawCodedFormulaOperationTreeRealization.

Module PABoundedRawCodedFormulaOpeningAfterShift.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedTermOperationsStandardAdequacy.
Import PABoundedRawCodedFormulaOperationsStandardAdequacy.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedNumeralTermShift.
Import PABoundedRawCodedTermOperationTreeRealization.
Import PABoundedRawCodedFormulaShiftTreeRealization.
Import PABoundedRawCodedFormulaOperationTreeRealization.

(** The source index at a variable leaf is exactly its one-step shifted
    index.  Its target is the original quoted variable. *)
Fixpoint rawStandardTermOpeningAfterShiftTree (M : RawPAModel)
    (cutoff : nat) (input : term) : RawTermOperationTree M :=
  match input with
  | tVar index =>
      RTOTVar M
        (rawNumeralValue M
          (if index <? cutoff then index else index + 1))
        (rawTermVarCode M (rawNumeralValue M index))
  | tZero => RTOTZero M
  | tSucc child =>
      RTOTSucc M (rawStandardTermOpeningAfterShiftTree M cutoff child)
  | tAdd lhs rhs =>
      RTOTBinary M RTOBAdd
        (rawStandardTermOpeningAfterShiftTree M cutoff lhs)
        (rawStandardTermOpeningAfterShiftTree M cutoff rhs)
  | tMul lhs rhs =>
      RTOTBinary M RTOBMul
        (rawStandardTermOpeningAfterShiftTree M cutoff lhs)
        (rawStandardTermOpeningAfterShiftTree M cutoff rhs)
  end.

Lemma rawStandardTermOpeningAfterShiftTree_source : forall M cutoff input,
  rawTermOperationTreeSource M
    (rawStandardTermOpeningAfterShiftTree M cutoff input) =
  rawQuotedTermCode M (standardTermShift cutoff 1 input).
Proof.
  intros M cutoff input.
  induction input as [index | | child IH | left IHleft right IHright |
      left IHleft right IHright];
    cbn [rawStandardTermOpeningAfterShiftTree
      rawTermOperationTreeSource rawTermOperationBinaryCode
      rawQuotedTermCode standardTermShift].
  - destruct (index <? cutoff); reflexivity.
  - reflexivity.
  - now rewrite IH.
  - now rewrite IHleft, IHright.
  - now rewrite IHleft, IHright.
Qed.

Lemma rawStandardTermOpeningAfterShiftTree_target : forall M cutoff input,
  rawTermOperationTreeTarget M
    (rawStandardTermOpeningAfterShiftTree M cutoff input) =
  rawQuotedTermCode M input.
Proof.
  intros M cutoff input.
  induction input as [index | | child IH | left IHleft right IHright |
      left IHleft right IHright];
    cbn [rawStandardTermOpeningAfterShiftTree
      rawTermOperationTreeTarget rawTermOperationBinaryCode
      rawQuotedTermCode].
  - reflexivity.
  - reflexivity.
  - now rewrite IH.
  - now rewrite IHleft, IHright.
  - now rewrite IHleft, IHright.
Qed.

Theorem rawStandardTermOpeningAfterShiftTree_valid : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    cutoff liftedReplacement input,
  RawTermOperationTreeValid M
    (RawCodedTermOpeningVariableRow M
      (rawNumeralValue M cutoff) liftedReplacement)
    (rawStandardTermOpeningAfterShiftTree M cutoff input).
Proof.
  intros M hPA cutoff liftedReplacement input.
  induction input as [index | | child IH | left IHleft right IHright |
      left IHleft right IHright];
    cbn [rawStandardTermOpeningAfterShiftTree RawTermOperationTreeValid].
  - destruct (index <? cutoff) eqn:hbelow.
    + apply Nat.ltb_lt in hbelow.
      exists (rawNumeralValue M index). split; [reflexivity |].
      left. split.
      * apply raw_lt_numeralValue_of_lt; [exact hPA | exact hbelow].
      * reflexivity.
    + apply Nat.ltb_ge in hbelow.
      exists (rawNumeralValue M (index + 1)). split; [reflexivity |].
      right. right.
      exists (rawNumeralValue M index). split.
      * replace (index + 1) with (S index) by lia. reflexivity.
      * split.
        -- apply raw_lt_numeralValue_of_lt; [exact hPA | lia].
        -- reflexivity.
  - exact I.
  - exact IH.
  - split; assumption.
  - split; assumption.
Qed.

Theorem raw_codedTermOpening_after_standardShift_one : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    cutoff liftedReplacement input,
  RawCodedTermOpening M (rawNumeralValue M cutoff) liftedReplacement
    (rawQuotedTermCode M (standardTermShift cutoff 1 input))
    (rawQuotedTermCode M input).
Proof.
  intros M hPA cutoff liftedReplacement input.
  pose proof (raw_codedTermOpening_of_valid_tree M hPA
    (rawNumeralValue M cutoff) liftedReplacement
    (rawStandardTermOpeningAfterShiftTree M cutoff input)
    (rawStandardTermOpeningAfterShiftTree_valid M hPA
      cutoff liftedReplacement input)) as hopening.
  rewrite rawStandardTermOpeningAfterShiftTree_source in hopening.
  rewrite rawStandardTermOpeningAfterShiftTree_target in hopening.
  exact hopening.
Qed.

(** Formula-level tree with the shifted quotation as source and the original
    quotation as target. *)
Fixpoint rawStandardFormulaOpeningAfterShiftTree (M : RawPAModel)
    (depth : nat) (input : formula) : RawFormulaShiftTree M :=
  match input with
  | pEq lhs rhs =>
      RFSTEq M (rawNumeralValue M depth)
        (rawQuotedTermCode M (standardTermShift depth 1 lhs))
        (rawQuotedTermCode M lhs)
        (rawQuotedTermCode M (standardTermShift depth 1 rhs))
        (rawQuotedTermCode M rhs)
  | pBot => RFSTBot M (rawNumeralValue M depth)
  | pImp lhs rhs =>
      RFSTBinary M RFSBImp (rawNumeralValue M depth)
        (rawStandardFormulaOpeningAfterShiftTree M depth lhs)
        (rawStandardFormulaOpeningAfterShiftTree M depth rhs)
  | pAnd lhs rhs =>
      RFSTBinary M RFSBAnd (rawNumeralValue M depth)
        (rawStandardFormulaOpeningAfterShiftTree M depth lhs)
        (rawStandardFormulaOpeningAfterShiftTree M depth rhs)
  | pOr lhs rhs =>
      RFSTBinary M RFSBOr (rawNumeralValue M depth)
        (rawStandardFormulaOpeningAfterShiftTree M depth lhs)
        (rawStandardFormulaOpeningAfterShiftTree M depth rhs)
  | pAll child =>
      RFSTUnary M RFSUAll (rawNumeralValue M depth)
        (rawStandardFormulaOpeningAfterShiftTree M (S depth) child)
  | pEx child =>
      RFSTUnary M RFSUEx (rawNumeralValue M depth)
        (rawStandardFormulaOpeningAfterShiftTree M (S depth) child)
  end.

Lemma rawStandardFormulaOpeningAfterShiftTree_depth : forall M depth input,
  rawFormulaShiftTreeDepth M
    (rawStandardFormulaOpeningAfterShiftTree M depth input) =
  rawNumeralValue M depth.
Proof. intros M depth input. now destruct input. Qed.

Lemma rawStandardFormulaOpeningAfterShiftTree_source : forall M depth input,
  rawFormulaShiftTreeSource M
    (rawStandardFormulaOpeningAfterShiftTree M depth input) =
  rawQuotedFormulaCode M (standardFormulaShift depth 1 input).
Proof.
  intros M depth input. revert depth.
  induction input as [left right | | left IHleft right IHright |
      left IHleft right IHright | left IHleft right IHright |
      child IHchild | child IHchild]; intro depth;
    cbn [rawStandardFormulaOpeningAfterShiftTree
      rawFormulaShiftTreeSource rawFormulaShiftBinaryCode
      rawFormulaShiftUnaryCode rawQuotedFormulaCode standardFormulaShift];
    now rewrite ?IHleft, ?IHright, ?IHchild.
Qed.

Lemma rawStandardFormulaOpeningAfterShiftTree_target : forall M depth input,
  rawFormulaShiftTreeTarget M
    (rawStandardFormulaOpeningAfterShiftTree M depth input) =
  rawQuotedFormulaCode M input.
Proof.
  intros M depth input. revert depth.
  induction input as [left right | | left IHleft right IHright |
      left IHleft right IHright | left IHleft right IHright |
      child IHchild | child IHchild]; intro depth;
    cbn [rawStandardFormulaOpeningAfterShiftTree
      rawFormulaShiftTreeTarget rawFormulaShiftBinaryCode
      rawFormulaShiftUnaryCode rawQuotedFormulaCode];
    now rewrite ?IHleft, ?IHright, ?IHchild.
Qed.

Theorem rawStandardFormulaOpeningAfterShiftTree_valid : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    replacementBound replacement depth input,
  RawNumeralTermCodeAt M replacementBound replacement ->
  RawFormulaSubstitutionTreeValid M replacement
    (rawStandardFormulaOpeningAfterShiftTree M depth input).
Proof.
  intros M hPA replacementBound replacement depth input hreplacement.
  revert depth.
  induction input as [left right | | left IHleft right IHright |
      left IHleft right IHright | left IHleft right IHright |
      child IHchild | child IHchild]; intro depth;
    cbn [rawStandardFormulaOpeningAfterShiftTree
      RawFormulaSubstitutionTreeValid RawFormulaOperationTreeValid
      rawFormulaShiftTreeDepth].
  - split; exists replacement; split.
    + exact (raw_codedTermShift_numeral_identity M hPA
        replacementBound replacement (raw_zero M)
        (rawNumeralValue M depth) hreplacement).
    + exact (raw_codedTermOpening_after_standardShift_one
        M hPA depth replacement left).
    + exact (raw_codedTermShift_numeral_identity M hPA
        replacementBound replacement (raw_zero M)
        (rawNumeralValue M depth) hreplacement).
    + exact (raw_codedTermOpening_after_standardShift_one
        M hPA depth replacement right).
  - exact I.
  - repeat split.
    + apply rawStandardFormulaOpeningAfterShiftTree_depth.
    + apply rawStandardFormulaOpeningAfterShiftTree_depth.
    + apply IHleft.
    + apply IHright.
  - repeat split.
    + apply rawStandardFormulaOpeningAfterShiftTree_depth.
    + apply rawStandardFormulaOpeningAfterShiftTree_depth.
    + apply IHleft.
    + apply IHright.
  - repeat split.
    + apply rawStandardFormulaOpeningAfterShiftTree_depth.
    + apply rawStandardFormulaOpeningAfterShiftTree_depth.
    + apply IHleft.
    + apply IHright.
  - split.
    + rewrite rawStandardFormulaOpeningAfterShiftTree_depth. reflexivity.
    + apply IHchild.
  - split.
    + rewrite rawStandardFormulaOpeningAfterShiftTree_depth. reflexivity.
    + apply IHchild.
Qed.

Corollary raw_codedFormulaSubstitution_after_standardShift_one : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    replacementBound replacement depth input,
  RawNumeralTermCodeAt M replacementBound replacement ->
  RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
    replacement (rawNumeralValue M depth)
    (rawQuotedFormulaCode M (standardFormulaShift depth 1 input))
    (rawQuotedFormulaCode M input).
Proof.
  intros M hPA replacementBound replacement depth input hreplacement.
  pose proof (raw_codedFormulaSubstitution_of_valid_tree M hPA replacement
    (rawStandardFormulaOpeningAfterShiftTree M depth input)
    (rawStandardFormulaOpeningAfterShiftTree_valid M hPA
      replacementBound replacement depth input hreplacement)) as hoperation.
  rewrite rawStandardFormulaOpeningAfterShiftTree_depth in hoperation.
  rewrite rawStandardFormulaOpeningAfterShiftTree_source in hoperation.
  rewrite rawStandardFormulaOpeningAfterShiftTree_target in hoperation.
  exact hoperation.
Qed.

End PABoundedRawCodedFormulaOpeningAfterShift.
