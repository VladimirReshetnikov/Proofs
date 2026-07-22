(**
  Formula shifting for the finite restricted-target syntax context.

  The only nonstandard syntax leaf occurring in the restricted consistency
  formulas is the code of a numeral term.  All other leaves are ordinary
  quoted terms or formulas.  We therefore instantiate the generic raw shift
  tree with two atomic cases:

  - fixed syntax uses the standard quotation theorem;
  - the numeral hole uses [raw_codedTermShift_numeral_identity].

  [prior] records how many outer successor renamings have already been
  applied.  One tree realizes the edge [prior -> S prior], which lets the
  same construction provide the three-, two-, and one-edge orbits needed by
  the nested existential eliminations.

  The current restricted target uses only fixed and hole term contexts and
  no [RTFCSeal] below the proof assumption.  Those precise restrictions are
  exposed by the two [ShiftSupported] predicates instead of silently
  claiming an operation theorem for unused context constructors.
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
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedFormulaShiftTreeRealization RawCodedFormulaShiftTreeStandard.

Module PABoundedRawCodedRestrictedTargetFormulaShift.

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
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedFormulaShiftTreeRealization.
Import PABoundedRawCodedFormulaShiftTreeStandard.

(** Repeated shifts at one cutoff add their amounts.  Only the successor
    instance is needed below, so it is proved directly without a general
    arithmetic normalization layer. *)
Lemma standardTermShift_after_prior : forall cutoff prior t,
  standardTermShift cutoff 1 (standardTermShift cutoff prior t) =
  standardTermShift cutoff (S prior) t.
Proof.
  intros cutoff prior t.
  induction t as [index | | child IH | lhs IHlhs rhs IHrhs |
      lhs IHlhs rhs IHrhs];
    cbn [standardTermShift].
  - destruct (index <? cutoff) eqn:hindex.
    + cbn [standardTermShift]. now rewrite hindex.
    + apply Nat.ltb_ge in hindex.
      assert (hshifted : (index + prior <? cutoff) = false).
      { apply Nat.ltb_ge. lia. }
      cbn [standardTermShift]. rewrite hshifted. f_equal. lia.
  - reflexivity.
  - now rewrite IH.
  - now rewrite IHlhs, IHrhs.
  - now rewrite IHlhs, IHrhs.
Qed.

Lemma standardFormulaShift_after_prior : forall cutoff prior phi,
  standardFormulaShift cutoff 1
    (standardFormulaShift cutoff prior phi) =
  standardFormulaShift cutoff (S prior) phi.
Proof.
  intros cutoff prior phi. revert cutoff.
  induction phi as [lhs rhs | | lhs IHlhs rhs IHrhs |
      lhs IHlhs rhs IHrhs | lhs IHlhs rhs IHrhs |
      child IHchild | child IHchild]; intro cutoff;
    cbn [standardFormulaShift].
  - now rewrite !standardTermShift_after_prior.
  - reflexivity.
  - now rewrite IHlhs, IHrhs.
  - now rewrite IHlhs, IHrhs.
  - now rewrite IHlhs, IHrhs.
  - now rewrite IHchild.
  - now rewrite IHchild.
Qed.

Lemma standardTermShift_amount_zero : forall cutoff t,
  standardTermShift cutoff 0 t = t.
Proof.
  intros cutoff t.
  induction t as [index | | child IH | lhs IHlhs rhs IHrhs |
      lhs IHlhs rhs IHrhs]; cbn [standardTermShift].
  - destruct (index <? cutoff); [reflexivity |].
    now rewrite Nat.add_0_r.
  - reflexivity.
  - now rewrite IH.
  - now rewrite IHlhs, IHrhs.
  - now rewrite IHlhs, IHrhs.
Qed.

Lemma standardFormulaShift_amount_zero : forall cutoff phi,
  standardFormulaShift cutoff 0 phi = phi.
Proof.
  intros cutoff phi. revert cutoff.
  induction phi as [lhs rhs | | lhs IHlhs rhs IHrhs |
      lhs IHlhs rhs IHrhs | lhs IHlhs rhs IHrhs |
      child IHchild | child IHchild]; intro cutoff;
    cbn [standardFormulaShift].
  - now rewrite !standardTermShift_amount_zero.
  - reflexivity.
  - now rewrite IHlhs, IHrhs.
  - now rewrite IHlhs, IHrhs.
  - now rewrite IHlhs, IHrhs.
  - now rewrite IHchild.
  - now rewrite IHchild.
Qed.

(** Exactly the term contexts occurring at equality leaves of the current
    restricted target. *)
Definition RestrictedTargetTermContextShiftSupported
    (context : RestrictedTargetTermContext) : Prop :=
  match context with
  | RTTCFixed _ => True
  | RTTCHole => True
  | RTTCSucc _ => False
  | RTTCAdd _ _ => False
  | RTTCMul _ _ => False
  end.

Fixpoint RestrictedTargetFormulaContextShiftSupported
    (context : RestrictedTargetFormulaContext) : Prop :=
  match context with
  | RTFCFixed _ => True
  | RTFCBot => True
  | RTFCEq lhs rhs =>
      RestrictedTargetTermContextShiftSupported lhs /\
      RestrictedTargetTermContextShiftSupported rhs
  | RTFCImp lhs rhs
  | RTFCAnd lhs rhs
  | RTFCOr lhs rhs =>
      RestrictedTargetFormulaContextShiftSupported lhs /\
      RestrictedTargetFormulaContextShiftSupported rhs
  | RTFCAll child
  | RTFCEx child => RestrictedTargetFormulaContextShiftSupported child
  | RTFCSeal _ => False
  end.

(** Raw codes after [prior] shifts.  Unsupported constructors are still
    assigned transparent codes, but no theorem below can use them without a
    proof of the corresponding support predicate. *)
Fixpoint rawRestrictedTargetTermContextIteratedShiftCode
    (M : RawPAModel) (numeralCode : M) (cutoff prior : nat)
    (context : RestrictedTargetTermContext) : M :=
  match context with
  | RTTCFixed fixed =>
      rawQuotedTermCode M (standardTermShift cutoff prior fixed)
  | RTTCHole => numeralCode
  | RTTCSucc child =>
      rawTermSuccCode M
        (rawRestrictedTargetTermContextIteratedShiftCode
          M numeralCode cutoff prior child)
  | RTTCAdd lhs rhs =>
      rawTermAddCode M
        (rawRestrictedTargetTermContextIteratedShiftCode
          M numeralCode cutoff prior lhs)
        (rawRestrictedTargetTermContextIteratedShiftCode
          M numeralCode cutoff prior rhs)
  | RTTCMul lhs rhs =>
      rawTermMulCode M
        (rawRestrictedTargetTermContextIteratedShiftCode
          M numeralCode cutoff prior lhs)
        (rawRestrictedTargetTermContextIteratedShiftCode
          M numeralCode cutoff prior rhs)
  end.

Fixpoint rawRestrictedTargetFormulaContextIteratedShiftCode
    (M : RawPAModel) (numeralCode : M) (cutoff prior : nat)
    (context : RestrictedTargetFormulaContext) : M :=
  match context with
  | RTFCFixed fixed =>
      rawQuotedFormulaCode M (standardFormulaShift cutoff prior fixed)
  | RTFCBot => rawFormulaBotCode M
  | RTFCEq lhs rhs =>
      rawFormulaEqCode M
        (rawRestrictedTargetTermContextIteratedShiftCode
          M numeralCode cutoff prior lhs)
        (rawRestrictedTargetTermContextIteratedShiftCode
          M numeralCode cutoff prior rhs)
  | RTFCImp lhs rhs =>
      rawFormulaImpCode M
        (rawRestrictedTargetFormulaContextIteratedShiftCode
          M numeralCode cutoff prior lhs)
        (rawRestrictedTargetFormulaContextIteratedShiftCode
          M numeralCode cutoff prior rhs)
  | RTFCAnd lhs rhs =>
      rawFormulaAndCode M
        (rawRestrictedTargetFormulaContextIteratedShiftCode
          M numeralCode cutoff prior lhs)
        (rawRestrictedTargetFormulaContextIteratedShiftCode
          M numeralCode cutoff prior rhs)
  | RTFCOr lhs rhs =>
      rawFormulaOrCode M
        (rawRestrictedTargetFormulaContextIteratedShiftCode
          M numeralCode cutoff prior lhs)
        (rawRestrictedTargetFormulaContextIteratedShiftCode
          M numeralCode cutoff prior rhs)
  | RTFCAll child =>
      rawFormulaAllCode M
        (rawRestrictedTargetFormulaContextIteratedShiftCode
          M numeralCode (S cutoff) prior child)
  | RTFCEx child =>
      rawFormulaExCode M
        (rawRestrictedTargetFormulaContextIteratedShiftCode
          M numeralCode (S cutoff) prior child)
  | RTFCSeal _ => rawFormulaBotCode M
  end.

Arguments rawRestrictedTargetTermContextIteratedShiftCode
  M numeralCode cutoff prior context : clear implicits.
Arguments rawRestrictedTargetFormulaContextIteratedShiftCode
  M numeralCode cutoff prior context : clear implicits.

Lemma rawRestrictedTargetTermContextIteratedShiftCode_zero : forall
    M numeralCode cutoff context,
  RestrictedTargetTermContextShiftSupported context ->
  rawRestrictedTargetTermContextIteratedShiftCode
    M numeralCode cutoff 0 context =
  rawRestrictedTargetTermContextCode M numeralCode context.
Proof.
  intros M numeralCode cutoff context hsupport.
  destruct context; cbn
    [RestrictedTargetTermContextShiftSupported
      rawRestrictedTargetTermContextIteratedShiftCode
      rawRestrictedTargetTermContextCode] in *;
    try contradiction; try reflexivity.
  now rewrite standardTermShift_amount_zero.
Qed.

Lemma rawRestrictedTargetFormulaContextIteratedShiftCode_zero : forall
    M numeralCode cutoff context,
  RestrictedTargetFormulaContextShiftSupported context ->
  rawRestrictedTargetFormulaContextIteratedShiftCode
    M numeralCode cutoff 0 context =
  rawRestrictedTargetFormulaContextCode M numeralCode context.
Proof.
  intros M numeralCode cutoff context. revert cutoff.
  induction context as [fixed | | lhs rhs | lhs IHlhs rhs IHrhs |
      lhs IHlhs rhs IHrhs | lhs IHlhs rhs IHrhs |
      child IHchild | child IHchild | child IHchild];
    intros cutoff hsupport;
    cbn [RestrictedTargetFormulaContextShiftSupported
      rawRestrictedTargetFormulaContextIteratedShiftCode
      rawRestrictedTargetFormulaContextCode] in *.
  - now rewrite standardFormulaShift_amount_zero.
  - reflexivity.
  - destruct hsupport as [hlhs hrhs].
    now rewrite rawRestrictedTargetTermContextIteratedShiftCode_zero,
      rawRestrictedTargetTermContextIteratedShiftCode_zero.
  - destruct hsupport as [hlhs hrhs].
    now rewrite IHlhs, IHrhs.
  - destruct hsupport as [hlhs hrhs].
    now rewrite IHlhs, IHrhs.
  - destruct hsupport as [hlhs hrhs].
    now rewrite IHlhs, IHrhs.
  - now rewrite IHchild.
  - now rewrite IHchild.
  - contradiction.
Qed.

(** One atomic term edge in the context. *)
Theorem raw_codedTermShift_restrictedTargetTermContext_iterated : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    numeralBound numeralCode cutoff prior context,
  RawNumeralTermCodeAt M numeralBound numeralCode ->
  RestrictedTargetTermContextShiftSupported context ->
  RawCodedTermShift M
    (rawNumeralValue M cutoff) (rawNumeralValue M 1)
    (rawRestrictedTargetTermContextIteratedShiftCode
      M numeralCode cutoff prior context)
    (rawRestrictedTargetTermContextIteratedShiftCode
      M numeralCode cutoff (S prior) context).
Proof.
  intros M hPA numeralBound numeralCode cutoff prior context
    hnumeral hsupport.
  destruct context; cbn
    [RestrictedTargetTermContextShiftSupported
      rawRestrictedTargetTermContextIteratedShiftCode] in *;
    try contradiction.
  - pose proof (raw_codedTermShift_standard M hPA cutoff 1
      (standardTermShift cutoff prior t)) as hshift.
    now rewrite standardTermShift_after_prior in hshift.
  - exact (raw_codedTermShift_numeral_identity M hPA
      numeralBound numeralCode (rawNumeralValue M cutoff)
      (rawNumeralValue M 1) hnumeral).
Qed.

(** The finite tree for the edge [prior -> S prior]. *)
Fixpoint rawRestrictedTargetFormulaShiftTree (M : RawPAModel)
    (numeralCode : M) (cutoff prior : nat)
    (context : RestrictedTargetFormulaContext) : RawFormulaShiftTree M :=
  match context with
  | RTFCFixed fixed =>
      rawStandardFormulaShiftTree M cutoff 1
        (standardFormulaShift cutoff prior fixed)
  | RTFCBot => RFSTBot M (rawNumeralValue M cutoff)
  | RTFCEq lhs rhs =>
      RFSTEq M (rawNumeralValue M cutoff)
        (rawRestrictedTargetTermContextIteratedShiftCode
          M numeralCode cutoff prior lhs)
        (rawRestrictedTargetTermContextIteratedShiftCode
          M numeralCode cutoff (S prior) lhs)
        (rawRestrictedTargetTermContextIteratedShiftCode
          M numeralCode cutoff prior rhs)
        (rawRestrictedTargetTermContextIteratedShiftCode
          M numeralCode cutoff (S prior) rhs)
  | RTFCImp lhs rhs =>
      RFSTBinary M RFSBImp (rawNumeralValue M cutoff)
        (rawRestrictedTargetFormulaShiftTree
          M numeralCode cutoff prior lhs)
        (rawRestrictedTargetFormulaShiftTree
          M numeralCode cutoff prior rhs)
  | RTFCAnd lhs rhs =>
      RFSTBinary M RFSBAnd (rawNumeralValue M cutoff)
        (rawRestrictedTargetFormulaShiftTree
          M numeralCode cutoff prior lhs)
        (rawRestrictedTargetFormulaShiftTree
          M numeralCode cutoff prior rhs)
  | RTFCOr lhs rhs =>
      RFSTBinary M RFSBOr (rawNumeralValue M cutoff)
        (rawRestrictedTargetFormulaShiftTree
          M numeralCode cutoff prior lhs)
        (rawRestrictedTargetFormulaShiftTree
          M numeralCode cutoff prior rhs)
  | RTFCAll child =>
      RFSTUnary M RFSUAll (rawNumeralValue M cutoff)
        (rawRestrictedTargetFormulaShiftTree
          M numeralCode (S cutoff) prior child)
  | RTFCEx child =>
      RFSTUnary M RFSUEx (rawNumeralValue M cutoff)
        (rawRestrictedTargetFormulaShiftTree
          M numeralCode (S cutoff) prior child)
  | RTFCSeal _ => RFSTBot M (rawNumeralValue M cutoff)
  end.

Lemma rawRestrictedTargetFormulaShiftTree_depth : forall
    M numeralCode cutoff prior context,
  rawFormulaShiftTreeDepth M
    (rawRestrictedTargetFormulaShiftTree
      M numeralCode cutoff prior context) = rawNumeralValue M cutoff.
Proof.
  intros M numeralCode cutoff prior context. destruct context;
    cbn [rawRestrictedTargetFormulaShiftTree rawFormulaShiftTreeDepth];
    try reflexivity.
  apply rawStandardFormulaShiftTree_depth.
Qed.

Lemma rawRestrictedTargetFormulaShiftTree_source : forall
    M numeralCode cutoff prior context,
  RestrictedTargetFormulaContextShiftSupported context ->
  rawFormulaShiftTreeSource M
    (rawRestrictedTargetFormulaShiftTree
      M numeralCode cutoff prior context) =
  rawRestrictedTargetFormulaContextIteratedShiftCode
    M numeralCode cutoff prior context.
Proof.
  intros M numeralCode cutoff prior context. revert cutoff.
  induction context as [fixed | | lhs rhs | lhs IHlhs rhs IHrhs |
      lhs IHlhs rhs IHrhs | lhs IHlhs rhs IHrhs |
      child IHchild | child IHchild | child IHchild];
    intros cutoff hsupport;
    cbn [RestrictedTargetFormulaContextShiftSupported
      rawRestrictedTargetFormulaShiftTree
      rawRestrictedTargetFormulaContextIteratedShiftCode
      rawFormulaShiftTreeSource rawFormulaShiftBinaryCode
      rawFormulaShiftUnaryCode] in *.
  - apply rawStandardFormulaShiftTree_source.
  - reflexivity.
  - reflexivity.
  - destruct hsupport as [hlhs hrhs]. now rewrite IHlhs, IHrhs.
  - destruct hsupport as [hlhs hrhs]. now rewrite IHlhs, IHrhs.
  - destruct hsupport as [hlhs hrhs]. now rewrite IHlhs, IHrhs.
  - now rewrite IHchild.
  - now rewrite IHchild.
  - contradiction.
Qed.

Lemma rawRestrictedTargetFormulaShiftTree_target : forall
    M numeralCode cutoff prior context,
  RestrictedTargetFormulaContextShiftSupported context ->
  rawFormulaShiftTreeTarget M
    (rawRestrictedTargetFormulaShiftTree
      M numeralCode cutoff prior context) =
  rawRestrictedTargetFormulaContextIteratedShiftCode
    M numeralCode cutoff (S prior) context.
Proof.
  intros M numeralCode cutoff prior context. revert cutoff.
  induction context as [fixed | | lhs rhs | lhs IHlhs rhs IHrhs |
      lhs IHlhs rhs IHrhs | lhs IHlhs rhs IHrhs |
      child IHchild | child IHchild | child IHchild];
    intros cutoff hsupport;
    cbn [RestrictedTargetFormulaContextShiftSupported
      rawRestrictedTargetFormulaShiftTree
      rawRestrictedTargetFormulaContextIteratedShiftCode
      rawFormulaShiftTreeTarget rawFormulaShiftBinaryCode
      rawFormulaShiftUnaryCode] in *.
  - rewrite rawStandardFormulaShiftTree_target.
    apply f_equal. apply standardFormulaShift_after_prior.
  - reflexivity.
  - reflexivity.
  - destruct hsupport as [hlhs hrhs]. now rewrite IHlhs, IHrhs.
  - destruct hsupport as [hlhs hrhs]. now rewrite IHlhs, IHrhs.
  - destruct hsupport as [hlhs hrhs]. now rewrite IHlhs, IHrhs.
  - now rewrite IHchild.
  - now rewrite IHchild.
  - contradiction.
Qed.

Theorem rawRestrictedTargetFormulaShiftTree_valid : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    numeralBound numeralCode cutoff prior context,
  RawNumeralTermCodeAt M numeralBound numeralCode ->
  RestrictedTargetFormulaContextShiftSupported context ->
  RawFormulaShiftTreeValid M (rawNumeralValue M 1)
    (rawRestrictedTargetFormulaShiftTree
      M numeralCode cutoff prior context).
Proof.
  intros M hPA numeralBound numeralCode cutoff prior context.
  revert cutoff.
  induction context as [fixed | | lhs rhs | lhs IHlhs rhs IHrhs |
      lhs IHlhs rhs IHrhs | lhs IHlhs rhs IHrhs |
      child IHchild | child IHchild | child IHchild];
    intros cutoff hnumeral hsupport;
    cbn [RestrictedTargetFormulaContextShiftSupported
      rawRestrictedTargetFormulaShiftTree RawFormulaShiftTreeValid] in *.
  - apply rawStandardFormulaShiftTree_valid. exact hPA.
  - exact I.
  - destruct hsupport as [hlhs hrhs]. split.
    + exact (raw_codedTermShift_restrictedTargetTermContext_iterated
        M hPA numeralBound numeralCode cutoff prior lhs hnumeral hlhs).
    + exact (raw_codedTermShift_restrictedTargetTermContext_iterated
        M hPA numeralBound numeralCode cutoff prior rhs hnumeral hrhs).
  - destruct hsupport as [hlhs hrhs]. repeat split.
    + apply rawRestrictedTargetFormulaShiftTree_depth.
    + apply rawRestrictedTargetFormulaShiftTree_depth.
    + exact (IHlhs cutoff hnumeral hlhs).
    + exact (IHrhs cutoff hnumeral hrhs).
  - destruct hsupport as [hlhs hrhs]. repeat split.
    + apply rawRestrictedTargetFormulaShiftTree_depth.
    + apply rawRestrictedTargetFormulaShiftTree_depth.
    + exact (IHlhs cutoff hnumeral hlhs).
    + exact (IHrhs cutoff hnumeral hrhs).
  - destruct hsupport as [hlhs hrhs]. repeat split.
    + apply rawRestrictedTargetFormulaShiftTree_depth.
    + apply rawRestrictedTargetFormulaShiftTree_depth.
    + exact (IHlhs cutoff hnumeral hlhs).
    + exact (IHrhs cutoff hnumeral hrhs).
  - split.
    + rewrite rawRestrictedTargetFormulaShiftTree_depth. reflexivity.
    + exact (IHchild (S cutoff) hnumeral hsupport).
  - split.
    + rewrite rawRestrictedTargetFormulaShiftTree_depth. reflexivity.
    + exact (IHchild (S cutoff) hnumeral hsupport).
  - contradiction.
Qed.

(** Public edge theorem. *)
Theorem raw_codedFormulaShift_restrictedTargetContext_iterated : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    numeralBound numeralCode cutoff prior context,
  RawNumeralTermCodeAt M numeralBound numeralCode ->
  RestrictedTargetFormulaContextShiftSupported context ->
  RawCodedFormulaShift M
    (rawNumeralValue M cutoff) (rawNumeralValue M 1)
    (rawRestrictedTargetFormulaContextIteratedShiftCode
      M numeralCode cutoff prior context)
    (rawRestrictedTargetFormulaContextIteratedShiftCode
      M numeralCode cutoff (S prior) context).
Proof.
  intros M hPA numeralBound numeralCode cutoff prior context
    hnumeral hsupport.
  pose proof (raw_codedFormulaShift_of_valid_tree M hPA
    (rawNumeralValue M 1)
    (rawRestrictedTargetFormulaShiftTree
      M numeralCode cutoff prior context)
    (rawRestrictedTargetFormulaShiftTree_valid M hPA
      numeralBound numeralCode cutoff prior context
      hnumeral hsupport)) as hshift.
  rewrite rawRestrictedTargetFormulaShiftTree_depth in hshift.
  rewrite rawRestrictedTargetFormulaShiftTree_source in hshift
    by exact hsupport.
  rewrite rawRestrictedTargetFormulaShiftTree_target in hshift
    by exact hsupport.
  exact hshift.
Qed.

Corollary raw_codedFormulaShift_restrictedTargetContext_zero_one : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    numeralBound numeralCode context,
  RawNumeralTermCodeAt M numeralBound numeralCode ->
  RestrictedTargetFormulaContextShiftSupported context ->
  RawCodedFormulaShift M (raw_zero M) (rawNumeralValue M 1)
    (rawRestrictedTargetFormulaContextCode M numeralCode context)
    (rawRestrictedTargetFormulaContextIteratedShiftCode
      M numeralCode 0 1 context).
Proof.
  intros M hPA numeralBound numeralCode context hnumeral hsupport.
  pose proof (raw_codedFormulaShift_restrictedTargetContext_iterated
    M hPA numeralBound numeralCode 0 0 context hnumeral hsupport) as hshift.
  cbn [rawNumeralValue] in hshift.
  rewrite rawRestrictedTargetFormulaContextIteratedShiftCode_zero in hshift
    by exact hsupport.
  exact hshift.
Qed.

End PABoundedRawCodedRestrictedTargetFormulaShift.
