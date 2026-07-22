(**
  Arbitrary-model substitution of the dynamic restricted-PA soundness source.

  The source formula has one distinguished free variable for the restriction
  level.  Given any model-internal numeral-term code, this module constructs
  a finite carrier-valued formula tree whose source is that fixed formula and
  whose target is the exact six-premise dynamic-soundness implication.  Thus
  the construction works at nonstandard levels and never decodes the numeral
  code outside the model.
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
  RawCodedNumeralTermOpening RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedProofAtomicAdequacy RawCodedProofFormulaCoverage
  RawCodedProofRuleCoverage RawCodedProofRules
  RawCodedRestrictedPAProof
  RawCodedRestrictedTargetFormulaShift
  RawCodedRestrictedPAConsistencyOpenDescent
  RawCodedRestrictedPADynamicSoundnessComposition
  RawCodedRestrictedPADynamicSoundnessSource
  RawCodedFormulaShiftTreeRealization
  RawCodedFormulaOperationTreeRealization
  RawCodedFormulaOpeningAfterShift.

Module PABoundedRawCodedRestrictedPADynamicSoundnessSubstitution.

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
Import PABoundedRawCodedNumeralTermOpening.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedProofFormulaCoverage.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedRestrictedTargetFormulaShift.
Import PABoundedRawCodedRestrictedPAConsistencyOpenDescent.
Import PABoundedRawCodedRestrictedPADynamicSoundnessComposition.
Import PABoundedRawCodedRestrictedPADynamicSoundnessSource.
Import PABoundedRawCodedFormulaShiftTreeRealization.
Import PABoundedRawCodedFormulaOperationTreeRealization.
Import PABoundedRawCodedFormulaOpeningAfterShift.

(** Raw quotation of the source term context. *)
Fixpoint rawRestrictedPADynamicSourceTermContextCode
    (M : RawPAModel) (depth : nat)
    (context : RestrictedTargetTermContext) : M :=
  match context with
  | RTTCFixed fixed =>
      rawQuotedTermCode M (standardTermShift depth 1 fixed)
  | RTTCHole => rawTermVarCode M (rawNumeralValue M depth)
  | RTTCSucc child =>
      rawTermSuccCode M
        (rawRestrictedPADynamicSourceTermContextCode M depth child)
  | RTTCAdd lhs rhs =>
      rawTermAddCode M
        (rawRestrictedPADynamicSourceTermContextCode M depth lhs)
        (rawRestrictedPADynamicSourceTermContextCode M depth rhs)
  | RTTCMul lhs rhs =>
      rawTermMulCode M
        (rawRestrictedPADynamicSourceTermContextCode M depth lhs)
        (rawRestrictedPADynamicSourceTermContextCode M depth rhs)
  end.

Fixpoint rawRestrictedPADynamicSourceFormulaContextCode
    (M : RawPAModel) (depth : nat)
    (context : RestrictedTargetFormulaContext) : M :=
  match context with
  | RTFCFixed fixed =>
      rawQuotedFormulaCode M (standardFormulaShift depth 1 fixed)
  | RTFCBot => rawFormulaBotCode M
  | RTFCEq lhs rhs =>
      rawFormulaEqCode M
        (rawRestrictedPADynamicSourceTermContextCode M depth lhs)
        (rawRestrictedPADynamicSourceTermContextCode M depth rhs)
  | RTFCImp lhs rhs =>
      rawFormulaImpCode M
        (rawRestrictedPADynamicSourceFormulaContextCode M depth lhs)
        (rawRestrictedPADynamicSourceFormulaContextCode M depth rhs)
  | RTFCAnd lhs rhs =>
      rawFormulaAndCode M
        (rawRestrictedPADynamicSourceFormulaContextCode M depth lhs)
        (rawRestrictedPADynamicSourceFormulaContextCode M depth rhs)
  | RTFCOr lhs rhs =>
      rawFormulaOrCode M
        (rawRestrictedPADynamicSourceFormulaContextCode M depth lhs)
        (rawRestrictedPADynamicSourceFormulaContextCode M depth rhs)
  | RTFCAll child =>
      rawFormulaAllCode M
        (rawRestrictedPADynamicSourceFormulaContextCode M (S depth) child)
  | RTFCEx child =>
      rawFormulaExCode M
        (rawRestrictedPADynamicSourceFormulaContextCode M (S depth) child)
  | RTFCSeal _ => rawFormulaBotCode M
  end.

Arguments rawRestrictedPADynamicSourceTermContextCode
  M depth context : clear implicits.
Arguments rawRestrictedPADynamicSourceFormulaContextCode
  M depth context : clear implicits.

Lemma rawRestrictedPADynamicSourceTermContextCode_quoted : forall
    M depth context,
  rawRestrictedPADynamicSourceTermContextCode M depth context =
  rawQuotedTermCode M
    (restrictedPADynamicSourceTermContext depth context).
Proof.
  intros M depth context.
  induction context as [fixed | | child IH | lhs IHlhs rhs IHrhs |
      lhs IHlhs rhs IHrhs];
    cbn [rawRestrictedPADynamicSourceTermContextCode
      restrictedPADynamicSourceTermContext rawQuotedTermCode];
    now rewrite ?IH, ?IHlhs, ?IHrhs.
Qed.

Lemma rawRestrictedPADynamicSourceFormulaContextCode_quoted : forall
    M depth context,
  rawRestrictedPADynamicSourceFormulaContextCode M depth context =
  rawQuotedFormulaCode M
    (restrictedPADynamicSourceFormulaContext depth context).
Proof.
  intros M depth context. revert depth.
  induction context as [fixed | | lhs rhs | lhs IHlhs rhs IHrhs |
      lhs IHlhs rhs IHrhs | lhs IHlhs rhs IHrhs |
      child IHchild | child IHchild | child IHchild]; intro depth;
    cbn [rawRestrictedPADynamicSourceFormulaContextCode
      restrictedPADynamicSourceFormulaContext rawQuotedFormulaCode];
    now rewrite ?rawRestrictedPADynamicSourceTermContextCode_quoted,
      ?IHlhs, ?IHrhs, ?IHchild.
Qed.

(** Atomic opening for the only supported term leaves: fixed syntax and the
    distinguished level hole. *)
Lemma raw_codedFormulaSubstitutionAtom_dynamicSourceTermContext : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    numeralBound numeralCode depth context,
  RawNumeralTermCodeAt M numeralBound numeralCode ->
  RestrictedTargetTermContextShiftSupported context ->
  RawCodedFormulaSubstitutionAtom M numeralCode
    (rawNumeralValue M depth)
    (rawRestrictedPADynamicSourceTermContextCode M depth context)
    (rawRestrictedTargetTermContextCode M numeralCode context).
Proof.
  intros M hPA numeralBound numeralCode depth context hnumeral hsupport.
  destruct context; cbn
    [RestrictedTargetTermContextShiftSupported
      rawRestrictedPADynamicSourceTermContextCode
      rawRestrictedTargetTermContextCode] in *;
    try contradiction.
  - exists numeralCode. split.
    + exact (raw_codedTermShift_numeral_identity M hPA
        numeralBound numeralCode (raw_zero M)
        (rawNumeralValue M depth) hnumeral).
    + exact (raw_codedTermOpening_after_standardShift_one
        M hPA depth numeralCode t).
  - exact (raw_codedFormulaSubstitutionAtom_variable_numeral
      M hPA numeralBound numeralCode (rawNumeralValue M depth) hnumeral).
Qed.

(** The dynamic context tree. *)
Fixpoint rawRestrictedPADynamicSourceContextSubstitutionTree
    (M : RawPAModel) (numeralCode : M) (depth : nat)
    (context : RestrictedTargetFormulaContext) : RawFormulaShiftTree M :=
  match context with
  | RTFCFixed fixed =>
      rawStandardFormulaOpeningAfterShiftTree M depth fixed
  | RTFCBot => RFSTBot M (rawNumeralValue M depth)
  | RTFCEq lhs rhs =>
      RFSTEq M (rawNumeralValue M depth)
        (rawRestrictedPADynamicSourceTermContextCode M depth lhs)
        (rawRestrictedTargetTermContextCode M numeralCode lhs)
        (rawRestrictedPADynamicSourceTermContextCode M depth rhs)
        (rawRestrictedTargetTermContextCode M numeralCode rhs)
  | RTFCImp lhs rhs =>
      RFSTBinary M RFSBImp (rawNumeralValue M depth)
        (rawRestrictedPADynamicSourceContextSubstitutionTree
          M numeralCode depth lhs)
        (rawRestrictedPADynamicSourceContextSubstitutionTree
          M numeralCode depth rhs)
  | RTFCAnd lhs rhs =>
      RFSTBinary M RFSBAnd (rawNumeralValue M depth)
        (rawRestrictedPADynamicSourceContextSubstitutionTree
          M numeralCode depth lhs)
        (rawRestrictedPADynamicSourceContextSubstitutionTree
          M numeralCode depth rhs)
  | RTFCOr lhs rhs =>
      RFSTBinary M RFSBOr (rawNumeralValue M depth)
        (rawRestrictedPADynamicSourceContextSubstitutionTree
          M numeralCode depth lhs)
        (rawRestrictedPADynamicSourceContextSubstitutionTree
          M numeralCode depth rhs)
  | RTFCAll child =>
      RFSTUnary M RFSUAll (rawNumeralValue M depth)
        (rawRestrictedPADynamicSourceContextSubstitutionTree
          M numeralCode (S depth) child)
  | RTFCEx child =>
      RFSTUnary M RFSUEx (rawNumeralValue M depth)
        (rawRestrictedPADynamicSourceContextSubstitutionTree
          M numeralCode (S depth) child)
  | RTFCSeal _ => RFSTBot M (rawNumeralValue M depth)
  end.

Lemma rawRestrictedPADynamicSourceContextSubstitutionTree_depth : forall
    M numeralCode depth context,
  rawFormulaShiftTreeDepth M
    (rawRestrictedPADynamicSourceContextSubstitutionTree
      M numeralCode depth context) = rawNumeralValue M depth.
Proof.
  intros M numeralCode depth context. destruct context;
    cbn [rawRestrictedPADynamicSourceContextSubstitutionTree
      rawFormulaShiftTreeDepth]; try reflexivity.
  apply rawStandardFormulaOpeningAfterShiftTree_depth.
Qed.

Lemma rawRestrictedPADynamicSourceContextSubstitutionTree_source : forall
    M numeralCode depth context,
  RestrictedTargetFormulaContextShiftSupported context ->
  rawFormulaShiftTreeSource M
    (rawRestrictedPADynamicSourceContextSubstitutionTree
      M numeralCode depth context) =
  rawRestrictedPADynamicSourceFormulaContextCode M depth context.
Proof.
  intros M numeralCode depth context. revert depth.
  induction context as [fixed | | lhs rhs | lhs IHlhs rhs IHrhs |
      lhs IHlhs rhs IHrhs | lhs IHlhs rhs IHrhs |
      child IHchild | child IHchild | child IHchild];
    intros depth hsupport;
    cbn [RestrictedTargetFormulaContextShiftSupported
      rawRestrictedPADynamicSourceContextSubstitutionTree
      rawRestrictedPADynamicSourceFormulaContextCode
      rawFormulaShiftTreeSource rawFormulaShiftBinaryCode
      rawFormulaShiftUnaryCode] in *.
  - apply rawStandardFormulaOpeningAfterShiftTree_source.
  - reflexivity.
  - reflexivity.
  - destruct hsupport as [hlhs hrhs]. now rewrite IHlhs, IHrhs.
  - destruct hsupport as [hlhs hrhs]. now rewrite IHlhs, IHrhs.
  - destruct hsupport as [hlhs hrhs]. now rewrite IHlhs, IHrhs.
  - now rewrite IHchild.
  - now rewrite IHchild.
  - contradiction.
Qed.

Lemma rawRestrictedPADynamicSourceContextSubstitutionTree_target : forall
    M numeralCode depth context,
  RestrictedTargetFormulaContextShiftSupported context ->
  rawFormulaShiftTreeTarget M
    (rawRestrictedPADynamicSourceContextSubstitutionTree
      M numeralCode depth context) =
  rawRestrictedTargetFormulaContextCode M numeralCode context.
Proof.
  intros M numeralCode depth context. revert depth.
  induction context as [fixed | | lhs rhs | lhs IHlhs rhs IHrhs |
      lhs IHlhs rhs IHrhs | lhs IHlhs rhs IHrhs |
      child IHchild | child IHchild | child IHchild];
    intros depth hsupport;
    cbn [RestrictedTargetFormulaContextShiftSupported
      rawRestrictedPADynamicSourceContextSubstitutionTree
      rawRestrictedTargetFormulaContextCode
      rawFormulaShiftTreeTarget rawFormulaShiftBinaryCode
      rawFormulaShiftUnaryCode] in *.
  - apply rawStandardFormulaOpeningAfterShiftTree_target.
  - reflexivity.
  - reflexivity.
  - destruct hsupport as [hlhs hrhs]. now rewrite IHlhs, IHrhs.
  - destruct hsupport as [hlhs hrhs]. now rewrite IHlhs, IHrhs.
  - destruct hsupport as [hlhs hrhs]. now rewrite IHlhs, IHrhs.
  - now rewrite IHchild.
  - now rewrite IHchild.
  - contradiction.
Qed.

Theorem rawRestrictedPADynamicSourceContextSubstitutionTree_valid : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    numeralBound numeralCode depth context,
  RawNumeralTermCodeAt M numeralBound numeralCode ->
  RestrictedTargetFormulaContextShiftSupported context ->
  RawFormulaSubstitutionTreeValid M numeralCode
    (rawRestrictedPADynamicSourceContextSubstitutionTree
      M numeralCode depth context).
Proof.
  intros M hPA numeralBound numeralCode depth context.
  revert depth.
  induction context as [fixed | | lhs rhs | lhs IHlhs rhs IHrhs |
      lhs IHlhs rhs IHrhs | lhs IHlhs rhs IHrhs |
      child IHchild | child IHchild | child IHchild];
    intros depth hnumeral hsupport;
    cbn [RestrictedTargetFormulaContextShiftSupported
      rawRestrictedPADynamicSourceContextSubstitutionTree
      RawFormulaSubstitutionTreeValid RawFormulaOperationTreeValid] in *.
  - exact (rawStandardFormulaOpeningAfterShiftTree_valid M hPA
      numeralBound numeralCode depth fixed hnumeral).
  - exact I.
  - destruct hsupport as [hlhs hrhs]. split.
    + exact (raw_codedFormulaSubstitutionAtom_dynamicSourceTermContext
        M hPA numeralBound numeralCode depth lhs hnumeral hlhs).
    + exact (raw_codedFormulaSubstitutionAtom_dynamicSourceTermContext
        M hPA numeralBound numeralCode depth rhs hnumeral hrhs).
  - destruct hsupport as [hlhs hrhs]. repeat split.
    + apply rawRestrictedPADynamicSourceContextSubstitutionTree_depth.
    + apply rawRestrictedPADynamicSourceContextSubstitutionTree_depth.
    + exact (IHlhs depth hnumeral hlhs).
    + exact (IHrhs depth hnumeral hrhs).
  - destruct hsupport as [hlhs hrhs]. repeat split.
    + apply rawRestrictedPADynamicSourceContextSubstitutionTree_depth.
    + apply rawRestrictedPADynamicSourceContextSubstitutionTree_depth.
    + exact (IHlhs depth hnumeral hlhs).
    + exact (IHrhs depth hnumeral hrhs).
  - destruct hsupport as [hlhs hrhs]. repeat split.
    + apply rawRestrictedPADynamicSourceContextSubstitutionTree_depth.
    + apply rawRestrictedPADynamicSourceContextSubstitutionTree_depth.
    + exact (IHlhs depth hnumeral hlhs).
    + exact (IHrhs depth hnumeral hrhs).
  - split.
    + rewrite rawRestrictedPADynamicSourceContextSubstitutionTree_depth.
      reflexivity.
    + exact (IHchild (S depth) hnumeral hsupport).
  - split.
    + rewrite rawRestrictedPADynamicSourceContextSubstitutionTree_depth.
      reflexivity.
    + exact (IHchild (S depth) hnumeral hsupport).
  - contradiction.
Qed.

(** A small structural helper keeps the seven-node implication chain
    readable. *)
Lemma raw_formulaSubstitutionTreeValid_imp : forall
    M replacement depth left right,
  rawFormulaShiftTreeDepth M left = depth ->
  rawFormulaShiftTreeDepth M right = depth ->
  RawFormulaSubstitutionTreeValid M replacement left ->
  RawFormulaSubstitutionTreeValid M replacement right ->
  RawFormulaSubstitutionTreeValid M replacement
    (RFSTBinary M RFSBImp depth left right).
Proof.
  intros M replacement depth left right hleftDepth hrightDepth
    hleft hright.
  unfold RawFormulaSubstitutionTreeValid in *.
  cbn [RawFormulaOperationTreeValid]. tauto.
Qed.

(** The complete source tree, with the occurrence field as its sole dynamic
    subtree. *)
Definition rawRestrictedPADynamicSoundnessSubstitutionTree
    (M : RawPAModel) (numeralCode : M) : RawFormulaShiftTree M :=
  RFSTBinary M RFSBImp (raw_zero M)
    (rawStandardFormulaOpeningAfterShiftTree M 0
      (codedPAAxiomWitnessContextTermAt (tVar 2) (tVar 0)))
    (RFSTBinary M RFSBImp (raw_zero M)
      (rawRestrictedPADynamicSourceContextSubstitutionTree M numeralCode 0
        (restrictedTargetProofContext (tVar 1)))
      (RFSTBinary M RFSBImp (raw_zero M)
        (rawStandardFormulaOpeningAfterShiftTree M 0
          (proofAtomicallyAdequateTermAt (tVar 1)))
        (RFSTBinary M RFSBImp (raw_zero M)
          (rawStandardFormulaOpeningAfterShiftTree M 0
            (proofHasFormulaCoverageTermAt (tVar 1)))
          (RFSTBinary M RFSBImp (raw_zero M)
            (rawStandardFormulaOpeningAfterShiftTree M 0
              (proofRuleCoverageTermAt (tVar 1)))
            (RFSTBinary M RFSBImp (raw_zero M)
              (rawStandardFormulaOpeningAfterShiftTree M 0
                (proofRuleValidTermAt
                  (tVar 1) (tVar 0) rawFormulaBotCodeTerm))
              (RFSTBot M (raw_zero M))))))).

Lemma rawRestrictedPADynamicSoundnessSubstitutionTree_depth : forall
    M numeralCode,
  rawFormulaShiftTreeDepth M
    (rawRestrictedPADynamicSoundnessSubstitutionTree M numeralCode) =
  raw_zero M.
Proof. reflexivity. Qed.

Lemma rawRestrictedPADynamicSoundnessSubstitutionTree_source : forall
    M numeralCode,
  rawFormulaShiftTreeSource M
    (rawRestrictedPADynamicSoundnessSubstitutionTree M numeralCode) =
  rawRestrictedPADynamicSoundnessSourceCode M.
Proof.
  intros M numeralCode.
  unfold rawRestrictedPADynamicSoundnessSubstitutionTree,
    rawRestrictedPADynamicSoundnessSourceCode,
    restrictedPADynamicSoundnessSourceFormula,
    restrictedPADynamicOccurrenceSourceFormula.
  cbn [rawFormulaShiftTreeSource rawFormulaShiftBinaryCode
    rawQuotedFormulaCode].
  rewrite !rawStandardFormulaOpeningAfterShiftTree_source.
  rewrite rawRestrictedPADynamicSourceContextSubstitutionTree_source
    by exact restrictedPADynamicOccurrenceContext_shift_supported.
  rewrite rawRestrictedPADynamicSourceFormulaContextCode_quoted.
  reflexivity.
Qed.

Lemma rawRestrictedPADynamicSoundnessSubstitutionTree_target : forall
    M numeralCode,
  rawFormulaShiftTreeTarget M
    (rawRestrictedPADynamicSoundnessSubstitutionTree M numeralCode) =
  rawRestrictedPADynamicSoundnessImplicationCode M numeralCode.
Proof.
  intros M numeralCode.
  unfold rawRestrictedPADynamicSoundnessSubstitutionTree,
    rawRestrictedPADynamicSoundnessImplicationCode,
    rawRestrictedPAAxiomContextFieldCode,
    rawRestrictedPAOccurrenceBoundFieldCode,
    rawRestrictedPAAtomicAdequacyFieldCode,
    rawRestrictedPAFormulaCoverageFieldCode,
    rawRestrictedPARuleCoverageFieldCode,
    rawRestrictedPABottomEndpointFieldCode.
  cbn [rawFormulaShiftTreeTarget rawFormulaShiftBinaryCode].
  rewrite !rawStandardFormulaOpeningAfterShiftTree_target.
  rewrite rawRestrictedPADynamicSourceContextSubstitutionTree_target
    by exact restrictedPADynamicOccurrenceContext_shift_supported.
  reflexivity.
Qed.

Theorem rawRestrictedPADynamicSoundnessSubstitutionTree_valid : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    numeralBound numeralCode,
  RawNumeralTermCodeAt M numeralBound numeralCode ->
  RawFormulaSubstitutionTreeValid M numeralCode
    (rawRestrictedPADynamicSoundnessSubstitutionTree M numeralCode).
Proof.
  intros M hPA numeralBound numeralCode hnumeral.
  unfold rawRestrictedPADynamicSoundnessSubstitutionTree.
  repeat apply raw_formulaSubstitutionTreeValid_imp.
  all: try reflexivity.
  all: try apply rawStandardFormulaOpeningAfterShiftTree_depth.
  all: try apply rawRestrictedPADynamicSourceContextSubstitutionTree_depth.
  all: try solve
    [eapply (rawStandardFormulaOpeningAfterShiftTree_valid M hPA
        numeralBound numeralCode 0); exact hnumeral].
  all: try solve
    [exact (rawRestrictedPADynamicSourceContextSubstitutionTree_valid
      M hPA numeralBound numeralCode 0
      (restrictedTargetProofContext (tVar 1)) hnumeral
      restrictedPADynamicOccurrenceContext_shift_supported)].
Qed.

(** The advertised arbitrary-model source equation. *)
Theorem raw_codedRestrictedPADynamicSoundnessSource_substitution : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    numeralBound numeralCode,
  RawNumeralTermCodeAt M numeralBound numeralCode ->
  RawCodedFormulaSingleSubstitution M numeralCode
    (rawRestrictedPADynamicSoundnessSourceCode M)
    (rawRestrictedPADynamicSoundnessImplicationCode M numeralCode).
Proof.
  intros M hPA numeralBound numeralCode hnumeral.
  pose proof (raw_codedFormulaSingleSubstitution_of_valid_tree M hPA
    numeralCode
    (rawRestrictedPADynamicSoundnessSubstitutionTree M numeralCode)
    (rawRestrictedPADynamicSoundnessSubstitutionTree_depth M numeralCode)
    (rawRestrictedPADynamicSoundnessSubstitutionTree_valid M hPA
      numeralBound numeralCode hnumeral)) as hsubstitution.
  rewrite rawRestrictedPADynamicSoundnessSubstitutionTree_source
    in hsubstitution.
  rewrite rawRestrictedPADynamicSoundnessSubstitutionTree_target
    in hsubstitution.
  exact hsubstitution.
Qed.

End PABoundedRawCodedRestrictedPADynamicSoundnessSubstitution.
