(**
  The fixed one-free-variable source for dynamic restricted-PA soundness.

  The dynamic implication used after the three checker witnesses have been
  opened has free variables 0, 1, and 2 for the proof context, proof root,
  and witness list.  To induct on the restriction level we insert a new free
  variable at index zero.  Every old free variable is shifted once, while a
  level hole occurring below [d] binders becomes variable [d].  Opening that
  distinguished variable with a closed numeral therefore recovers the exact
  existing implication.

  This file is deliberately metasyntactic: it fixes the formula and proves
  the exact host-level substitution equation.  The following downstream
  realization supplies beta-coded substitution certificates for possibly
  nonstandard numeral terms.
*)

From Stdlib Require Import Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax RawCodedSyntaxConstructors RawCodedFormulaOperations
  RawCodedTermOperationsStandardAdequacy
  RawCodedFormulaOperationsStandardAdequacy
  RawCodedProofAtomicAdequacy RawCodedProofFormulaCoverage
  RawCodedProofRuleCoverage RawCodedProofRules
  RawCodedRestrictedPAProof
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedRestrictedTargetFormulaShift
  RawCodedRestrictedPAConsistencyOpenDescent
  RawCodedRestrictedPADynamicSoundnessComposition.

Module PABoundedRawCodedRestrictedPADynamicSoundnessSource.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedTermOperationsStandardAdequacy.
Import PABoundedRawCodedFormulaOperationsStandardAdequacy.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedProofFormulaCoverage.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedRestrictedTargetFormulaShift.
Import PABoundedRawCodedRestrictedPAConsistencyOpenDescent.
Import PABoundedRawCodedRestrictedPADynamicSoundnessComposition.

(** Insert a new free variable below [depth] binders.  Unlike ordinary
    context instantiation, the hole is not assumed closed: its de Bruijn code
    is lifted to [depth], preventing capture by the context's quantifiers. *)
Fixpoint restrictedPADynamicSourceTermContext
    (depth : nat) (context : RestrictedTargetTermContext) : term :=
  match context with
  | RTTCFixed fixed => standardTermShift depth 1 fixed
  | RTTCHole => tVar depth
  | RTTCSucc child =>
      tSucc (restrictedPADynamicSourceTermContext depth child)
  | RTTCAdd lhs rhs =>
      tAdd
        (restrictedPADynamicSourceTermContext depth lhs)
        (restrictedPADynamicSourceTermContext depth rhs)
  | RTTCMul lhs rhs =>
      tMul
        (restrictedPADynamicSourceTermContext depth lhs)
        (restrictedPADynamicSourceTermContext depth rhs)
  end.

Fixpoint restrictedPADynamicSourceFormulaContext
    (depth : nat) (context : RestrictedTargetFormulaContext) : formula :=
  match context with
  | RTFCFixed fixed => standardFormulaShift depth 1 fixed
  | RTFCBot => pBot
  | RTFCEq lhs rhs =>
      pEq
        (restrictedPADynamicSourceTermContext depth lhs)
        (restrictedPADynamicSourceTermContext depth rhs)
  | RTFCImp lhs rhs =>
      pImp
        (restrictedPADynamicSourceFormulaContext depth lhs)
        (restrictedPADynamicSourceFormulaContext depth rhs)
  | RTFCAnd lhs rhs =>
      pAnd
        (restrictedPADynamicSourceFormulaContext depth lhs)
        (restrictedPADynamicSourceFormulaContext depth rhs)
  | RTFCOr lhs rhs =>
      pOr
        (restrictedPADynamicSourceFormulaContext depth lhs)
        (restrictedPADynamicSourceFormulaContext depth rhs)
  | RTFCAll child =>
      pAll (restrictedPADynamicSourceFormulaContext (S depth) child)
  | RTFCEx child =>
      pEx (restrictedPADynamicSourceFormulaContext (S depth) child)
  | RTFCSeal _ => pBot
  end.

(** The only level-dependent field of the six-premise implication. *)
Definition restrictedPADynamicOccurrenceSourceFormula : formula :=
  restrictedPADynamicSourceFormulaContext 0
    (restrictedTargetProofContext (tVar 1)).

(** The exact endpoint formula when its level is represented by an ordinary
    closed term.  The raw endpoint below remains meaningful for nonstandard
    numeral-term codes as well. *)
Definition restrictedPADynamicSoundnessImplicationFormula
    (levelTerm : term) : formula :=
  pImp
    (codedPAAxiomWitnessContextTermAt (tVar 2) (tVar 0))
    (pImp
      (instantiateRestrictedTargetFormulaContext levelTerm
        (restrictedTargetProofContext (tVar 1)))
      (pImp
        (proofAtomicallyAdequateTermAt (tVar 1))
        (pImp
          (proofHasFormulaCoverageTermAt (tVar 1))
          (pImp
            (proofRuleCoverageTermAt (tVar 1))
            (pImp
              (proofRuleValidTermAt
                (tVar 1) (tVar 0) rawFormulaBotCodeTerm)
              pBot))))).

(** Shift the five fixed endpoint fields, and use the capture-avoiding hole
    insertion above for the occurrence-bound field. *)
Definition restrictedPADynamicSoundnessSourceFormula : formula :=
  pImp
    (standardFormulaShift 0 1
      (codedPAAxiomWitnessContextTermAt (tVar 2) (tVar 0)))
    (pImp
      restrictedPADynamicOccurrenceSourceFormula
      (pImp
        (standardFormulaShift 0 1
          (proofAtomicallyAdequateTermAt (tVar 1)))
        (pImp
          (standardFormulaShift 0 1
            (proofHasFormulaCoverageTermAt (tVar 1)))
          (pImp
            (standardFormulaShift 0 1
              (proofRuleCoverageTermAt (tVar 1)))
            (pImp
              (standardFormulaShift 0 1
                (proofRuleValidTermAt
                  (tVar 1) (tVar 0) rawFormulaBotCodeTerm))
              pBot))))).

Definition rawRestrictedPADynamicSoundnessSourceCode
    (M : RawPAModel) : M :=
  rawQuotedFormulaCode M restrictedPADynamicSoundnessSourceFormula.

Arguments rawRestrictedPADynamicSoundnessSourceCode M : clear implicits.

(** Shifting by one at a cutoff and then opening that cutoff is an exact
    syntactic inverse.  The replacement is never used: shifted variables at
    or above the cutoff become strict successors and take opening's third
    branch. *)
Lemma standardTermOpening_after_shift_one : forall
    cutoff liftedReplacement input,
  standardTermOpening cutoff liftedReplacement
    (standardTermShift cutoff 1 input) = input.
Proof.
  intros cutoff liftedReplacement input.
  induction input as [index | | child IH | lhs IHlhs rhs IHrhs |
      lhs IHlhs rhs IHrhs]; cbn [standardTermShift standardTermOpening].
  - destruct (index <? cutoff) eqn:hlow.
    + cbn [standardTermOpening]. now rewrite hlow.
    + apply Nat.ltb_ge in hlow.
      assert (hshiftLow : (index + 1 <? cutoff) = false)
        by (apply Nat.ltb_ge; lia).
      assert (hshiftEq : (index + 1 =? cutoff) = false)
        by (apply Nat.eqb_neq; lia).
      cbn [standardTermOpening].
      rewrite hshiftLow, hshiftEq.
      f_equal. lia.
  - reflexivity.
  - now rewrite IH.
  - now rewrite IHlhs, IHrhs.
  - now rewrite IHlhs, IHrhs.
Qed.

Lemma standardFormulaSingleSubstitution_after_shift_one : forall
    replacement depth input,
  standardFormulaSingleSubstitution replacement depth
    (standardFormulaShift depth 1 input) = input.
Proof.
  intros replacement depth input. revert depth.
  induction input as [lhs rhs | | lhs IHlhs rhs IHrhs |
      lhs IHlhs rhs IHrhs | lhs IHlhs rhs IHrhs |
      child IHchild | child IHchild]; intro depth;
    cbn [standardFormulaShift standardFormulaSingleSubstitution].
  - now rewrite !standardTermOpening_after_shift_one.
  - reflexivity.
  - now rewrite IHlhs, IHrhs.
  - now rewrite IHlhs, IHrhs.
  - now rewrite IHlhs, IHrhs.
  - now rewrite IHchild.
  - now rewrite IHchild.
Qed.

Lemma standardTermShift_numeral_any : forall depth level,
  standardTermShift 0 depth (Term.numeral level) = Term.numeral level.
Proof.
  intros depth level.
  rewrite standardTermShift_as_rename, Term.rename_numeral.
  reflexivity.
Qed.

Lemma restrictedPADynamicSourceTermContext_substitute_numeral : forall
    level depth context,
  standardTermOpening depth
    (standardTermShift 0 depth (Term.numeral level))
    (restrictedPADynamicSourceTermContext depth context) =
  instantiateRestrictedTargetTermContext (Term.numeral level) context.
Proof.
  intros level depth context.
  induction context as [fixed | | child IH | lhs IHlhs rhs IHrhs |
      lhs IHlhs rhs IHrhs];
    cbn [restrictedPADynamicSourceTermContext
      instantiateRestrictedTargetTermContext standardTermOpening].
  - apply standardTermOpening_after_shift_one.
  - rewrite Nat.ltb_irrefl, Nat.eqb_refl.
    apply standardTermShift_numeral_any.
  - now rewrite IH.
  - now rewrite IHlhs, IHrhs.
  - now rewrite IHlhs, IHrhs.
Qed.

Lemma restrictedPADynamicSourceFormulaContext_substitute_numeral : forall
    level depth context,
  RestrictedTargetFormulaContextShiftSupported context ->
  standardFormulaSingleSubstitution (Term.numeral level) depth
    (restrictedPADynamicSourceFormulaContext depth context) =
  instantiateRestrictedTargetFormulaContext (Term.numeral level) context.
Proof.
  intros level depth context. revert depth.
  induction context as [fixed | | lhs rhs | lhs IHlhs rhs IHrhs |
      lhs IHlhs rhs IHrhs | lhs IHlhs rhs IHrhs |
      child IHchild | child IHchild | child IHchild];
    intros depth hsupport;
    cbn [RestrictedTargetFormulaContextShiftSupported
      restrictedPADynamicSourceFormulaContext
      instantiateRestrictedTargetFormulaContext
      standardFormulaSingleSubstitution] in *.
  - apply standardFormulaSingleSubstitution_after_shift_one.
  - reflexivity.
  - destruct hsupport as [hlhs hrhs].
    now rewrite !restrictedPADynamicSourceTermContext_substitute_numeral.
  - destruct hsupport as [hlhs hrhs]. now rewrite IHlhs, IHrhs.
  - destruct hsupport as [hlhs hrhs]. now rewrite IHlhs, IHrhs.
  - destruct hsupport as [hlhs hrhs]. now rewrite IHlhs, IHrhs.
  - now rewrite IHchild.
  - now rewrite IHchild.
  - contradiction.
Qed.

Lemma restrictedPADynamicOccurrenceContext_shift_supported :
  RestrictedTargetFormulaContextShiftSupported
    (restrictedTargetProofContext (tVar 1)).
Proof.
  unfold restrictedTargetProofContext,
    restrictedTargetProofCertificateWithSupportContext,
    restrictedTargetProofTraversalContext,
    restrictedTargetProofConstructorOccurrencesBoundedContext,
    restrictedTargetProofOccurrenceCasesBoundedContext,
    restrictedTargetProofFormulaFieldsBoundedContext,
    restrictedTargetContextAllBoundedContext,
    restrictedTargetContextAllBoundedWithTablesContext,
    restrictedTargetFormulaQuantifierBoundedContext,
    restrictedTargetSigmaDomainContext,
    restrictedTargetPiDomainContext,
    restrictedTargetLeContext.
  cbn [restrictedTargetExN restrictedTargetAllN
    RestrictedTargetFormulaContextShiftSupported
    RestrictedTargetTermContextShiftSupported].
  repeat split; exact I.
Qed.

(** The promised exact source equation. *)
Theorem restrictedPADynamicSoundnessSourceFormula_substitute_numeral :
    forall level,
  standardFormulaSingleSubstitution (Term.numeral level) 0
    restrictedPADynamicSoundnessSourceFormula =
  restrictedPADynamicSoundnessImplicationFormula (Term.numeral level).
Proof.
  intro level.
  unfold restrictedPADynamicSoundnessSourceFormula,
    restrictedPADynamicSoundnessImplicationFormula,
    restrictedPADynamicOccurrenceSourceFormula.
  cbn [standardFormulaSingleSubstitution].
  rewrite !standardFormulaSingleSubstitution_after_shift_one.
  rewrite (restrictedPADynamicSourceFormulaContext_substitute_numeral
    level 0 (restrictedTargetProofContext (tVar 1))
    restrictedPADynamicOccurrenceContext_shift_supported).
  reflexivity.
Qed.

(** At every ordinary numeral, the existing carrier-level endpoint is the
    quotation of the formula displayed above. *)
Theorem raw_restrictedPADynamicSoundnessImplicationCode_standard : forall
    (M : RawPAModel) level,
  rawRestrictedPADynamicSoundnessImplicationCode M
    (rawQuotedTermCode M (Term.numeral level)) =
  rawQuotedFormulaCode M
    (restrictedPADynamicSoundnessImplicationFormula (Term.numeral level)).
Proof.
  intros M level.
  unfold rawRestrictedPADynamicSoundnessImplicationCode,
    restrictedPADynamicSoundnessImplicationFormula,
    rawRestrictedPAAxiomContextFieldCode,
    rawRestrictedPAOccurrenceBoundFieldCode,
    rawRestrictedPAAtomicAdequacyFieldCode,
    rawRestrictedPAFormulaCoverageFieldCode,
    rawRestrictedPARuleCoverageFieldCode,
    rawRestrictedPABottomEndpointFieldCode.
  rewrite (rawRestrictedTargetFormulaContextCode_quoted M
    (Term.numeral level)).
  - reflexivity.
  - induction level; cbn [Term.numeral Term.bound].
    + reflexivity.
    + exact IHlevel.
Qed.

End PABoundedRawCodedRestrictedPADynamicSoundnessSource.
