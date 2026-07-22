(**
  The genuinely one-variable dynamic-soundness induction predicate.

  The open source has four free slots: level 0 followed by the three checker
  parameters.  Rotate those slots to put the level at index 3, then close the
  three checker slots.  The resulting formula has only free variable 0 and
  can therefore be used by PA's induction scheme without the invalid
  diagonal-stability assumption that the unclosed checker parameters would
  require.
*)

From Stdlib Require Import Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedNumeralTermCode
  RawCodedFormulaOperationsStandardAdequacy
  RawCodedPAAxiomWitness
  RawCodedRestrictedPADynamicSoundnessSource
  RawCodedFormulaDiagonalOperationComposition
  RawCodedUniversalClosureDiagonalSubstitution
  RawCodedScopedFormulaDiagonalSubstitution
  RawCodedStandardFormulaScopeTransport
  RawCodedRestrictedPADynamicSoundnessSourceScope.

Module PABoundedRawCodedRestrictedPADynamicSoundnessInductionSyntax.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedFormulaOperationsStandardAdequacy.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedRestrictedPADynamicSoundnessSource.
Import PABoundedRawCodedFormulaDiagonalOperationComposition.
Import PABoundedRawCodedUniversalClosureDiagonalSubstitution.
Import PABoundedRawCodedScopedFormulaDiagonalSubstitution.
Import PABoundedRawCodedStandardFormulaScopeTransport.
Import PABoundedRawCodedRestrictedPADynamicSoundnessSourceScope.

Definition restrictedPADynamicSoundnessCheckerCount : nat := 3.

Definition restrictedPADynamicSoundnessInductionRenaming
    (index : nat) : nat :=
  match index with
  | 0 => restrictedPADynamicSoundnessCheckerCount
  | S predecessor => predecessor
  end.

Definition restrictedPADynamicSoundnessInductionOpenFormula : formula :=
  Formula.rename restrictedPADynamicSoundnessInductionRenaming
    restrictedPADynamicSoundnessSourceFormula.

Definition restrictedPADynamicSoundnessInductionSourceFormula : formula :=
  Formula.closeN restrictedPADynamicSoundnessCheckerCount
    restrictedPADynamicSoundnessInductionOpenFormula.

(** The source certificate is proved compositionally in the scope module;
    importing it here avoids normalizing the large quoted-code numerals. *)
Lemma restrictedPADynamicSoundnessSourceFormula_scoped_four :
  StandardFormulaScoped 4 restrictedPADynamicSoundnessSourceFormula.
Proof.
  exact PABoundedRawCodedRestrictedPADynamicSoundnessSourceScope.restrictedPADynamicSoundnessSourceFormula_scoped_four.
Qed.

Lemma restrictedPADynamicSoundnessInductionOpenFormula_scoped_four :
  StandardFormulaScoped 4
    restrictedPADynamicSoundnessInductionOpenFormula.
Proof.
  intros index hfree.
  unfold restrictedPADynamicSoundnessInductionOpenFormula in hfree.
  destruct (standardFormulaFree_rename_preimage
    restrictedPADynamicSoundnessSourceFormula
    restrictedPADynamicSoundnessInductionRenaming index hfree)
    as [[|sourceIndex] [hsource heq]].
  - cbn [restrictedPADynamicSoundnessInductionRenaming
      restrictedPADynamicSoundnessCheckerCount] in heq.
    subst index. exact (Nat.lt_succ_diag_r 3).
  - cbn [restrictedPADynamicSoundnessInductionRenaming] in heq.
    pose proof (restrictedPADynamicSoundnessSourceFormula_scoped_four
      (S sourceIndex) hsource) as hscope.
    lia.
Qed.

Theorem restrictedPADynamicSoundnessInductionSourceFormula_scoped :
  StandardFormulaScoped 1
    restrictedPADynamicSoundnessInductionSourceFormula.
Proof.
  intros index hfree.
  unfold restrictedPADynamicSoundnessInductionSourceFormula in hfree.
  pose proof (Formula.Free_closeN
    restrictedPADynamicSoundnessCheckerCount
    restrictedPADynamicSoundnessInductionOpenFormula index hfree)
    as hopen.
  pose proof
    (restrictedPADynamicSoundnessInductionOpenFormula_scoped_four
      (restrictedPADynamicSoundnessCheckerCount + index) hopen) as hscope.
  unfold restrictedPADynamicSoundnessCheckerCount in hscope. lia.
Qed.

Definition restrictedPADynamicSoundnessInductionShiftedFormula : formula :=
  standardPAAxiomInductionShifted
    restrictedPADynamicSoundnessInductionSourceFormula.

Definition restrictedPADynamicSoundnessInductionSuccessorFormula : formula :=
  standardPAAxiomInductionSuccessorInstance
    restrictedPADynamicSoundnessInductionSourceFormula.

Definition restrictedPADynamicSoundnessInductionZeroFormula : formula :=
  standardPAAxiomInductionZeroInstance
    restrictedPADynamicSoundnessInductionSourceFormula.

Definition restrictedPADynamicSoundnessInductionStepFormula : formula :=
  pAll (pImp
    restrictedPADynamicSoundnessInductionSourceFormula
    restrictedPADynamicSoundnessInductionSuccessorFormula).

Definition restrictedPADynamicSoundnessInductionBodyFormula : formula :=
  standardPAAxiomInductionBody
    restrictedPADynamicSoundnessInductionSourceFormula.

Definition restrictedPADynamicSoundnessInductionAxiomFormula : formula :=
  Formula.sealPA restrictedPADynamicSoundnessInductionBodyFormula.

Lemma restrictedPADynamicSoundnessInductionSuccessorFormula_scoped :
  StandardFormulaScoped 1
    restrictedPADynamicSoundnessInductionSuccessorFormula.
Proof.
  unfold restrictedPADynamicSoundnessInductionSuccessorFormula,
    standardPAAxiomInductionSuccessorInstance.
  rewrite standardFormulaShift_one_one_then_substitute_succ.
  apply (standardFormulaSubstitution_scoped 1 1
    restrictedPADynamicSoundnessInductionSourceFormula
    Formula.substSuccVar).
  - exact restrictedPADynamicSoundnessInductionSourceFormula_scoped.
  - intros [|sourceIndex] hindex; [|lia].
    intros index hfree.
    cbn [Formula.substSuccVar Term.Free] in hfree.
    lia.
Qed.

Lemma restrictedPADynamicSoundnessInductionZeroFormula_closed :
  StandardFormulaScoped 0
    restrictedPADynamicSoundnessInductionZeroFormula.
Proof.
  unfold restrictedPADynamicSoundnessInductionZeroFormula,
    standardPAAxiomInductionZeroInstance.
  rewrite standardFormulaSingleSubstitution_zero.
  apply (standardFormulaSubstitution_scoped 1 0
    restrictedPADynamicSoundnessInductionSourceFormula
    (Formula.instTerm tZero)).
  - exact restrictedPADynamicSoundnessInductionSourceFormula_scoped.
  - intros [|sourceIndex] hindex; [|lia].
    intros index hfree.
    cbn [Formula.instTerm Term.Free] in hfree. contradiction.
Qed.

Lemma restrictedPADynamicSoundnessInductionBodyFormula_closed :
  StandardFormulaScoped 0
    restrictedPADynamicSoundnessInductionBodyFormula.
Proof.
  unfold restrictedPADynamicSoundnessInductionBodyFormula,
    standardPAAxiomInductionBody.
  intros index hfree.
  cbn [Formula.Free] in hfree.
  destruct hfree as [[hzero | hstep] | hsource].
  - exact (restrictedPADynamicSoundnessInductionZeroFormula_closed
      index hzero).
  - destruct hstep as [hsource | hsuccessor].
    + pose proof
        (restrictedPADynamicSoundnessInductionSourceFormula_scoped
          (S index) hsource). lia.
    + pose proof
        (restrictedPADynamicSoundnessInductionSuccessorFormula_scoped
          (S index) hsuccessor). lia.
  - pose proof
      (restrictedPADynamicSoundnessInductionSourceFormula_scoped
        (S index) hsource). lia.
Qed.

Theorem raw_codedRestrictedPADynamicSoundnessInductionBody_diagonal : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    numeralBound numeralCode,
  RawNumeralTermCodeAt M numeralBound numeralCode ->
  RawCodedFormulaDiagonalSubstitutionAtAllDepths M numeralCode
    (rawQuotedFormulaCode M
      restrictedPADynamicSoundnessInductionBodyFormula).
Proof.
  intros M hPA numeralBound numeralCode hnumeral.
  unfold restrictedPADynamicSoundnessInductionBodyFormula,
    standardPAAxiomInductionBody.
  apply (raw_codedFormulaDiagonalSubstitutionAtAllDepths_inductionBody
    M hPA numeralCode
    (rawQuotedFormulaCode M
      restrictedPADynamicSoundnessInductionSourceFormula)
    (rawQuotedFormulaCode M
      restrictedPADynamicSoundnessInductionSuccessorFormula)
    (rawQuotedFormulaCode M
      restrictedPADynamicSoundnessInductionZeroFormula)).
  - exact (raw_codedFormulaDiagonalSubstitution_standard_positive
      M hPA numeralBound numeralCode
      restrictedPADynamicSoundnessInductionSourceFormula hnumeral
      restrictedPADynamicSoundnessInductionSourceFormula_scoped).
  - exact (raw_codedFormulaDiagonalSubstitution_standard_positive
      M hPA numeralBound numeralCode
      restrictedPADynamicSoundnessInductionSuccessorFormula hnumeral
      restrictedPADynamicSoundnessInductionSuccessorFormula_scoped).
  - exact (raw_codedFormulaDiagonalSubstitution_standard_closed
      M hPA numeralBound numeralCode
      restrictedPADynamicSoundnessInductionZeroFormula hnumeral
      restrictedPADynamicSoundnessInductionZeroFormula_closed).
Qed.

End PABoundedRawCodedRestrictedPADynamicSoundnessInductionSyntax.
