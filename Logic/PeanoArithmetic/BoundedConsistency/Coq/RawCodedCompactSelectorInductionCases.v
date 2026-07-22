(**
  Semantic and proof-theoretic interfaces for the two selector-induction
  cases.

  The zero case is unconditional: the established proof of [Con_0(PA)] can
  be quoted into the compact package.  The successor case is characterized
  exactly by the already isolated proof-certificate transformer.  This file
  therefore contributes a genuine base theorem while making sure that no
  semantic reflection premise is hidden in the step formulation.
*)

From Stdlib Require Import Arith Lia FunctionalExtensionality.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax RawModelCompleteness RawCodedPAProvability
  RawCodedFormulaOperationsStandardAdequacy RawCodedPAAxiomWitness
  CompactPAUniformProvability
  RawCodedCompactSelectorInductionSyntax.

Module PABoundedRawCodedCompactSelectorInductionCases.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedFormulaOperationsStandardAdequacy.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedCompactPAUniformProvability.
Import PABoundedRawCodedCompactSelectorInductionSyntax.

Lemma compactSelectorInductionZeroFormula_sentence :
  Formula.Sentence compactSelectorInductionZeroFormula.
Proof.
  intros index hfree.
  pose proof (compactSelectorInductionZeroFormula_closed index hfree).
  lia.
Qed.

Lemma compactSelectorInductionStepFormula_sentence :
  Formula.Sentence compactSelectorInductionStepFormula.
Proof.
  intros index hfree.
  unfold compactSelectorInductionStepFormula in hfree.
  cbn [Formula.Free] in hfree.
  destruct hfree as [hsource | hsuccessor].
  - pose proof (compactSelectorInductionSourceFormula_scoped
      (S index) hsource). lia.
  - pose proof (compactSelectorInductionSuccessorFormula_scoped
      (S index) hsuccessor). lia.
Qed.

(** Raw substitution by [substSuccVar] advances the distinguished package
    level and leaves the tail environment untouched. *)
Lemma raw_sat_compactSelectorInductionSuccessorFormula_iff : forall
    (M : RawPAModel) (tail : nat -> M) level,
  raw_formula_sat M (scons M level tail)
    compactSelectorInductionSuccessorFormula <->
  RawCompactSelectorPackageAt M tail (raw_succ M level).
Proof.
  intros M tail level.
  unfold compactSelectorInductionSuccessorFormula,
    compactSelectorInductionSourceFormula,
    standardPAAxiomInductionSuccessorInstance.
  rewrite standardFormulaShift_one_one_then_substitute_succ.
  rewrite raw_formula_sat_subst.
  rewrite (raw_formula_sat_ext M compactSelectorPackageFormula
    (fun n => raw_term_eval M (scons M level tail)
      (Formula.substSuccVar n))
    (scons M (raw_succ M level) tail)).
  - exact (raw_sat_compactSelectorPackageFormula_iff
      M tail (raw_succ M level)).
  - intros [|index]; reflexivity.
Qed.

Lemma raw_sat_compactSelectorInductionZeroFormula_iff : forall
    (M : RawPAModel) (tail : nat -> M),
  raw_formula_sat M tail compactSelectorInductionZeroFormula <->
  RawCompactSelectorPackageAt M tail (raw_zero M).
Proof.
  intros M tail.
  unfold compactSelectorInductionZeroFormula,
    compactSelectorInductionSourceFormula,
    standardPAAxiomInductionZeroInstance.
  rewrite standardFormulaSingleSubstitution_zero.
  rewrite raw_formula_sat_instTerm.
  cbn [raw_term_eval].
  exact (raw_sat_compactSelectorPackageFormula_iff
    M tail (raw_zero M)).
Qed.

(** The closed step formula has precisely the intended arbitrary-model
    meaning: it advances every package at the current carrier element. *)
Theorem raw_sat_compactSelectorInductionStepFormula_iff : forall
    (M : RawPAModel) (tail : nat -> M),
  raw_formula_sat M tail compactSelectorInductionStepFormula <->
  forall level,
    RawCompactSelectorPackageAt M tail level ->
    RawCompactSelectorPackageAt M tail (raw_succ M level).
Proof.
  intros M tail.
  unfold compactSelectorInductionStepFormula.
  cbn [raw_formula_sat].
  split.
  - intros hstep level hpackage.
    apply (proj1
      (raw_sat_compactSelectorInductionSuccessorFormula_iff
        M tail level)).
    apply (hstep level).
    exact (proj2
      (@raw_sat_compactSelectorPackageFormula_iff M tail level)
      hpackage).
  - intros hstep level hpackage.
    apply (proj2
      (raw_sat_compactSelectorInductionSuccessorFormula_iff
        M tail level)).
    apply hstep.
    exact (proj1
      (@raw_sat_compactSelectorPackageFormula_iff M tail level)
      hpackage).
Qed.

(** The base induction case is an actual PA theorem, with no compiler
    premise. *)
Theorem PA_BProv_compactSelectorInductionZeroFormula :
  Formula.BProv Formula.Ax_s nil compactSelectorInductionZeroFormula.
Proof.
  apply PA_BProv_of_raw_valid.
  - exact compactSelectorInductionZeroFormula_sentence.
  - intros M hPA tail.
    apply (proj2 (raw_sat_compactSelectorInductionZeroFormula_iff M tail)).
    exact (raw_compactSelectorPackage_zero M hPA tail).
Qed.

Corollary raw_codedPAProofOf_compactSelectorInductionZeroFormula : forall
    (M : RawPAModel), RawPASatisfies M ->
  exists certificate,
    RawCodedPAProofOf M
      (rawNumeralValue M
        (formulaCode compactSelectorInductionZeroFormula))
      certificate.
Proof.
  intros M hPA.
  exact (raw_codedPAProofOf_of_BProv M hPA
    compactSelectorInductionZeroFormula
    PA_BProv_compactSelectorInductionZeroFormula).
Qed.

(** This equivalence prevents the induction step from being weakened into a
    mere package-existence assumption.  Every supplied lower certificate is
    passed to the exact proof successor, and conversely its witnesses give
    the semantic step. *)
Theorem raw_compactSelectorInductionStep_exact : forall
    (M : RawPAModel),
  RawRestrictedPAConsistencyProofSuccessor M <->
  forall tail,
    raw_formula_sat M tail compactSelectorInductionStepFormula.
Proof.
  intros M. split.
  - intros hsuccessor tail.
    apply (proj2
      (raw_sat_compactSelectorInductionStepFormula_iff M tail)).
    intros level [target [certificate [htarget hcertificate]]].
    exact (hsuccessor level target certificate htarget hcertificate).
  - intros hstep level target certificate htarget hcertificate.
    pose (tail := fun _ : nat => raw_zero M).
    pose proof (proj1
      (raw_sat_compactSelectorInductionStepFormula_iff M tail)
      (hstep tail)) as hsemantic.
    exact (hsemantic level
      (ex_intro _ target
        (ex_intro _ certificate (conj htarget hcertificate)))).
Qed.

Corollary PA_BProv_compactSelectorInductionStepFormula :
    RawRestrictedPAConsistencyProofSuccessorInAllModels ->
  Formula.BProv Formula.Ax_s nil compactSelectorInductionStepFormula.
Proof.
  intro hsuccessor.
  apply PA_BProv_of_raw_valid.
  - exact compactSelectorInductionStepFormula_sentence.
  - intros M hPA tail.
    exact (proj1 (raw_compactSelectorInductionStep_exact M)
      (hsuccessor M hPA) tail).
Qed.

End PABoundedRawCodedCompactSelectorInductionCases.
