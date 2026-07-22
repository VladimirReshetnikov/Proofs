(**
  Ordinary PA-proof certificates built by universal introduction.

  The general wrapper exposes the exact shifted-context side condition of
  [RP_allI].  A closed specialization then uses the proved fact that the
  empty coded context shifts to itself.  This is the form needed after a
  local contradiction proof has discharged its temporary assumption and the
  resulting implication must be universally quantified.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedContextShift
  RawCodedRestrictedPAProof RawCodedProofEndpoints
  RawCodedProofRuleCoverage RawCodedPAProvability
  RawCodedProofImpIConstructor RawCodedProofAllIConstructor
  RawCodedPAProofLeafCertificates RawCodedPAOpenProofComposition.

Module PABoundedRawCodedPAProofAllICertificates.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedProofImpIConstructor.
Import PABoundedRawCodedProofAllIConstructor.
Import PABoundedRawCodedPAProofLeafCertificates.
Import PABoundedRawCodedPAOpenProofComposition.

Definition rawProofAllICertificate (M : RawPAModel)
    (witnessList context body child : M) : M :=
  rawCodeList3 M (rawNumeralValue M 0) witnessList
    (rawProofAllIRoot M context body child).

Arguments rawProofAllICertificate
  M witnessList context body child : clear implicits.

Theorem raw_codedPAProofOf_allI_from_fields : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      witnessList context shiftedContext body child,
  RawCodedPAAxiomWitnessContext M witnessList context ->
  RawContextShift M context shiftedContext ->
  RawProofRuleCoverage M child ->
  RawProofEndpoint M child shiftedContext body ->
  RawCodedPAProofOf M (rawFormulaAllCode M body)
    (rawProofAllICertificate M witnessList context body child).
Proof.
  intros M hPA witnessList context shiftedContext body child
    hwitness hcontextShift hcoverage hendpoint.
  exists witnessList, (rawProofAllIRoot M context body child), context.
  split.
  - unfold rawProofAllICertificate. reflexivity.
  - repeat split.
    + exact hwitness.
    + exact (raw_proofAllI_ruleCoverage M hPA
        context shiftedContext body child
        hcontextShift hcoverage hendpoint).
    + exact (raw_proofAllI_endpoint M context body child).
Qed.

Definition rawProofAllIEmptyCertificate
    (M : RawPAModel) (body child : M) : M :=
  rawProofAllICertificate M
    (raw_zero M) (raw_zero M) body child.

Arguments rawProofAllIEmptyCertificate M body child : clear implicits.

(** Closed-context specialization used to quantify the certificate variable
    in the consistency body. *)
Theorem raw_codedPAProofOf_allI_empty_from_fields : forall
    (M : RawPAModel), RawPASatisfies M -> forall body child,
  RawProofRuleCoverage M child ->
  RawProofEndpoint M child (raw_zero M) body ->
  RawCodedPAProofOf M (rawFormulaAllCode M body)
    (rawProofAllIEmptyCertificate M body child).
Proof.
  intros M hPA body child hcoverage hendpoint.
  unfold rawProofAllIEmptyCertificate.
  exact (raw_codedPAProofOf_allI_from_fields M hPA
    (raw_zero M) (raw_zero M) (raw_zero M) body child
    (raw_codedPAAxiomWitnessContext_empty M hPA)
    (raw_contextShift_empty M hPA)
    hcoverage hendpoint).
Qed.

(** The exact consistency-body proof root: first discharge the candidate
    restricted-proof assumption, then quantify its certificate variable. *)
Definition rawProofUniversalOpenNegationRoot (M : RawPAModel)
    (assumption child : M) : M :=
  rawProofAllIRoot M (raw_zero M)
    (rawFormulaImpCode M assumption (rawFormulaBotCode M))
    (rawProofImpIRoot M (raw_zero M)
      assumption (rawFormulaBotCode M) child).

Arguments rawProofUniversalOpenNegationRoot
  M assumption child : clear implicits.

Definition rawProofUniversalOpenNegationCertificate (M : RawPAModel)
    (assumption child : M) : M :=
  rawCodeList3 M (rawNumeralValue M 0) (raw_zero M)
    (rawProofUniversalOpenNegationRoot M assumption child).

Arguments rawProofUniversalOpenNegationCertificate
  M assumption child : clear implicits.

Theorem raw_codedPAProofOf_universal_negation_of_open_bottom : forall
    (M : RawPAModel), RawPASatisfies M -> forall assumption child,
  RawCodedPAOpenProofOf M
    (raw_zero M) (raw_zero M) assumption (rawFormulaBotCode M) child ->
  RawCodedPAProofOf M
    (rawFormulaAllCode M
      (rawFormulaImpCode M assumption (rawFormulaBotCode M)))
    (rawProofUniversalOpenNegationCertificate M assumption child).
Proof.
  intros M hPA assumption child [_ [hcoverage hendpoint]].
  unfold rawProofUniversalOpenNegationCertificate,
    rawProofUniversalOpenNegationRoot,
    rawProofAllIEmptyCertificate, rawProofAllICertificate.
  apply (raw_codedPAProofOf_allI_empty_from_fields M hPA
    (rawFormulaImpCode M assumption (rawFormulaBotCode M))
    (rawProofImpIRoot M (raw_zero M)
      assumption (rawFormulaBotCode M) child)).
  - exact (raw_proofImpI_ruleCoverage M hPA
      (raw_zero M) assumption (rawFormulaBotCode M) child
      hcoverage hendpoint).
  - exact (raw_proofImpI_endpoint M
      (raw_zero M) assumption (rawFormulaBotCode M) child).
Qed.

(** This is the remaining substantive local compiler seam, stated without
    disguise: once an open contradiction root exists, all proof constructors
    needed to package the quantified consistency body are now concrete. *)
Corollary raw_codedPAProvability_universal_negation_of_open_bottom : forall
    (M : RawPAModel), RawPASatisfies M -> forall assumption,
  RawCodedPAOpenProvability M
    (raw_zero M) (raw_zero M) assumption (rawFormulaBotCode M) ->
  exists certificate,
    RawCodedPAProofOf M
      (rawFormulaAllCode M
        (rawFormulaImpCode M assumption (rawFormulaBotCode M)))
      certificate.
Proof.
  intros M hPA assumption [child hopen].
  exists (rawProofUniversalOpenNegationCertificate M assumption child).
  exact (raw_codedPAProofOf_universal_negation_of_open_bottom M hPA
    assumption child hopen).
Qed.

End PABoundedRawCodedPAProofAllICertificates.
