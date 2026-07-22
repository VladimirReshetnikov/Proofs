(**
  Ordinary PA-proof certificates built by unary raw-proof constructors.

  Bottom elimination is the key bridge from an arbitrary coded proof of
  falsity to a coded proof of any requested target.  The witnessed PA-axiom
  list and its context are reused unchanged; only the proof root is replaced
  by the coverage-certified parent from [RawCodedProofUnaryConstructors].
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedRestrictedPAProof
  RawCodedProofEndpoints RawCodedProofRuleCoverage
  RawCodedPAProvability RawCodedProofUnaryConstructors.

Module PABoundedRawCodedPAProofUnaryCertificates.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedProofUnaryConstructors.

Definition rawProofBotECertificate (M : RawPAModel)
    (witnessList context conclusion child : M) : M :=
  rawCodeList3 M (rawNumeralValue M 0) witnessList
    (rawProofBotERoot M context conclusion child).

Arguments rawProofBotECertificate
  M witnessList context conclusion child : clear implicits.

(** Field-level packaging is useful to later compilers that already carry
    the decoded components of a [RawCodedPAProofOf] certificate. *)
Theorem raw_codedPAProofOf_botE_from_fields : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      witnessList context conclusion child,
  RawCodedPAAxiomWitnessContext M witnessList context ->
  RawProofRuleCoverage M child ->
  RawProofEndpoint M child context (rawFormulaBotCode M) ->
  RawCodedPAProofOf M conclusion
    (rawProofBotECertificate M
      witnessList context conclusion child).
Proof.
  intros M hPA witnessList context conclusion child
    hwitness hcoverage hendpoint.
  exists witnessList,
    (rawProofBotERoot M context conclusion child), context.
  split.
  - unfold rawProofBotECertificate. reflexivity.
  - repeat split.
    + exact hwitness.
    + exact (raw_proofBotE_ruleCoverage M hPA
        context conclusion child hcoverage hendpoint).
    + exact (raw_proofBotE_endpoint M context conclusion child).
Qed.

(** Public ex-falso compiler for represented ordinary PA proofs. *)
Theorem raw_codedPAProofOf_botE : forall
    (M : RawPAModel), RawPASatisfies M -> forall certificate,
  RawCodedPAProofOf M (rawFormulaBotCode M) certificate ->
  forall conclusion,
  exists nextCertificate,
    RawCodedPAProofOf M conclusion nextCertificate.
Proof.
  intros M hPA certificate
    (witnessList & child & context & _ &
      hwitness & hcoverage & hendpoint)
    conclusion.
  exists (rawProofBotECertificate M
    witnessList context conclusion child).
  exact (raw_codedPAProofOf_botE_from_fields M hPA
    witnessList context conclusion child
    hwitness hcoverage hendpoint).
Qed.

Corollary raw_codedPAProvability_botE : forall
    (M : RawPAModel), RawPASatisfies M ->
  (exists certificate,
    RawCodedPAProofOf M (rawFormulaBotCode M) certificate) ->
  forall conclusion,
  exists certificate, RawCodedPAProofOf M conclusion certificate.
Proof.
  intros M hPA [certificate hcertificate] conclusion.
  exact (raw_codedPAProofOf_botE M hPA
    certificate hcertificate conclusion).
Qed.

End PABoundedRawCodedPAProofUnaryCertificates.
