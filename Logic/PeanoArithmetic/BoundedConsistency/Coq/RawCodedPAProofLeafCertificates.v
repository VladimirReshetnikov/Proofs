(**
  Ordinary PA-proof certificates built from coverage-certified raw leaves.

  [RawCodedProofLeafConstructors] establishes the internal proof-tree
  obligations.  Here those trees are paired with the empty witnessed-axiom
  context and packaged in the exact three-field certificate format used by
  [codedPAProvabilityTermAt].
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAListCoding Require Import ListCode.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedRestrictedProofStandardAdequacy
  RawCodedRestrictedPAProof
  RawCodedPAProvability
  RawCodedProofLeafConstructors.

Import ListNotations.

Module PABoundedRawCodedPAProofLeafCertificates.

Import PA.
Import PAListCode.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedRestrictedProofStandardAdequacy.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedProofLeafConstructors.

Lemma raw_codedPAAxiomWitnessContext_empty : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedPAAxiomWitnessContext M (raw_zero M) (raw_zero M).
Proof.
  intros M hPA.
  pose proof (raw_codedPAAxiomWitnessContext_standard M hPA []) as h.
  cbn [rawQuotedPAAxiomWitnessList rawQuotedContextCode
    rawListCode map] in h.
  exact h.
Qed.

Definition rawProofLemCertificate
    (M : RawPAModel) (body : M) : M :=
  rawCodeList3 M (rawNumeralValue M 0) (raw_zero M)
    (rawProofLemRoot M (raw_zero M) body).

Arguments rawProofLemCertificate M body : clear implicits.

(** Excluded middle is now an ordinary represented PA proof at an arbitrary
    (possibly nonstandard) formula-code parameter. *)
Theorem raw_codedPAProofOf_lem : forall
    (M : RawPAModel), RawPASatisfies M -> forall body,
  RawCodedPAProofOf M
    (rawProofLemConclusion M body)
    (rawProofLemCertificate M body).
Proof.
  intros M hPA body.
  exists (raw_zero M),
    (rawProofLemRoot M (raw_zero M) body), (raw_zero M).
  split.
  - unfold rawProofLemCertificate. reflexivity.
  - repeat split.
    + exact (raw_codedPAAxiomWitnessContext_empty M hPA).
    + exact (raw_proofLem_ruleCoverage M hPA (raw_zero M) body).
    + exact (raw_proofLem_endpoint M (raw_zero M) body).
Qed.

Corollary raw_codedPAProvability_lem : forall
    (M : RawPAModel), RawPASatisfies M -> forall body,
  exists certificate,
    RawCodedPAProofOf M
      (rawProofLemConclusion M body) certificate.
Proof.
  intros M hPA body.
  exists (rawProofLemCertificate M body).
  exact (raw_codedPAProofOf_lem M hPA body).
Qed.

End PABoundedRawCodedPAProofLeafCertificates.
