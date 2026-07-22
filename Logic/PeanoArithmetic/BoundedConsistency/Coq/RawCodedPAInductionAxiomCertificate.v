(**
  A genuine PA proof certificate for an induction axiom over an arbitrary
  model-coded source formula.

  Standard quotation is insufficient for a uniform truth compiler: at a
  nonstandard hierarchy stage the induction predicate itself has a
  nonstandard formula code.  [RawCodedPAAxiomInduction] is the transparent
  graph certifying the shift, the zero/successor instances, the induction
  body, its closure bound, and its universal closure.  This module turns that
  graph witness into an actual PA-axiom witness, extends any existing
  witnessed PA context by it, and builds the covered assumption leaf.

  Thus the theorem below does not postulate an induction rule for arbitrary
  codes.  It produces an honest [RawCodedPAProofOf] whose sole new context
  entry is certified by PA's represented induction-axiom recognizer.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedPAAxiomWitness
  RawCodedRestrictedPAProof RawCodedPAProvability
  RawCodedProofEndpoints RawCodedProofRuleCoverage
  RawCodedProofAssumptionLeaf RawCodedPAProofImpICertificates
  RawCodedPALocalProofExistential RawCodedPAAxiomWitnessContextCons.

Module PABoundedRawCodedPAInductionAxiomCertificate.

Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedProofAssumptionLeaf.
Import PABoundedRawCodedPAProofImpICertificates.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPAAxiomWitnessContextCons.

Definition rawPAAxiomInductionWitnessCode (M : RawPAModel)
    (source : M) : M :=
  rawCodeList2 M (rawNumeralValue M 6) source.

Definition rawPAInductionExtendedWitnessList (M : RawPAModel)
    (baseWitnessList source : M) : M :=
  rawListNode M (rawPAAxiomInductionWitnessCode M source)
    baseWitnessList.

Definition rawPAInductionExtendedContext (M : RawPAModel)
    (baseContext axiom : M) : M :=
  rawListNode M axiom baseContext.

Definition rawPAInductionAxiomProofRoot (M : RawPAModel)
    (baseContext axiom : M) : M :=
  rawProofAssumptionRoot M
    (rawPAInductionExtendedContext M baseContext axiom) axiom.

Definition rawPAInductionAxiomCertificate (M : RawPAModel)
    (baseWitnessList baseContext source axiom : M) : M :=
  rawCodeList3 M (rawNumeralValue M 0)
    (rawPAInductionExtendedWitnessList M baseWitnessList source)
    (rawPAInductionAxiomProofRoot M baseContext axiom).

Arguments rawPAAxiomInductionWitnessCode M source : clear implicits.
Arguments rawPAInductionExtendedWitnessList M baseWitnessList source
  : clear implicits.
Arguments rawPAInductionExtendedContext M baseContext axiom
  : clear implicits.
Arguments rawPAInductionAxiomProofRoot M baseContext axiom
  : clear implicits.
Arguments rawPAInductionAxiomCertificate
  M baseWitnessList baseContext source axiom : clear implicits.

(** Tag six is exactly the induction branch of the seven-way represented PA
    axiom recognizer. *)
Lemma raw_codedPAAxiomWitness_of_induction : forall
    (M : RawPAModel) source axiom,
  RawCodedPAAxiomInduction M source axiom ->
  RawCodedPAAxiomWitness M
    (rawPAAxiomInductionWitnessCode M source) axiom.
Proof.
  intros M source axiom hinduction.
  right. right. right. right. right. right.
  exists source. split; [reflexivity | exact hinduction].
Qed.

(** Extend an arbitrary already witnessed PA base by the generated induction
    axiom.  Both old lists may have nonstandard length. *)
Theorem raw_codedPAAxiomWitnessContext_add_induction : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseWitnessList baseContext source axiom,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPAAxiomInduction M source axiom ->
  RawCodedPAAxiomWitnessContext M
    (rawPAInductionExtendedWitnessList M baseWitnessList source)
    (rawPAInductionExtendedContext M baseContext axiom).
Proof.
  intros M hPA baseWitnessList baseContext source axiom
    hbase hinduction.
  exact (raw_codedPAAxiomWitnessContext_cons M hPA
    baseWitnessList baseContext
    (rawPAAxiomInductionWitnessCode M source) axiom hbase
    (raw_codedPAAxiomWitness_of_induction M source axiom hinduction)).
Qed.

(** The newly adjoined axiom is available as an honest local proof in the
    extended context. *)
Theorem raw_codedPALocalProofOf_induction_axiom : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseWitnessList baseContext source axiom,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPAAxiomInduction M source axiom ->
  RawCodedPALocalProofOf M
    (rawPAInductionExtendedContext M baseContext axiom) axiom
    (rawPAInductionAxiomProofRoot M baseContext axiom).
Proof.
  intros M hPA baseWitnessList baseContext source axiom hbase _.
  unfold rawPAInductionAxiomProofRoot,
    rawPAInductionExtendedContext.
  apply (raw_codedPALocalProofOf_assumption M hPA).
  exact (raw_codedPAAxiomWitnessContext_context_realizable M
    baseWitnessList baseContext hbase).
Qed.

(** Public certificate endpoint: an arbitrary model-coded induction-axiom
    graph produces an ordinary covered PA proof, while retaining the incoming
    witnessed base and adding only the new induction witness. *)
Theorem raw_codedPAProofOf_induction_axiom : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseWitnessList baseContext source axiom,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPAAxiomInduction M source axiom ->
  RawCodedPAProofOf M axiom
    (rawPAInductionAxiomCertificate M
      baseWitnessList baseContext source axiom).
Proof.
  intros M hPA baseWitnessList baseContext source axiom
    hbase hinduction.
  exists (rawPAInductionExtendedWitnessList M baseWitnessList source),
    (rawPAInductionAxiomProofRoot M baseContext axiom),
    (rawPAInductionExtendedContext M baseContext axiom).
  split.
  - unfold rawPAInductionAxiomCertificate. reflexivity.
  - split.
    + exact (raw_codedPAAxiomWitnessContext_add_induction M hPA
        baseWitnessList baseContext source axiom hbase hinduction).
    + exact (raw_codedPALocalProofOf_induction_axiom M hPA
        baseWitnessList baseContext source axiom hbase hinduction).
Qed.

End PABoundedRawCodedPAInductionAxiomCertificate.
