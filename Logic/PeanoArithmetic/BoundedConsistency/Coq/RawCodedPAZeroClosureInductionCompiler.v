(**
  A genuine PA-proof compiler for zero-closure arbitrary-code induction.

  The induction predicate [source] and all intermediate formula codes may be
  nonstandard carrier elements.  The data below is exactly the transparent
  [RawCodedPAAxiomInduction] graph specialized to a body whose represented
  (coarse syntactic) free-variable bound is zero.  Its universal closure
  therefore returns the body itself.  This lets an honest PA induction-axiom
  leaf be combined with covered proofs of the zero and successor cases.

  This specialization is intentionally stronger than merely saying that the
  body is a sentence: [Formula.bound] is additive and does not decrease below
  binders.  General induction sources therefore still require the separate
  represented universal-closure elimination orbit documented by the
  single-step [RP_allE] constructor.

  No semantic induction principle and no opaque "the desired implication is
  provable" callback occurs in this interface: the operation graphs, the PA
  axiom witness, and every proof-tree constructor remain explicit.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax RawCodedSyntaxConstructors RawCodedFormulaOperations
  RawCodedPAAxiomWitness RawCodedRestrictedPAProof RawCodedPAProvability
  RawCodedPAInductionAxiomCertificate
  RawCodedProofAndIConstructor RawCodedProofBinaryConstructors
  RawCodedPALocalProofExistential
  RawCodedPALocalProofAndIntroduction RawCodedPALocalProofComposition.

Module PABoundedRawCodedPAZeroClosureInductionCompiler.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedPAInductionAxiomCertificate.
Import PABoundedRawCodedProofAndIConstructor.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofAndIntroduction.
Import PABoundedRawCodedPALocalProofComposition.

(** A field-by-field, zero-closure specialization of the represented
    induction-axiom recognizer.  Naming every intermediate code makes later
    proof certificates deterministic and inspectable. *)
Definition RawCodedPAZeroClosureInductionData (M : RawPAModel)
    (source axiom shifted successorInstance zeroInstance sourceAll
      stepImp stepAll premise body : M) : Prop :=
  RawCodedFormulaShift M
    (rawNumeralValue M 1) (rawNumeralValue M 1) source shifted /\
  RawCodedFormulaSingleSubstitution M
    (rawNumeralValue M (termCode (tSucc (tVar 0))))
    shifted successorInstance /\
  RawCodedFormulaSingleSubstitution M
    (rawNumeralValue M (termCode tZero)) source zeroInstance /\
  sourceAll = rawFormulaAllCode M source /\
  stepImp = rawFormulaImpCode M source successorInstance /\
  stepAll = rawFormulaAllCode M stepImp /\
  premise = rawFormulaAndCode M zeroInstance stepAll /\
  body = rawFormulaImpCode M premise sourceAll /\
  RawCodedFormulaBound M body (raw_zero M) /\
  RawCodedUniversalClosure M (raw_zero M) body axiom.

Arguments RawCodedPAZeroClosureInductionData
  M source axiom shifted successorInstance zeroInstance sourceAll
  stepImp stepAll premise body : clear implicits.

Lemma raw_codedPAZeroClosureInductionData_axiom : forall
    (M : RawPAModel) source axiom shifted successorInstance zeroInstance
      sourceAll stepImp stepAll premise body,
  RawCodedPAZeroClosureInductionData M
    source axiom shifted successorInstance zeroInstance sourceAll
    stepImp stepAll premise body ->
  RawCodedPAAxiomInduction M source axiom.
Proof.
  intros M source axiom shifted successorInstance zeroInstance sourceAll
    stepImp stepAll premise body hdata.
  exists shifted, successorInstance, zeroInstance, sourceAll,
    stepImp, stepAll, premise, body, (raw_zero M).
  exact hdata.
Qed.

(** Zero universal-closure steps are observationally the identity in every
    model of PA, including for a nonstandard body code. *)
Lemma raw_codedPAZeroClosureInductionData_axiom_is_body : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      source axiom shifted successorInstance zeroInstance sourceAll
      stepImp stepAll premise body,
  RawCodedPAZeroClosureInductionData M
    source axiom shifted successorInstance zeroInstance sourceAll
    stepImp stepAll premise body ->
  axiom = body.
Proof.
  intros M hPA source axiom shifted successorInstance zeroInstance
    sourceAll stepImp stepAll premise body hdata.
  unfold RawCodedPAZeroClosureInductionData in hdata.
  destruct hdata as
    [_ [_ [_ [_ [_ [_ [_ [_ [_ hclosure]]]]]]]]].
  exact (raw_codedUniversalClosure_zero M hPA body axiom hclosure).
Qed.

Definition rawPAZeroClosureInductionPremiseProofRoot (M : RawPAModel)
    (baseContext axiom zeroInstance stepAll zeroChild stepChild : M) : M :=
  rawProofAndIRoot M
    (rawPAInductionExtendedContext M baseContext axiom)
    zeroInstance stepAll zeroChild stepChild.

Definition rawPAZeroClosureInductionProofRoot (M : RawPAModel)
    (baseContext axiom premise sourceAll zeroInstance stepAll
      zeroChild stepChild : M) : M :=
  rawProofImpERoot M
    (rawPAInductionExtendedContext M baseContext axiom)
    premise sourceAll
    (rawPAInductionAxiomProofRoot M baseContext axiom)
    (rawPAZeroClosureInductionPremiseProofRoot M
      baseContext axiom zeroInstance stepAll zeroChild stepChild).

Definition rawPAZeroClosureInductionCertificate (M : RawPAModel)
    (baseWitnessList baseContext source axiom premise sourceAll
      zeroInstance stepAll zeroChild stepChild : M) : M :=
  rawCodeList3 M (rawNumeralValue M 0)
    (rawPAInductionExtendedWitnessList M baseWitnessList source)
    (rawPAZeroClosureInductionProofRoot M
      baseContext axiom premise sourceAll zeroInstance stepAll
      zeroChild stepChild).

Arguments rawPAZeroClosureInductionPremiseProofRoot
  M baseContext axiom zeroInstance stepAll zeroChild stepChild
  : clear implicits.
Arguments rawPAZeroClosureInductionProofRoot
  M baseContext axiom premise sourceAll zeroInstance stepAll
  zeroChild stepChild : clear implicits.
Arguments rawPAZeroClosureInductionCertificate
  M baseWitnessList baseContext source axiom premise sourceAll
  zeroInstance stepAll zeroChild stepChild : clear implicits.

(** Core local compiler.  The two inputs are concrete covered proof roots for
    the induction base and step formulas in the same extended context. *)
Theorem raw_codedPALocalProofOf_zeroClosure_induction : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseWitnessList baseContext source axiom shifted successorInstance
      zeroInstance sourceAll stepImp stepAll premise body
      zeroChild stepChild,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPAZeroClosureInductionData M
    source axiom shifted successorInstance zeroInstance sourceAll
    stepImp stepAll premise body ->
  RawCodedPALocalProofOf M
    (rawPAInductionExtendedContext M baseContext axiom)
    zeroInstance zeroChild ->
  RawCodedPALocalProofOf M
    (rawPAInductionExtendedContext M baseContext axiom)
    stepAll stepChild ->
  RawCodedPALocalProofOf M
    (rawPAInductionExtendedContext M baseContext axiom)
    sourceAll
    (rawPAZeroClosureInductionProofRoot M
      baseContext axiom premise sourceAll zeroInstance stepAll
      zeroChild stepChild).
Proof.
  intros M hPA baseWitnessList baseContext source axiom shifted
    successorInstance zeroInstance sourceAll stepImp stepAll premise body
    zeroChild stepChild hbase hdata hzero hstep.
  pose proof (raw_codedPAZeroClosureInductionData_axiom M
    source axiom shifted successorInstance zeroInstance sourceAll
    stepImp stepAll premise body hdata) as hinduction.
  pose proof (raw_codedPALocalProofOf_induction_axiom M hPA
    baseWitnessList baseContext source axiom hbase hinduction)
    as haxiomProof.
  pose proof (raw_codedPAZeroClosureInductionData_axiom_is_body M hPA
    source axiom shifted successorInstance zeroInstance sourceAll
    stepImp stepAll premise body hdata) as haxiomBody.
  unfold RawCodedPAZeroClosureInductionData in hdata.
  destruct hdata as
    [_ [_ [_ [_ [_ [_ [hpremise [hbody [_ _]]]]]]]]].
  assert (haxiomImp :
      axiom = rawFormulaImpCode M premise sourceAll).
  { now rewrite haxiomBody, hbody. }
  assert (haxiomImpProof : RawCodedPALocalProofOf M
      (rawPAInductionExtendedContext M baseContext axiom)
      (rawFormulaImpCode M premise sourceAll)
      (rawPAInductionAxiomProofRoot M baseContext axiom)).
  { rewrite <- haxiomImp. exact haxiomProof. }
  pose proof (raw_codedPALocalProofOf_andI M hPA
    (rawPAInductionExtendedContext M baseContext axiom)
    zeroInstance stepAll zeroChild stepChild hzero hstep)
    as hpremiseProof.
  rewrite <- hpremise in hpremiseProof.
  exact (raw_codedPALocalProofOf_impE M hPA
    (rawPAInductionExtendedContext M baseContext axiom)
    premise sourceAll
    (rawPAInductionAxiomProofRoot M baseContext axiom)
    (rawPAZeroClosureInductionPremiseProofRoot M
      baseContext axiom zeroInstance stepAll zeroChild stepChild)
    haxiomImpProof hpremiseProof).
Qed.

(** Package the local compiler as an ordinary represented PA proof. *)
Theorem raw_codedPAProofOf_zeroClosure_induction : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseWitnessList baseContext source axiom shifted successorInstance
      zeroInstance sourceAll stepImp stepAll premise body
      zeroChild stepChild,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPAZeroClosureInductionData M
    source axiom shifted successorInstance zeroInstance sourceAll
    stepImp stepAll premise body ->
  RawCodedPALocalProofOf M
    (rawPAInductionExtendedContext M baseContext axiom)
    zeroInstance zeroChild ->
  RawCodedPALocalProofOf M
    (rawPAInductionExtendedContext M baseContext axiom)
    stepAll stepChild ->
  RawCodedPAProofOf M sourceAll
    (rawPAZeroClosureInductionCertificate M
      baseWitnessList baseContext source axiom premise sourceAll
      zeroInstance stepAll zeroChild stepChild).
Proof.
  intros M hPA baseWitnessList baseContext source axiom shifted
    successorInstance zeroInstance sourceAll stepImp stepAll premise body
    zeroChild stepChild hbase hdata hzero hstep.
  pose proof (raw_codedPAZeroClosureInductionData_axiom M
    source axiom shifted successorInstance zeroInstance sourceAll
    stepImp stepAll premise body hdata) as hinduction.
  pose proof (raw_codedPALocalProofOf_zeroClosure_induction M hPA
    baseWitnessList baseContext source axiom shifted successorInstance
    zeroInstance sourceAll stepImp stepAll premise body
    zeroChild stepChild hbase hdata hzero hstep) as hlocal.
  exists (rawPAInductionExtendedWitnessList M baseWitnessList source),
    (rawPAZeroClosureInductionProofRoot M
      baseContext axiom premise sourceAll zeroInstance stepAll
      zeroChild stepChild),
    (rawPAInductionExtendedContext M baseContext axiom).
  split.
  - unfold rawPAZeroClosureInductionCertificate. reflexivity.
  - split.
    + exact (raw_codedPAAxiomWitnessContext_add_induction M hPA
        baseWitnessList baseContext source axiom hbase hinduction).
    + exact hlocal.
Qed.

End PABoundedRawCodedPAZeroClosureInductionCompiler.
