(**
  A PA-proof compiler for arbitrary model-coded induction closures.

  This is the positive-count counterpart of the zero-closure compiler.  The
  represented induction-axiom graph supplies a possibly nonstandard closure
  count.  [RawCodedUniversalClosureSelfInstantiationThrough] supplies only
  the syntax-operation certificates needed to open its strict prefixes, and
  [raw_codedPALocalProofOf_universalClosure_reduce] performs the entire
  model-internal proof reduction.

  Once the sealed axiom has been reduced to its implication body, the rest is
  ordinary natural deduction: introduce the conjunction of the supplied base
  and step proofs and apply implication elimination.  Every output remains an
  explicit covered PA proof tree.
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
  RawCodedPALocalProofAndIntroduction RawCodedPALocalProofComposition
  RawCodedPAUniversalClosureProofReduction.

Module PABoundedRawCodedPAClosureInductionCompiler.

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
Import PABoundedRawCodedPAUniversalClosureProofReduction.

(** Field-by-field induction data, now retaining the arbitrary represented
    closure count and its bounded self-instantiation graph. *)
Definition RawCodedPAClosureInductionData (M : RawPAModel)
    (replacement source axiom shifted successorInstance zeroInstance
      sourceAll stepImp stepAll premise body closureCount : M) : Prop :=
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
  RawCodedFormulaBound M body closureCount /\
  RawCodedUniversalClosure M closureCount body axiom /\
  RawCodedUniversalClosureSelfInstantiationThrough
    M replacement body closureCount.

Arguments RawCodedPAClosureInductionData
  M replacement source axiom shifted successorInstance zeroInstance
  sourceAll stepImp stepAll premise body closureCount : clear implicits.

Lemma raw_codedPAClosureInductionData_axiom : forall
    (M : RawPAModel) replacement source axiom shifted successorInstance
      zeroInstance sourceAll stepImp stepAll premise body closureCount,
  RawCodedPAClosureInductionData M replacement source axiom shifted
    successorInstance zeroInstance sourceAll stepImp stepAll premise body
    closureCount ->
  RawCodedPAAxiomInduction M source axiom.
Proof.
  intros M replacement source axiom shifted successorInstance zeroInstance
    sourceAll stepImp stepAll premise body closureCount hdata.
  exists shifted, successorInstance, zeroInstance, sourceAll,
    stepImp, stepAll, premise, body, closureCount.
  unfold RawCodedPAClosureInductionData in hdata.
  destruct hdata as
    [hshift [hsucc [hzero [hsourceAll [hstepImp [hstepAll
      [hpremise [hbody [hbound [hclosure _]]]]]]]]]].
  repeat split; assumption.
Qed.

Definition rawPAClosureInductionPremiseProofRoot (M : RawPAModel)
    (baseContext axiom zeroInstance stepAll zeroChild stepChild : M) : M :=
  rawProofAndIRoot M
    (rawPAInductionExtendedContext M baseContext axiom)
    zeroInstance stepAll zeroChild stepChild.

Definition rawPAClosureInductionProofRoot (M : RawPAModel)
    (baseContext axiom premise sourceAll zeroInstance stepAll
      bodyChild zeroChild stepChild : M) : M :=
  rawProofImpERoot M
    (rawPAInductionExtendedContext M baseContext axiom)
    premise sourceAll bodyChild
    (rawPAClosureInductionPremiseProofRoot M
      baseContext axiom zeroInstance stepAll zeroChild stepChild).

Definition rawPAClosureInductionCertificate (M : RawPAModel)
    (baseWitnessList baseContext source axiom premise sourceAll
      zeroInstance stepAll bodyChild zeroChild stepChild : M) : M :=
  rawCodeList3 M (rawNumeralValue M 0)
    (rawPAInductionExtendedWitnessList M baseWitnessList source)
    (rawPAClosureInductionProofRoot M
      baseContext axiom premise sourceAll zeroInstance stepAll
      bodyChild zeroChild stepChild).

Arguments rawPAClosureInductionPremiseProofRoot
  M baseContext axiom zeroInstance stepAll zeroChild stepChild
  : clear implicits.
Arguments rawPAClosureInductionProofRoot
  M baseContext axiom premise sourceAll zeroInstance stepAll
  bodyChild zeroChild stepChild : clear implicits.
Arguments rawPAClosureInductionCertificate
  M baseWitnessList baseContext source axiom premise sourceAll
  zeroInstance stepAll bodyChild zeroChild stepChild : clear implicits.

(** Core compiler in the extended induction-axiom context.  The existential
    [bodyChild] is the concrete root selected by represented unsealing; the
    final proof root is otherwise completely explicit. *)
Theorem raw_codedPALocalProofOf_closure_induction : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseWitnessList baseContext replacement source axiom shifted
      successorInstance zeroInstance sourceAll stepImp stepAll premise body
      closureCount zeroChild stepChild,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPAClosureInductionData M replacement source axiom shifted
    successorInstance zeroInstance sourceAll stepImp stepAll premise body
    closureCount ->
  RawCodedPALocalProofOf M
    (rawPAInductionExtendedContext M baseContext axiom)
    zeroInstance zeroChild ->
  RawCodedPALocalProofOf M
    (rawPAInductionExtendedContext M baseContext axiom)
    stepAll stepChild ->
  exists bodyChild : M,
    RawCodedPALocalProofOf M
      (rawPAInductionExtendedContext M baseContext axiom)
      sourceAll
      (rawPAClosureInductionProofRoot M
        baseContext axiom premise sourceAll zeroInstance stepAll
        bodyChild zeroChild stepChild).
Proof.
  intros M hPA baseWitnessList baseContext replacement source axiom shifted
    successorInstance zeroInstance sourceAll stepImp stepAll premise body
    closureCount zeroChild stepChild hbase hdata hzeroProof hstepProof.
  pose proof (raw_codedPAClosureInductionData_axiom M
    replacement source axiom shifted successorInstance zeroInstance
    sourceAll stepImp stepAll premise body closureCount hdata) as hinduction.
  pose proof (raw_codedPALocalProofOf_induction_axiom M hPA
    baseWitnessList baseContext source axiom hbase hinduction)
    as hsealedProof.
  unfold RawCodedPAClosureInductionData in hdata.
  destruct hdata as
    [_ [_ [_ [_ [_ [_ [hpremise [hbody [_ [hclosure hself]]]]]]]]]].
  destruct (raw_codedPALocalProofOf_universalClosure_reduce M hPA
    replacement body closureCount
    (rawPAInductionExtendedContext M baseContext axiom)
    axiom (rawPAInductionAxiomProofRoot M baseContext axiom)
    hself hclosure hsealedProof) as [bodyChild hbodyProof].
  assert (himpProof : RawCodedPALocalProofOf M
      (rawPAInductionExtendedContext M baseContext axiom)
      (rawFormulaImpCode M premise sourceAll) bodyChild).
  { rewrite <- hbody. exact hbodyProof. }
  pose proof (raw_codedPALocalProofOf_andI M hPA
    (rawPAInductionExtendedContext M baseContext axiom)
    zeroInstance stepAll zeroChild stepChild hzeroProof hstepProof)
    as hpremiseProof.
  rewrite <- hpremise in hpremiseProof.
  exists bodyChild.
  exact (raw_codedPALocalProofOf_impE M hPA
    (rawPAInductionExtendedContext M baseContext axiom)
    premise sourceAll bodyChild
    (rawPAClosureInductionPremiseProofRoot M
      baseContext axiom zeroInstance stepAll zeroChild stepChild)
    himpProof hpremiseProof).
Qed.

(** Ordinary PA-proof packaging. *)
Theorem raw_codedPAProofOf_closure_induction : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseWitnessList baseContext replacement source axiom shifted
      successorInstance zeroInstance sourceAll stepImp stepAll premise body
      closureCount zeroChild stepChild,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPAClosureInductionData M replacement source axiom shifted
    successorInstance zeroInstance sourceAll stepImp stepAll premise body
    closureCount ->
  RawCodedPALocalProofOf M
    (rawPAInductionExtendedContext M baseContext axiom)
    zeroInstance zeroChild ->
  RawCodedPALocalProofOf M
    (rawPAInductionExtendedContext M baseContext axiom)
    stepAll stepChild ->
  exists bodyChild : M,
    RawCodedPAProofOf M sourceAll
      (rawPAClosureInductionCertificate M
        baseWitnessList baseContext source axiom premise sourceAll
        zeroInstance stepAll bodyChild zeroChild stepChild).
Proof.
  intros M hPA baseWitnessList baseContext replacement source axiom shifted
    successorInstance zeroInstance sourceAll stepImp stepAll premise body
    closureCount zeroChild stepChild hbase hdata hzeroProof hstepProof.
  pose proof (raw_codedPAClosureInductionData_axiom M
    replacement source axiom shifted successorInstance zeroInstance
    sourceAll stepImp stepAll premise body closureCount hdata) as hinduction.
  destruct (raw_codedPALocalProofOf_closure_induction M hPA
    baseWitnessList baseContext replacement source axiom shifted
    successorInstance zeroInstance sourceAll stepImp stepAll premise body
    closureCount zeroChild stepChild hbase hdata hzeroProof hstepProof)
    as [bodyChild hlocal].
  exists bodyChild.
  exists (rawPAInductionExtendedWitnessList M baseWitnessList source),
    (rawPAClosureInductionProofRoot M
      baseContext axiom premise sourceAll zeroInstance stepAll
      bodyChild zeroChild stepChild),
    (rawPAInductionExtendedContext M baseContext axiom).
  split.
  - unfold rawPAClosureInductionCertificate. reflexivity.
  - split.
    + exact (raw_codedPAAxiomWitnessContext_add_induction M hPA
        baseWitnessList baseContext source axiom hbase hinduction).
    + exact hlocal.
Qed.

End PABoundedRawCodedPAClosureInductionCompiler.
