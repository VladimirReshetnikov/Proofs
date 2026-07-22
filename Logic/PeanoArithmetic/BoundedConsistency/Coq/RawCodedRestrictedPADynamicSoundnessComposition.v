(**
  The exact propositional shell of dynamic restricted-proof soundness.

  Once the three certificate witnesses have been opened, six of the seven
  projected fields are precisely the hypotheses needed to refute the alleged
  proof of falsity.  The remaining certificate-tuple equality only connects
  those witnesses to the outer certificate; it plays no role in soundness of
  the exposed proof tree itself.

  This module therefore isolates the genuinely mathematical obligation as
  one curried implication.  A future represented partial-truth construction
  need only produce a local proof of that implication for the possibly
  nonstandard numeral code.  The theorem below performs all six subsequent
  modus-ponens steps and returns the exact local proof of falsity required by
  existential descent.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedProofBinaryConstructors
  RawCodedPALocalProofExistential RawCodedPALocalProofComposition
  RawCodedRestrictedPAConsistencyOpenDescent
  RawCodedRestrictedPAConsistencyTripleExDescent
  RawCodedRestrictedPAFieldProjections.

Module PABoundedRawCodedRestrictedPADynamicSoundnessComposition.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedRestrictedPAConsistencyOpenDescent.
Import PABoundedRawCodedRestrictedPAConsistencyTripleExDescent.
Import PABoundedRawCodedRestrictedPAFieldProjections.

(** Right-associated implication from the six semantic checker fields to
    falsity.  [numeralCode] remains a raw carrier element: no standardness or
    decoding hypothesis is hidden in this definition. *)
Definition rawRestrictedPADynamicSoundnessImplicationCode
    (M : RawPAModel) (numeralCode : M) : M :=
  rawFormulaImpCode M
    (rawRestrictedPAAxiomContextFieldCode M)
    (rawFormulaImpCode M
      (rawRestrictedPAOccurrenceBoundFieldCode M numeralCode)
      (rawFormulaImpCode M
        (rawRestrictedPAAtomicAdequacyFieldCode M)
        (rawFormulaImpCode M
          (rawRestrictedPAFormulaCoverageFieldCode M)
          (rawFormulaImpCode M
            (rawRestrictedPARuleCoverageFieldCode M)
            (rawFormulaImpCode M
              (rawRestrictedPABottomEndpointFieldCode M)
              (rawFormulaBotCode M)))))).

Arguments rawRestrictedPADynamicSoundnessImplicationCode M numeralCode
  : clear implicits.

(** The smallest proof-producing dynamic-soundness package left after all
    syntax decomposition.  Its context is stated explicitly so downstream
    code cannot silently weaken or replace the existential-descent context. *)
Definition RawRestrictedPADynamicSoundnessImplicationProof
    (M : RawPAModel) (numeralCode tailContext : M) : Prop :=
  exists child : M,
    RawCodedPALocalProofOf M
      (rawRestrictedPAFieldsContextCode M numeralCode tailContext)
      (rawRestrictedPADynamicSoundnessImplicationCode M numeralCode)
      child.

Arguments RawRestrictedPADynamicSoundnessImplicationProof
  M numeralCode tailContext : clear implicits.

(** Apply the dynamic implication to the honest conjunction projections.
    The output root is intentionally existential: it is the concrete nest of
    six [RP_impE] nodes built by [raw_codedPALocalProofOf_impE]. *)
Theorem raw_codedPALocalProofOf_bottom_of_dynamicSoundness : forall
    (M : RawPAModel), RawPASatisfies M -> forall numeralCode tailContext,
  RawRestrictedPADynamicSoundnessImplicationProof
    M numeralCode tailContext ->
  RawRestrictedPAFieldProjectionPackage M numeralCode tailContext ->
  exists child : M,
    RawCodedPALocalProofOf M
      (rawRestrictedPAFieldsContextCode M numeralCode tailContext)
      (rawFormulaBotCode M) child.
Proof.
  intros M hPA numeralCode tailContext
    [soundnessChild hsoundness] hprojections.
  destruct hprojections as
    [hcertificate haxiom hoccurrence hatomic hformula hrule hendpoint].
  set (context := rawRestrictedPAFieldsContextCode
    M numeralCode tailContext) in *.
  unfold rawRestrictedPADynamicSoundnessImplicationCode in hsoundness.
  pose proof (raw_codedPALocalProofOf_impE M hPA context
    (rawRestrictedPAAxiomContextFieldCode M)
    (rawFormulaImpCode M
      (rawRestrictedPAOccurrenceBoundFieldCode M numeralCode)
      (rawFormulaImpCode M
        (rawRestrictedPAAtomicAdequacyFieldCode M)
        (rawFormulaImpCode M
          (rawRestrictedPAFormulaCoverageFieldCode M)
          (rawFormulaImpCode M
            (rawRestrictedPARuleCoverageFieldCode M)
            (rawFormulaImpCode M
              (rawRestrictedPABottomEndpointFieldCode M)
              (rawFormulaBotCode M))))))
    soundnessChild
    (rawRestrictedPAAxiomContextProjectionRoot M numeralCode tailContext)
    hsoundness haxiom) as h1.
  pose proof (raw_codedPALocalProofOf_impE M hPA context
    (rawRestrictedPAOccurrenceBoundFieldCode M numeralCode)
    (rawFormulaImpCode M
      (rawRestrictedPAAtomicAdequacyFieldCode M)
      (rawFormulaImpCode M
        (rawRestrictedPAFormulaCoverageFieldCode M)
        (rawFormulaImpCode M
          (rawRestrictedPARuleCoverageFieldCode M)
          (rawFormulaImpCode M
            (rawRestrictedPABottomEndpointFieldCode M)
            (rawFormulaBotCode M)))))
    _ _ h1 hoccurrence) as h2.
  pose proof (raw_codedPALocalProofOf_impE M hPA context
    (rawRestrictedPAAtomicAdequacyFieldCode M)
    (rawFormulaImpCode M
      (rawRestrictedPAFormulaCoverageFieldCode M)
      (rawFormulaImpCode M
        (rawRestrictedPARuleCoverageFieldCode M)
        (rawFormulaImpCode M
          (rawRestrictedPABottomEndpointFieldCode M)
          (rawFormulaBotCode M))))
    _ _ h2 hatomic) as h3.
  pose proof (raw_codedPALocalProofOf_impE M hPA context
    (rawRestrictedPAFormulaCoverageFieldCode M)
    (rawFormulaImpCode M
      (rawRestrictedPARuleCoverageFieldCode M)
      (rawFormulaImpCode M
        (rawRestrictedPABottomEndpointFieldCode M)
        (rawFormulaBotCode M)))
    _ _ h3 hformula) as h4.
  pose proof (raw_codedPALocalProofOf_impE M hPA context
    (rawRestrictedPARuleCoverageFieldCode M)
    (rawFormulaImpCode M
      (rawRestrictedPABottomEndpointFieldCode M)
      (rawFormulaBotCode M))
    _ _ h4 hrule) as h5.
  pose proof (raw_codedPALocalProofOf_impE M hPA context
    (rawRestrictedPABottomEndpointFieldCode M)
    (rawFormulaBotCode M)
    _ _ h5 hendpoint) as h6.
  eexists. exact h6.
Qed.

End PABoundedRawCodedRestrictedPADynamicSoundnessComposition.
