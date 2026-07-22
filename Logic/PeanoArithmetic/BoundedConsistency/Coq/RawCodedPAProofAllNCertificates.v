(**
  Iterated universal-introduction certificates over the empty context.

  [Formula.sealPA] closes a formula by a fixed metatheoretic number of outer
  universal quantifiers.  The restricted-consistency target graph mirrors
  that operation with [rawRestrictedTargetCloseNFormulaCode].  A single
  [RP_allI] constructor is therefore insufficient even after the candidate
  proof variable has been quantified: the enclosing seal must be replayed
  exactly as many times as its syntactic bound requests.

  This module performs that finite replay on raw proof codes.  The count is
  metatheoretic (the shape of the fixed target template), while every formula
  and proof node may still be nonstandard model data.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedContextShift
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedRestrictedPAProof RawCodedProofEndpoints
  RawCodedProofRuleCoverage RawCodedPAProvability
  RawCodedProofImpIConstructor RawCodedProofAllIConstructor
  RawCodedPAProofLeafCertificates RawCodedPAOpenProofComposition
  RawCodedPAProofAllICertificates.

Module PABoundedRawCodedPAProofAllNCertificates.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedProofImpIConstructor.
Import PABoundedRawCodedProofAllIConstructor.
Import PABoundedRawCodedPAProofLeafCertificates.
Import PABoundedRawCodedPAOpenProofComposition.
Import PABoundedRawCodedPAProofAllICertificates.

(** Replay [count] applications of [RP_allI].  The recursion follows the
    definition of [rawRestrictedTargetCloseNFormulaCode]: at a successor it
    first builds one universal-introduction node and then closes the result
    the remaining number of times. *)
Fixpoint rawProofCloseNRoot (M : RawPAModel) (count : nat)
    (body child : M) : M :=
  match count with
  | 0 => child
  | S count' =>
      rawProofCloseNRoot M count'
        (rawFormulaAllCode M body)
        (rawProofAllIRoot M (raw_zero M) body child)
  end.

Arguments rawProofCloseNRoot M count body child : clear implicits.

Theorem raw_proofCloseNRoot_ruleCoverage : forall
    (M : RawPAModel), RawPASatisfies M -> forall count body child,
  RawProofRuleCoverage M child ->
  RawProofEndpoint M child (raw_zero M) body ->
  RawProofRuleCoverage M (rawProofCloseNRoot M count body child).
Proof.
  intros M hPA count. induction count as [|count IH];
    intros body child hcoverage hendpoint.
  - exact hcoverage.
  - cbn [rawProofCloseNRoot].
    apply IH.
    + exact (raw_proofAllI_ruleCoverage M hPA
        (raw_zero M) (raw_zero M) body child
        (raw_contextShift_empty M hPA) hcoverage hendpoint).
    + exact (raw_proofAllI_endpoint M
        (raw_zero M) body child).
Qed.

Theorem raw_proofCloseNRoot_endpoint : forall
    (M : RawPAModel), RawPASatisfies M -> forall count body child,
  RawProofRuleCoverage M child ->
  RawProofEndpoint M child (raw_zero M) body ->
  RawProofEndpoint M
    (rawProofCloseNRoot M count body child)
    (raw_zero M)
    (rawRestrictedTargetCloseNFormulaCode M count body).
Proof.
  intros M hPA count. induction count as [|count IH];
    intros body child hcoverage hendpoint.
  - exact hendpoint.
  - cbn [rawProofCloseNRoot rawRestrictedTargetCloseNFormulaCode].
    apply IH.
    + exact (raw_proofAllI_ruleCoverage M hPA
        (raw_zero M) (raw_zero M) body child
        (raw_contextShift_empty M hPA) hcoverage hendpoint).
    + exact (raw_proofAllI_endpoint M
        (raw_zero M) body child).
Qed.

Definition rawProofCloseNCertificate (M : RawPAModel) (count : nat)
    (body child : M) : M :=
  rawCodeList3 M (rawNumeralValue M 0) (raw_zero M)
    (rawProofCloseNRoot M count body child).

Arguments rawProofCloseNCertificate M count body child : clear implicits.

Theorem raw_codedPAProofOf_closeN_empty_from_fields : forall
    (M : RawPAModel), RawPASatisfies M -> forall count body child,
  RawProofRuleCoverage M child ->
  RawProofEndpoint M child (raw_zero M) body ->
  RawCodedPAProofOf M
    (rawRestrictedTargetCloseNFormulaCode M count body)
    (rawProofCloseNCertificate M count body child).
Proof.
  intros M hPA count body child hcoverage hendpoint.
  exists (raw_zero M),
    (rawProofCloseNRoot M count body child), (raw_zero M).
  split.
  - unfold rawProofCloseNCertificate. reflexivity.
  - repeat split.
    + exact (raw_codedPAAxiomWitnessContext_empty M hPA).
    + exact (raw_proofCloseNRoot_ruleCoverage M hPA
        count body child hcoverage hendpoint).
    + exact (raw_proofCloseNRoot_endpoint M hPA
        count body child hcoverage hendpoint).
Qed.

(** Exact proof certificate for the sealed restricted-consistency shape.
    The first [RP_allI] binds the candidate certificate variable.  The
    iterated wrapper then reproduces the outer [sealPA] quantifiers of the
    fixed target template. *)
Definition rawProofSealedUniversalOpenNegationCertificate
    (M : RawPAModel) (sealCount : nat) (assumption child : M) : M :=
  rawProofCloseNCertificate M sealCount
    (rawFormulaAllCode M
      (rawFormulaImpCode M assumption (rawFormulaBotCode M)))
    (rawProofUniversalOpenNegationRoot M assumption child).

Arguments rawProofSealedUniversalOpenNegationCertificate
  M sealCount assumption child : clear implicits.

Theorem raw_codedPAProofOf_sealed_universal_negation_of_open_bottom : forall
    (M : RawPAModel), RawPASatisfies M -> forall sealCount assumption child,
  RawCodedPAOpenProofOf M
    (raw_zero M) (raw_zero M) assumption (rawFormulaBotCode M) child ->
  RawCodedPAProofOf M
    (rawRestrictedTargetCloseNFormulaCode M sealCount
      (rawFormulaAllCode M
        (rawFormulaImpCode M assumption (rawFormulaBotCode M))))
    (rawProofSealedUniversalOpenNegationCertificate
      M sealCount assumption child).
Proof.
  intros M hPA sealCount assumption child
    [_ [hcoverage hendpoint]].
  unfold rawProofSealedUniversalOpenNegationCertificate.
  apply (raw_codedPAProofOf_closeN_empty_from_fields M hPA sealCount
    (rawFormulaAllCode M
      (rawFormulaImpCode M assumption (rawFormulaBotCode M)))
    (rawProofUniversalOpenNegationRoot M assumption child)).
  - unfold rawProofUniversalOpenNegationRoot.
    apply (raw_proofAllI_ruleCoverage M hPA
      (raw_zero M) (raw_zero M)
      (rawFormulaImpCode M assumption (rawFormulaBotCode M))
      (rawProofImpIRoot M (raw_zero M)
        assumption (rawFormulaBotCode M) child)).
    + exact (raw_contextShift_empty M hPA).
    + exact (raw_proofImpI_ruleCoverage M hPA
        (raw_zero M) assumption (rawFormulaBotCode M) child
        hcoverage hendpoint).
    + exact (raw_proofImpI_endpoint M
        (raw_zero M) assumption (rawFormulaBotCode M) child).
  - unfold rawProofUniversalOpenNegationRoot.
    exact (raw_proofAllI_endpoint M (raw_zero M)
      (rawFormulaImpCode M assumption (rawFormulaBotCode M))
      (rawProofImpIRoot M (raw_zero M)
        assumption (rawFormulaBotCode M) child)).
Qed.

End PABoundedRawCodedPAProofAllNCertificates.
