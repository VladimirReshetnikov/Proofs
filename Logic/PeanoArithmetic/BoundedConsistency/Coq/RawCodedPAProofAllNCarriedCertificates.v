(**
  Iterated universal closure over a retained witnessed PA-axiom context.

  The earlier close-N wrapper was specialized to the empty context.  That
  specialization cannot package a successor proof which reuses the hidden
  witness list and context of an incoming [RawCodedPAProofOf].  Here the
  base context is arbitrary but is required to be fixed by the pointwise
  de Bruijn shift relation.  This is exactly the side condition needed by
  every [RP_allI] node; the witnessed base and its certificate are otherwise
  carried unchanged.
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
  RawCodedPAOpenProofComposition.

Module PABoundedRawCodedPAProofAllNCarriedCertificates.

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
Import PABoundedRawCodedPAOpenProofComposition.

(** Replay [count] universal-introduction nodes while retaining [context].
    The same context may be used as both source and target precisely because
    callers supply a genuine [RawContextShift context context]. *)
Fixpoint rawProofCloseNCarriedRoot (M : RawPAModel) (context : M)
    (count : nat) (body child : M) : M :=
  match count with
  | 0 => child
  | S count' =>
      rawProofCloseNCarriedRoot M context count'
        (rawFormulaAllCode M body)
        (rawProofAllIRoot M context body child)
  end.

Arguments rawProofCloseNCarriedRoot
  M context count body child : clear implicits.

Theorem raw_proofCloseNCarriedRoot_ruleCoverage : forall
    (M : RawPAModel), RawPASatisfies M -> forall context,
  RawContextShift M context context ->
  forall count body child,
  RawProofRuleCoverage M child ->
  RawProofEndpoint M child context body ->
  RawProofRuleCoverage M
    (rawProofCloseNCarriedRoot M context count body child).
Proof.
  intros M hPA context hself count.
  induction count as [|count IH];
    intros body child hcoverage hendpoint.
  - exact hcoverage.
  - cbn [rawProofCloseNCarriedRoot].
    apply IH.
    + exact (raw_proofAllI_ruleCoverage M hPA
        context context body child hself hcoverage hendpoint).
    + exact (raw_proofAllI_endpoint M context body child).
Qed.

Theorem raw_proofCloseNCarriedRoot_endpoint : forall
    (M : RawPAModel), RawPASatisfies M -> forall context,
  RawContextShift M context context ->
  forall count body child,
  RawProofRuleCoverage M child ->
  RawProofEndpoint M child context body ->
  RawProofEndpoint M
    (rawProofCloseNCarriedRoot M context count body child)
    context (rawRestrictedTargetCloseNFormulaCode M count body).
Proof.
  intros M hPA context hself count.
  induction count as [|count IH];
    intros body child hcoverage hendpoint.
  - exact hendpoint.
  - cbn [rawProofCloseNCarriedRoot
      rawRestrictedTargetCloseNFormulaCode].
    apply IH.
    + exact (raw_proofAllI_ruleCoverage M hPA
        context context body child hself hcoverage hendpoint).
    + exact (raw_proofAllI_endpoint M context body child).
Qed.

Definition rawProofUniversalOpenNegationCarriedRoot
    (M : RawPAModel) (context assumption child : M) : M :=
  rawProofAllIRoot M context
    (rawFormulaImpCode M assumption (rawFormulaBotCode M))
    (rawProofImpIRoot M context
      assumption (rawFormulaBotCode M) child).

Arguments rawProofUniversalOpenNegationCarriedRoot
  M context assumption child : clear implicits.

Definition rawProofSealedUniversalOpenNegationCarriedCertificate
    (M : RawPAModel) (witnessList context : M)
    (sealCount : nat) (assumption child : M) : M :=
  rawCodeList3 M (rawNumeralValue M 0) witnessList
    (rawProofCloseNCarriedRoot M context sealCount
      (rawFormulaAllCode M
        (rawFormulaImpCode M assumption (rawFormulaBotCode M)))
      (rawProofUniversalOpenNegationCarriedRoot
        M context assumption child)).

Arguments rawProofSealedUniversalOpenNegationCarriedCertificate
  M witnessList context sealCount assumption child : clear implicits.

(** Close the temporary restricted-proof assumption, quantify its candidate
    certificate, and replay the outer seal, all over the same witnessed PA
    base.  No proof-tree weakening or context erasure occurs. *)
Theorem
    raw_codedPAProofOf_sealed_universal_negation_of_carried_open_bottom :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      witnessList context sealCount assumption child,
  RawContextShift M context context ->
  RawCodedPAOpenProofOf M witnessList context assumption
    (rawFormulaBotCode M) child ->
  RawCodedPAProofOf M
    (rawRestrictedTargetCloseNFormulaCode M sealCount
      (rawFormulaAllCode M
        (rawFormulaImpCode M assumption (rawFormulaBotCode M))))
    (rawProofSealedUniversalOpenNegationCarriedCertificate M
      witnessList context sealCount assumption child).
Proof.
  intros M hPA witnessList context sealCount assumption child
    hself [hwitness [hcoverage hendpoint]].
  exists witnessList,
    (rawProofCloseNCarriedRoot M context sealCount
      (rawFormulaAllCode M
        (rawFormulaImpCode M assumption (rawFormulaBotCode M)))
      (rawProofUniversalOpenNegationCarriedRoot
        M context assumption child)), context.
  split.
  - unfold rawProofSealedUniversalOpenNegationCarriedCertificate.
    reflexivity.
  - repeat split.
    + exact hwitness.
    + apply (raw_proofCloseNCarriedRoot_ruleCoverage M hPA
        context hself sealCount
        (rawFormulaAllCode M
          (rawFormulaImpCode M assumption (rawFormulaBotCode M)))
        (rawProofUniversalOpenNegationCarriedRoot
          M context assumption child)).
      * unfold rawProofUniversalOpenNegationCarriedRoot.
        apply (raw_proofAllI_ruleCoverage M hPA
          context context
          (rawFormulaImpCode M assumption (rawFormulaBotCode M))
          (rawProofImpIRoot M context
            assumption (rawFormulaBotCode M) child)).
        -- exact hself.
        -- exact (raw_proofImpI_ruleCoverage M hPA
             context assumption (rawFormulaBotCode M) child
             hcoverage hendpoint).
        -- exact (raw_proofImpI_endpoint M
             context assumption (rawFormulaBotCode M) child).
      * unfold rawProofUniversalOpenNegationCarriedRoot.
        exact (raw_proofAllI_endpoint M context
          (rawFormulaImpCode M assumption (rawFormulaBotCode M))
          (rawProofImpIRoot M context
            assumption (rawFormulaBotCode M) child)).
    + apply (raw_proofCloseNCarriedRoot_endpoint M hPA
        context hself sealCount
        (rawFormulaAllCode M
          (rawFormulaImpCode M assumption (rawFormulaBotCode M)))
        (rawProofUniversalOpenNegationCarriedRoot
          M context assumption child)).
      * unfold rawProofUniversalOpenNegationCarriedRoot.
        apply (raw_proofAllI_ruleCoverage M hPA
          context context
          (rawFormulaImpCode M assumption (rawFormulaBotCode M))
          (rawProofImpIRoot M context
            assumption (rawFormulaBotCode M) child)).
        -- exact hself.
        -- exact (raw_proofImpI_ruleCoverage M hPA
             context assumption (rawFormulaBotCode M) child
             hcoverage hendpoint).
        -- exact (raw_proofImpI_endpoint M
             context assumption (rawFormulaBotCode M) child).
      * unfold rawProofUniversalOpenNegationCarriedRoot.
        exact (raw_proofAllI_endpoint M context
          (rawFormulaImpCode M assumption (rawFormulaBotCode M))
          (rawProofImpIRoot M context
            assumption (rawFormulaBotCode M) child)).
Qed.

End PABoundedRawCodedPAProofAllNCarriedCertificates.
