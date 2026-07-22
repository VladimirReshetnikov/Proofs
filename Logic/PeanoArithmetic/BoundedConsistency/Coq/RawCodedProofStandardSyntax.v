(**
  Standard quotations realize the honest raw proof-syntax domain.

  [RawCodedProofStandardSupport] builds a beta table which marks every
  canonical proof code below a fixed standard bound.  This file supplies the
  complementary local argument: a marked quotation has a constructor row,
  and every alternative constructor payload for the same carrier code closes
  over the very same table.

  The non-obvious point is the universal quantifier in [RawProofSyntaxStep].
  Its fields range over an arbitrary (and possibly nonstandard) PA model, so
  they must not be decoded in Rocq.  Instead, injectivity of the complete raw
  list code compares an alternative payload directly with the finite standard
  payload.  Distinct tags are separated by numeral injectivity; the matching
  tag identifies each recursive field with a genuine quoted child.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  BoundedConsistency CodedProof RawCodedAssignment
  RawCodedSyntaxConstructors RawCodedProofConstructors
  RawCodedProofDescent RawCodedProofTraversal
  RawCodedSyntaxConstructorSeparation
  RawCodedListInjectivity RawCodedProofStandardSupport.

Import ListNotations.

Module PABoundedRawCodedProofStandardSyntax.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedConsistency.
Import PABoundedCodedProof.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedSyntaxConstructorSeparation.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedProofTraversal.
Import PABoundedRawCodedListInjectivity.
Import PABoundedRawCodedProofStandardSupport.

(** The canonical quotation visibly has one of the seventeen arithmetic
    constructor occurrences.  Unused coordinates are filled with zero. *)
Lemma raw_quotedProof_constructor_occurs : forall (M : RawPAModel)
    (derivation : RawProof),
  exists context a b c t child1 child2 child3 : M,
    RawProofConstructorCode M
      (rawQuotedProofCode M derivation)
      context a b c t child1 child2 child3.
Proof.
  intros M derivation.
  destruct derivation as
    [G a | G a b h | G a b hImp hA | G a h | G a
    | G a b hA hB | G a b h | G a b h
    | G a b h | G a b h | G a b c hOr hA hB
    | G a h | G a witness h | G a witness h
    | G a c hEx hBody | G witness
    | G source target a hEq hA];
    cbn [rawQuotedProofCode].
  - exists (rawNumeralValue M (contextCode G)),
      (rawQuotedFormulaCode M a),
      (raw_zero M), (raw_zero M), (raw_zero M),
      (raw_zero M), (raw_zero M), (raw_zero M);
      unfold RawProofConstructorCode; eauto 20.
  - exists (rawNumeralValue M (contextCode G)),
      (rawQuotedFormulaCode M a), (rawQuotedFormulaCode M b),
      (raw_zero M), (raw_zero M),
      (rawQuotedProofCode M h), (raw_zero M), (raw_zero M);
      unfold RawProofConstructorCode; eauto 20.
  - exists (rawNumeralValue M (contextCode G)),
      (rawQuotedFormulaCode M a), (rawQuotedFormulaCode M b),
      (raw_zero M), (raw_zero M),
      (rawQuotedProofCode M hImp), (rawQuotedProofCode M hA),
      (raw_zero M);
      unfold RawProofConstructorCode; eauto 20.
  - exists (rawNumeralValue M (contextCode G)),
      (rawQuotedFormulaCode M a),
      (raw_zero M), (raw_zero M), (raw_zero M),
      (rawQuotedProofCode M h), (raw_zero M), (raw_zero M);
      unfold RawProofConstructorCode; eauto 20.
  - exists (rawNumeralValue M (contextCode G)),
      (rawQuotedFormulaCode M a),
      (raw_zero M), (raw_zero M), (raw_zero M),
      (raw_zero M), (raw_zero M), (raw_zero M);
      unfold RawProofConstructorCode; eauto 20.
  - exists (rawNumeralValue M (contextCode G)),
      (rawQuotedFormulaCode M a), (rawQuotedFormulaCode M b),
      (raw_zero M), (raw_zero M),
      (rawQuotedProofCode M hA), (rawQuotedProofCode M hB),
      (raw_zero M);
      unfold RawProofConstructorCode; eauto 20.
  - exists (rawNumeralValue M (contextCode G)),
      (rawQuotedFormulaCode M a), (rawQuotedFormulaCode M b),
      (raw_zero M), (raw_zero M),
      (rawQuotedProofCode M h), (raw_zero M), (raw_zero M);
      unfold RawProofConstructorCode; eauto 20.
  - exists (rawNumeralValue M (contextCode G)),
      (rawQuotedFormulaCode M a), (rawQuotedFormulaCode M b),
      (raw_zero M), (raw_zero M),
      (rawQuotedProofCode M h), (raw_zero M), (raw_zero M);
      unfold RawProofConstructorCode; eauto 20.
  - exists (rawNumeralValue M (contextCode G)),
      (rawQuotedFormulaCode M a), (rawQuotedFormulaCode M b),
      (raw_zero M), (raw_zero M),
      (rawQuotedProofCode M h), (raw_zero M), (raw_zero M);
      unfold RawProofConstructorCode; eauto 20.
  - exists (rawNumeralValue M (contextCode G)),
      (rawQuotedFormulaCode M a), (rawQuotedFormulaCode M b),
      (raw_zero M), (raw_zero M),
      (rawQuotedProofCode M h), (raw_zero M), (raw_zero M);
      unfold RawProofConstructorCode; eauto 20.
  - exists (rawNumeralValue M (contextCode G)),
      (rawQuotedFormulaCode M a), (rawQuotedFormulaCode M b),
      (rawQuotedFormulaCode M c), (raw_zero M),
      (rawQuotedProofCode M hOr), (rawQuotedProofCode M hA),
      (rawQuotedProofCode M hB);
      unfold RawProofConstructorCode; eauto 20.
  - exists (rawNumeralValue M (contextCode G)),
      (rawQuotedFormulaCode M a),
      (raw_zero M), (raw_zero M), (raw_zero M),
      (rawQuotedProofCode M h), (raw_zero M), (raw_zero M);
      unfold RawProofConstructorCode; eauto 20.
  - exists (rawNumeralValue M (contextCode G)),
      (rawQuotedFormulaCode M a),
      (raw_zero M), (raw_zero M), (rawQuotedTermCode M witness),
      (rawQuotedProofCode M h), (raw_zero M), (raw_zero M);
      unfold RawProofConstructorCode; eauto 20.
  - exists (rawNumeralValue M (contextCode G)),
      (rawQuotedFormulaCode M a),
      (raw_zero M), (raw_zero M), (rawQuotedTermCode M witness),
      (rawQuotedProofCode M h), (raw_zero M), (raw_zero M);
      unfold RawProofConstructorCode; eauto 20.
  - exists (rawNumeralValue M (contextCode G)),
      (rawQuotedFormulaCode M a), (rawQuotedFormulaCode M c),
      (raw_zero M), (raw_zero M),
      (rawQuotedProofCode M hEx), (rawQuotedProofCode M hBody),
      (raw_zero M);
      unfold RawProofConstructorCode; eauto 20.
  - exists (rawNumeralValue M (contextCode G)),
      (raw_zero M), (raw_zero M), (raw_zero M),
      (rawQuotedTermCode M witness),
      (raw_zero M), (raw_zero M), (raw_zero M);
      unfold RawProofConstructorCode; eauto 20.
  - exists (rawNumeralValue M (contextCode G)),
      (rawQuotedTermCode M source), (rawQuotedTermCode M target),
      (rawQuotedFormulaCode M a), (raw_zero M),
      (rawQuotedProofCode M hEq), (rawQuotedProofCode M hA),
      (raw_zero M);
      unfold RawProofConstructorCode; eauto 20.
Qed.

(** If one of the fourteen recursive payload patterns codes a standard
    quotation, each advertised recursive field is the quotation of a genuine
    meta-level child.  This lemma is deliberately independent of a support
    table.  It is the exact boundary at which arbitrary carrier payloads are
    compared with standard syntax, using injectivity rather than decoding. *)
Lemma raw_quotedProof_recursive_payload_child : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (derivation : RawProof) context a b c t child1 child2 child3
    fields children,
  In (fields, children)
    (rawProofRecursiveCases M
      context a b c t child1 child2 child3) ->
  rawQuotedProofCode M derivation = rawListCode M fields ->
  forall childCode, In childCode children ->
  exists child,
    In child (rawChildren derivation) /\
    childCode = rawQuotedProofCode M child.
Proof.
  intros M hPA derivation context a b c t child1 child2 child3
    fields children hentry hcode childCode hchild.
  unfold rawProofRecursiveCases in hentry. cbn in hentry.
  repeat match type of hentry with
  | _ \/ _ => destruct hentry as [hentry | hentry]
  end; try contradiction.
  all: inversion hentry; subst fields children; clear hentry.
  all: destruct derivation;
    cbn [rawQuotedProofCode rawChildren] in hcode, hchild |- *.
  all: pose proof (rawListCode_injective M hPA _ _ hcode) as hpayload.
  all: inversion hpayload; subst; clear hpayload hcode.
  (** [cbn] exposes standard tags as finite successor chains.  Cancel equal
      successors and reject the first zero/successor mismatch. *)
  all: repeat match goal with
  | hmodel : RawPASatisfies ?model,
    htag : raw_succ ?model ?left = raw_succ ?model ?right |- _ =>
      apply (raw_succ_injective_syntax model hmodel) in htag
  end.
  all: try match goal with
  | hmodel : RawPASatisfies ?model,
    htag : raw_zero ?model = raw_succ ?model ?value |- _ =>
      exfalso; exact (raw_zero_not_succ_syntax model hmodel value htag)
  | hmodel : RawPASatisfies ?model,
    htag : raw_succ ?model ?value = raw_zero ?model |- _ =>
      exfalso; apply (raw_zero_not_succ_syntax model hmodel value);
      symmetry; exact htag
  end.
  all: cbn [In] in hchild.
  all: repeat match type of hchild with
  | _ \/ _ => destruct hchild as [hchild | hchild]
  end; try contradiction; subst childCode.
  all: eexists; split; [| reflexivity]; cbn; tauto.
Qed.

(** A standard quoted row closes every alternative occurrence.  Arithmetic
    descent is constructor-generic; only support uses the payload lemma above. *)
Lemma raw_quotedProof_syntax_step : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    bound supportCode supportStep,
  RawStandardProofSupportTable M bound supportCode supportStep ->
  forall derivation,
  rawProofCode derivation < bound ->
  RawProofSyntaxStep M
    (rawQuotedProofCode M derivation) supportCode supportStep.
Proof.
  intros M hPA bound supportCode supportStep htable derivation hbound.
  split.
  - exact (raw_quotedProof_constructor_occurs M derivation).
  - intros context a b c t child1 child2 child3 hconstructor.
    split.
    + exact (raw_proofConstructorCode_descent M hPA
        (rawQuotedProofCode M derivation)
        context a b c t child1 child2 child3 hconstructor).
    + apply Forall_forall. intros [fields children] hentry.
      unfold RawProofChildrenClosedCase. intro hfields.
      pose proof (raw_proofConstructorCode_descent M hPA
        (rawQuotedProofCode M derivation)
        context a b c t child1 child2 child3 hconstructor) as hdescent.
      destruct hdescent as [_ hbelow].
      pose proof (proj1 (@Forall_forall (list M * list M)
        (fun entry => RawProofChildrenBelowCase M
          (rawQuotedProofCode M derivation) (fst entry) (snd entry))
        (rawProofRecursiveCases M
          context a b c t child1 child2 child3))
        hbelow (fields, children) hentry) as hcaseBelow.
      cbn in hcaseBelow. specialize (hcaseBelow hfields).
      apply Forall_forall. intros advertisedChild hadvertised.
      split.
      * destruct (raw_quotedProof_recursive_payload_child M hPA
          derivation context a b c t child1 child2 child3
          fields children hentry hfields advertisedChild hadvertised)
          as [child [hchild ->]].
        exact (raw_standardProofSupportTable_child M hPA
          bound supportCode supportStep htable
          derivation child hbound hchild).
      * exact (proj1 (@Forall_forall M
          (fun child => rawLt M child (rawQuotedProofCode M derivation))
          children) hcaseBelow advertisedChild hadvertised).
Qed.

(** The exact standard support table turns every marked row below the common
    bound into the local theorem above. *)
Theorem raw_quotedProof_syntax_certificate : forall
    (M : RawPAModel), RawPASatisfies M -> forall derivation,
  exists supportCode supportStep,
    RawProofSyntaxCertificateWithSupport M
      (rawQuotedProofCode M derivation) supportCode supportStep.
Proof.
  intros M hPA derivation.
  destruct (raw_standardProofSupportTable_for_quotation M hPA derivation)
    as (supportCode & supportStep & htable & hroot).
  exists supportCode, supportStep. split; [| exact hroot].
  destruct htable as [hdefined hexact]. split.
  - rewrite rawQuotedProofCode_standard by exact hPA.
    change (RawCodedAssignmentDefinedThrough M supportCode supportStep
      (rawNumeralValue M (S (rawProofCode derivation)))).
    exact hdefined.
  - intros code hcode hsupported.
    assert (hcodeBound : rawLt M code
        (rawNumeralValue M (S (rawProofCode derivation)))).
    {
      rewrite rawQuotedProofCode_standard in hcode by exact hPA.
      change (rawLt M code
        (rawNumeralValue M (S (rawProofCode derivation)))) in hcode.
      exact hcode.
    }
    destruct (proj1 (hexact code hcodeBound) hsupported)
      as [row [hrow hrowBound]].
    subst code.
    apply (raw_quotedProof_syntax_step M hPA
      (S (rawProofCode derivation)) supportCode supportStep).
    + split; assumption.
    + exact hrowBound.
Qed.

Corollary raw_quotedProof_syntax_realizable : forall
    (M : RawPAModel), RawPASatisfies M -> forall derivation,
  RawProofSyntaxRealizable M (rawQuotedProofCode M derivation).
Proof.
  intros M hPA derivation.
  exact (raw_quotedProof_syntax_certificate M hPA derivation).
Qed.

End PABoundedRawCodedProofStandardSyntax.
