(**
  Standard quotation adequacy for the globally restricted proof predicate.

  A restricted traversal cannot reuse the deliberately generous syntax-only
  support table: that table marks every canonical proof code below its bound,
  including invalid raw derivations.  We therefore build a second finite
  table whose live rows are exactly the canonical, valid, externally bounded
  proof codes.  Genuine premises remain live because validity and occurrence
  boundedness are inherited by every recursive child.

  All comparisons with arbitrary model elements use polynomial list-code
  injectivity.  In particular, no carrier value is ever decoded.  Two
  formula-level properties are named below and then proved:

  - a rank certificate for each standard quoted formula; and
  - boundedness preservation for an arbitrary trace claiming to be standard
    single substitution.

  The second property matters because [RawProofEndpoint] universally admits
  every substitution trace for all-elimination and equality elimination.
  [RawCodedFormulaOperationQuotedRankSound] proves it for arbitrary traces by
  showing that formula-operation rows preserve the constructor skeleton.
*)

From Stdlib Require Import List Arith Bool Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import ListCode.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  BoundedConsistency CodedSyntax CodedProof PolynomialPairInjectivity
  RawCodedAssignment RawCodedSyntaxConstructors
  RawCodedSyntaxConstructorSeparation RawCodedListInjectivity
  RawCodedFormulaRankStep RawCodedFormulaRankTraversal
  RawCodedFormulaRankTotality
  RawCodedFormulaOperations RawCodedFormulaOperationsStandardRealization
  RawCodedFormulaOperationQuotedRankSound
  RawCodedContextLists RawCodedContextBounds RawCodedContextStructure
  RawCodedContextFunctionality
  RawCodedContextShift RawCodedProofConstructors RawCodedProofDescent
  RawCodedProofTraversal RawCodedProofEndpoints RawCodedProofRules
  RawCodedProofStandardSyntax RawCodedRestrictedProofTraversal.

Import ListNotations.

Module PABoundedRawCodedRestrictedProofStandardAdequacy.

Import PA.
Import PAListCode.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedConsistency.
Import PABoundedCodedSyntax.
Import PABoundedCodedProof.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedSyntaxConstructorSeparation.
Import PABoundedRawCodedListInjectivity.
Import PABoundedRawCodedFormulaRankStep.
Import PABoundedRawCodedFormulaRankTraversal.
Import PABoundedRawCodedFormulaRankTotality.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaOperationsStandardRealization.
Import PABoundedRawCodedFormulaOperationQuotedRankSound.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextBounds.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedContextFunctionality.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedProofTraversal.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedProofStandardSyntax.
Import PABoundedRawCodedRestrictedProofTraversal.

(** A context quotation is written structurally, rather than as a numeral,
    so the context constructors can be applied by ordinary list induction. *)
Fixpoint rawQuotedContextCode (M : RawPAModel) (context : list formula) : M :=
  match context with
  | [] => raw_zero M
  | head :: tail =>
      rawListNode M (rawQuotedFormulaCode M head)
        (rawQuotedContextCode M tail)
  end.

Arguments rawQuotedContextCode M context : clear implicits.

Lemma rawQuotedContextCode_as_list : forall M context,
  rawQuotedContextCode M context =
  rawListCode M (map (rawQuotedFormulaCode M) context).
Proof. intros M context. induction context; cbn; congruence. Qed.

Lemma rawQuotedContextCode_standard : forall (M : RawPAModel),
  RawPASatisfies M -> forall context,
  rawQuotedContextCode M context =
  rawNumeralValue M (contextCode context).
Proof.
  intros M hPA context.
  rewrite rawQuotedContextCode_as_list.
  assert (hmap : map (rawQuotedFormulaCode M) context =
      map (rawNumeralValue M) (map formulaCode context)).
  {
    induction context as [|head tail IH]; cbn; [reflexivity |].
    rewrite rawQuotedFormulaCode_standard by exact hPA.
    now rewrite IH.
  }
  rewrite hmap. unfold contextCode.
  apply rawListCode_standard. exact hPA.
Qed.

(** Early structural context helpers are used by the local rule quotation
    theorem below. *)
Lemma raw_quotedContext_realizable_for_rules : forall (M : RawPAModel),
  RawPASatisfies M -> forall context,
  RawContextListRealizable M (rawQuotedContextCode M context).
Proof.
  intros M hPA context. induction context as [|head tail IH].
  - apply raw_contextList_empty_realizable. exact hPA.
  - cbn. apply raw_contextList_cons_realizable; assumption.
Qed.

Corollary raw_quotedContext_realizable : forall (M : RawPAModel),
  RawPASatisfies M -> forall context,
  RawContextListRealizable M (rawQuotedContextCode M context).
Proof. exact raw_quotedContext_realizable_for_rules. Qed.

Lemma raw_quotedContext_member_for_rules : forall (M : RawPAModel),
  RawPASatisfies M -> forall context phi,
  In phi context ->
  RawContextListMember M
    (rawQuotedContextCode M context) (rawQuotedFormulaCode M phi).
Proof.
  intros M hPA context. induction context as [|head tail IH];
    intros phi hin; cbn in hin |- *.
  - contradiction.
  - destruct hin as [-> | hin].
    + apply raw_contextList_cons_head_member; [exact hPA |].
      apply raw_quotedContext_realizable_for_rules. exact hPA.
    + apply raw_contextList_cons_tail_member; [exact hPA |].
      exact (IH phi hin).
Qed.

Corollary raw_quotedContext_member : forall (M : RawPAModel),
  RawPASatisfies M -> forall context phi,
  In phi context ->
  RawContextListMember M
    (rawQuotedContextCode M context) (rawQuotedFormulaCode M phi).
Proof. exact raw_quotedContext_member_for_rules. Qed.

Lemma raw_quotedContext_shift_for_rules : forall (M : RawPAModel),
  RawPASatisfies M -> forall context,
  RawContextShift M
    (rawQuotedContextCode M context)
    (rawQuotedContextCode M (map (Formula.rename S) context)).
Proof.
  intros M hPA context. induction context as [|head tail IH].
  - cbn. apply raw_contextShift_empty. exact hPA.
  - cbn [rawQuotedContextCode map].
    apply raw_contextShift_cons; [exact hPA | exact IH |].
    apply raw_codedFormulaShift_standard_zero_one. exact hPA.
Qed.

Corollary raw_quotedContext_shift : forall (M : RawPAModel),
  RawPASatisfies M -> forall context,
  RawContextShift M
    (rawQuotedContextCode M context)
    (rawQuotedContextCode M (map (Formula.rename S) context)).
Proof. exact raw_quotedContext_shift_for_rules. Qed.

(** Internal endpoint quotation helper.  It appears before the rule theorem
    because rule rows cite the canonical endpoints of their premises. *)
Lemma raw_quotedProof_endpoint_for_rules : forall (M : RawPAModel),
  RawPASatisfies M -> forall derivation,
  RawProofEndpoint M (rawQuotedProofCode M derivation)
    (rawQuotedContextCode M (rawContext derivation))
    (rawQuotedFormulaCode M (rawConclusion derivation)).
Proof.
  intros M hPA derivation.
  destruct derivation as
    [G a | G a b h | G a b hImp hA | G a h | G a
    | G a b hA hB | G a b h | G a b h
    | G a b h | G a b h | G a b c hOr hA hB
    | G a h | G a witness h | G a witness h
    | G a c hEx hBody | G witness
    | G source target a hEq hA];
    cbn [rawContext rawConclusion rawQuotedProofCode rawQuotedFormulaCode];
    rewrite rawQuotedContextCode_standard by exact hPA.
  - exists (rawNumeralValue M (contextCode G)),
      (rawQuotedFormulaCode M a),
      (raw_zero M), (raw_zero M), (raw_zero M),
      (raw_zero M), (raw_zero M), (raw_zero M).
    split; [reflexivity |]. unfold RawProofEndpointCases. eauto 20.
  - exists (rawNumeralValue M (contextCode G)),
      (rawQuotedFormulaCode M a), (rawQuotedFormulaCode M b),
      (raw_zero M), (raw_zero M),
      (rawQuotedProofCode M h), (raw_zero M), (raw_zero M).
    split; [reflexivity |]. unfold RawProofEndpointCases. eauto 20.
  - exists (rawNumeralValue M (contextCode G)),
      (rawQuotedFormulaCode M a), (rawQuotedFormulaCode M b),
      (raw_zero M), (raw_zero M),
      (rawQuotedProofCode M hImp), (rawQuotedProofCode M hA),
      (raw_zero M).
    split; [reflexivity |]. unfold RawProofEndpointCases. eauto 20.
  - exists (rawNumeralValue M (contextCode G)),
      (rawQuotedFormulaCode M a),
      (raw_zero M), (raw_zero M), (raw_zero M),
      (rawQuotedProofCode M h), (raw_zero M), (raw_zero M).
    split; [reflexivity |]. unfold RawProofEndpointCases. eauto 20.
  - exists (rawNumeralValue M (contextCode G)),
      (rawQuotedFormulaCode M a),
      (rawFormulaImpCode M (rawQuotedFormulaCode M a)
        (rawFormulaBotCode M)),
      (rawFormulaBotCode M), (raw_zero M),
      (raw_zero M), (raw_zero M), (raw_zero M).
    split; [reflexivity |]. unfold RawProofEndpointCases. eauto 20.
  - exists (rawNumeralValue M (contextCode G)),
      (rawQuotedFormulaCode M a), (rawQuotedFormulaCode M b),
      (raw_zero M), (raw_zero M),
      (rawQuotedProofCode M hA), (rawQuotedProofCode M hB),
      (raw_zero M).
    split; [reflexivity |]. unfold RawProofEndpointCases. eauto 20.
  - exists (rawNumeralValue M (contextCode G)),
      (rawQuotedFormulaCode M a), (rawQuotedFormulaCode M b),
      (raw_zero M), (raw_zero M),
      (rawQuotedProofCode M h), (raw_zero M), (raw_zero M).
    split; [reflexivity |]. unfold RawProofEndpointCases. eauto 20.
  - exists (rawNumeralValue M (contextCode G)),
      (rawQuotedFormulaCode M a), (rawQuotedFormulaCode M b),
      (raw_zero M), (raw_zero M),
      (rawQuotedProofCode M h), (raw_zero M), (raw_zero M).
    split; [reflexivity |]. unfold RawProofEndpointCases. eauto 20.
  - exists (rawNumeralValue M (contextCode G)),
      (rawQuotedFormulaCode M a), (rawQuotedFormulaCode M b),
      (raw_zero M), (raw_zero M),
      (rawQuotedProofCode M h), (raw_zero M), (raw_zero M).
    split; [reflexivity |]. unfold RawProofEndpointCases. eauto 20.
  - exists (rawNumeralValue M (contextCode G)),
      (rawQuotedFormulaCode M a), (rawQuotedFormulaCode M b),
      (raw_zero M), (raw_zero M),
      (rawQuotedProofCode M h), (raw_zero M), (raw_zero M).
    split; [reflexivity |]. unfold RawProofEndpointCases. eauto 20.
  - exists (rawNumeralValue M (contextCode G)),
      (rawQuotedFormulaCode M a), (rawQuotedFormulaCode M b),
      (rawQuotedFormulaCode M c),
      (rawFormulaOrCode M (rawQuotedFormulaCode M a)
        (rawQuotedFormulaCode M b)),
      (rawQuotedProofCode M hOr), (rawQuotedProofCode M hA),
      (rawQuotedProofCode M hB).
    split; [reflexivity |]. unfold RawProofEndpointCases. eauto 20.
  - exists (rawNumeralValue M (contextCode G)),
      (rawQuotedFormulaCode M a),
      (raw_zero M), (raw_zero M), (raw_zero M),
      (rawQuotedProofCode M h), (raw_zero M), (raw_zero M).
    split; [reflexivity |]. unfold RawProofEndpointCases. eauto 20.
  - assert (hsubst := raw_codedFormulaSingleSubstitution_standard
      M hPA witness a).
    exists (rawNumeralValue M (contextCode G)),
      (rawQuotedFormulaCode M a),
      (rawFormulaAllCode M (rawQuotedFormulaCode M a)),
      (raw_zero M), (rawQuotedTermCode M witness),
      (rawQuotedProofCode M h), (raw_zero M), (raw_zero M).
    split; [reflexivity |]. unfold RawProofEndpointCases. eauto 20.
  - exists (rawNumeralValue M (contextCode G)),
      (rawQuotedFormulaCode M a),
      (rawQuotedFormulaCode M
        (Formula.subst (Formula.instTerm witness) a)),
      (raw_zero M), (rawQuotedTermCode M witness),
      (rawQuotedProofCode M h), (raw_zero M), (raw_zero M).
    split; [reflexivity |]. unfold RawProofEndpointCases. eauto 20.
  - exists (rawNumeralValue M (contextCode G)),
      (rawQuotedFormulaCode M a), (rawQuotedFormulaCode M c),
      (raw_zero M), (raw_zero M),
      (rawQuotedProofCode M hEx), (rawQuotedProofCode M hBody),
      (raw_zero M).
    split; [reflexivity |]. unfold RawProofEndpointCases. eauto 20.
  - exists (rawNumeralValue M (contextCode G)),
      (raw_zero M), (raw_zero M), (raw_zero M),
      (rawQuotedTermCode M witness),
      (raw_zero M), (raw_zero M), (raw_zero M).
    split; [reflexivity |]. unfold RawProofEndpointCases. eauto 20.
  - assert (hsubst := raw_codedFormulaSingleSubstitution_standard
      M hPA target a).
    exists (rawNumeralValue M (contextCode G)),
      (rawQuotedTermCode M source), (rawQuotedTermCode M target),
      (rawQuotedFormulaCode M a),
      (rawFormulaEqCode M (rawQuotedTermCode M source)
        (rawQuotedTermCode M target)),
      (rawQuotedProofCode M hEq), (rawQuotedProofCode M hA),
      (raw_zero M).
    split; [reflexivity |]. unfold RawProofEndpointCases. eauto 20.
Qed.

Corollary raw_quotedProof_endpoint : forall (M : RawPAModel),
  RawPASatisfies M -> forall derivation,
  RawProofEndpoint M (rawQuotedProofCode M derivation)
    (rawQuotedContextCode M (rawContext derivation))
    (rawQuotedFormulaCode M (rawConclusion derivation)).
Proof. exact raw_quotedProof_endpoint_for_rules. Qed.

(** Declarative raw validity is represented by the arithmetic local-rule
    relation on standard quotations.  Child endpoint facts are supplied by
    [raw_quotedProof_endpoint]; no recursive model decoding is involved. *)
Lemma raw_quotedProof_rule_valid : forall (M : RawPAModel),
  RawPASatisfies M -> forall derivation,
  RawProofValid derivation ->
  RawProofRuleValid M (rawQuotedProofCode M derivation)
    (rawQuotedContextCode M (rawContext derivation))
    (rawQuotedFormulaCode M (rawConclusion derivation)).
Proof.
  intros M hPA derivation hvalid.
  destruct derivation as
    [G a | G a b h | G a b hImp hA | G a h | G a
    | G a b hA hB | G a b h | G a b h
    | G a b h | G a b h | G a b c hOr hA hB
    | G a h | G a witness h | G a witness h
    | G a c hEx hBody | G witness
    | G source target a hEq hA];
    cbn [RawProofValid rawContext rawConclusion] in hvalid |- *.
  - exists (rawQuotedContextCode M G),
      (rawQuotedFormulaCode M a),
      (raw_zero M), (raw_zero M), (raw_zero M),
      (raw_zero M), (raw_zero M), (raw_zero M).
    split; [reflexivity |].
    assert (hcode : rawQuotedProofCode M (RP_ass G a) =
        rawListCode M [rawNumeralValue M 0;
          rawQuotedContextCode M G; rawQuotedFormulaCode M a]).
    {
      cbn [rawQuotedProofCode].
      rewrite rawQuotedContextCode_standard by exact hPA. reflexivity.
    }
    unfold RawProofRuleValidCases. eauto 30 using raw_quotedContext_member.
  - destruct hvalid as [_ [hcontext hconclusion]].
    pose proof (raw_quotedProof_endpoint M hPA h) as hchild.
    rewrite hcontext, hconclusion in hchild.
    exists (rawQuotedContextCode M G),
      (rawQuotedFormulaCode M a), (rawQuotedFormulaCode M b),
      (raw_zero M), (raw_zero M),
      (rawQuotedProofCode M h), (raw_zero M), (raw_zero M).
    split; [reflexivity |].
    assert (hcode : rawQuotedProofCode M (RP_impI G a b h) =
        rawListCode M [rawNumeralValue M 1;
          rawQuotedContextCode M G; rawQuotedFormulaCode M a;
          rawQuotedFormulaCode M b; rawQuotedProofCode M h]).
    {
      cbn [rawQuotedProofCode].
      rewrite rawQuotedContextCode_standard by exact hPA. reflexivity.
    }
    unfold RawProofRuleValidCases. eauto 30.
  - destruct hvalid as
      [_ [hImpContext [hImpConclusion [_ [hAContext hAConclusion]]]]].
    pose proof (raw_quotedProof_endpoint M hPA hImp) as hImpEndpoint.
    pose proof (raw_quotedProof_endpoint M hPA hA) as hAEndpoint.
    rewrite hImpContext, hImpConclusion in hImpEndpoint.
    rewrite hAContext, hAConclusion in hAEndpoint.
    exists (rawQuotedContextCode M G),
      (rawQuotedFormulaCode M a), (rawQuotedFormulaCode M b),
      (rawQuotedFormulaCode M (pImp a b)), (raw_zero M),
      (rawQuotedProofCode M hImp), (rawQuotedProofCode M hA),
      (raw_zero M).
    split; [reflexivity |].
    assert (hcode : rawQuotedProofCode M (RP_impE G a b hImp hA) =
        rawListCode M [rawNumeralValue M 2;
          rawQuotedContextCode M G; rawQuotedFormulaCode M a;
          rawQuotedFormulaCode M b; rawQuotedProofCode M hImp;
          rawQuotedProofCode M hA]).
    {
      cbn [rawQuotedProofCode].
      rewrite rawQuotedContextCode_standard by exact hPA. reflexivity.
    }
    unfold RawProofRuleValidCases. eauto 30.
  - destruct hvalid as [_ [hcontext hconclusion]].
    pose proof (raw_quotedProof_endpoint M hPA h) as hchild.
    rewrite hcontext, hconclusion in hchild.
    exists (rawQuotedContextCode M G),
      (rawQuotedFormulaCode M a), (rawFormulaBotCode M),
      (raw_zero M), (raw_zero M),
      (rawQuotedProofCode M h), (raw_zero M), (raw_zero M).
    split; [reflexivity |].
    assert (hcode : rawQuotedProofCode M (RP_botE G a h) =
        rawListCode M [rawNumeralValue M 3;
          rawQuotedContextCode M G; rawQuotedFormulaCode M a;
          rawQuotedProofCode M h]).
    {
      cbn [rawQuotedProofCode].
      rewrite rawQuotedContextCode_standard by exact hPA. reflexivity.
    }
    unfold RawProofRuleValidCases. eauto 30.
  - exists (rawQuotedContextCode M G),
      (rawQuotedFormulaCode M a),
      (rawFormulaImpCode M (rawQuotedFormulaCode M a)
        (rawFormulaBotCode M)),
      (rawFormulaBotCode M), (raw_zero M),
      (raw_zero M), (raw_zero M), (raw_zero M).
    split; [reflexivity |].
    assert (hcode : rawQuotedProofCode M (RP_lem G a) =
        rawListCode M [rawNumeralValue M 4;
          rawQuotedContextCode M G; rawQuotedFormulaCode M a]).
    {
      cbn [rawQuotedProofCode].
      rewrite rawQuotedContextCode_standard by exact hPA. reflexivity.
    }
    unfold RawProofRuleValidCases. eauto 30.
  - destruct hvalid as
      [_ [hAContext [hAConclusion [_ [hBContext hBConclusion]]]]].
    pose proof (raw_quotedProof_endpoint M hPA hA) as hAEndpoint.
    pose proof (raw_quotedProof_endpoint M hPA hB) as hBEndpoint.
    rewrite hAContext, hAConclusion in hAEndpoint.
    rewrite hBContext, hBConclusion in hBEndpoint.
    exists (rawQuotedContextCode M G),
      (rawQuotedFormulaCode M a), (rawQuotedFormulaCode M b),
      (raw_zero M), (raw_zero M),
      (rawQuotedProofCode M hA), (rawQuotedProofCode M hB),
      (raw_zero M).
    split; [reflexivity |].
    assert (hcode : rawQuotedProofCode M (RP_andI G a b hA hB) =
        rawListCode M [rawNumeralValue M 5;
          rawQuotedContextCode M G; rawQuotedFormulaCode M a;
          rawQuotedFormulaCode M b; rawQuotedProofCode M hA;
          rawQuotedProofCode M hB]).
    {
      cbn [rawQuotedProofCode].
      rewrite rawQuotedContextCode_standard by exact hPA. reflexivity.
    }
    unfold RawProofRuleValidCases. eauto 30.
  - destruct hvalid as [_ [hcontext hconclusion]].
    pose proof (raw_quotedProof_endpoint M hPA h) as hchild.
    rewrite hcontext, hconclusion in hchild.
    exists (rawQuotedContextCode M G),
      (rawQuotedFormulaCode M a), (rawQuotedFormulaCode M b),
      (rawQuotedFormulaCode M (pAnd a b)), (raw_zero M),
      (rawQuotedProofCode M h), (raw_zero M), (raw_zero M).
    split; [reflexivity |].
    assert (hcode : rawQuotedProofCode M (RP_andE1 G a b h) =
        rawListCode M [rawNumeralValue M 6;
          rawQuotedContextCode M G; rawQuotedFormulaCode M a;
          rawQuotedFormulaCode M b; rawQuotedProofCode M h]).
    {
      cbn [rawQuotedProofCode].
      rewrite rawQuotedContextCode_standard by exact hPA. reflexivity.
    }
    unfold RawProofRuleValidCases. eauto 30.
  - destruct hvalid as [_ [hcontext hconclusion]].
    pose proof (raw_quotedProof_endpoint M hPA h) as hchild.
    rewrite hcontext, hconclusion in hchild.
    exists (rawQuotedContextCode M G),
      (rawQuotedFormulaCode M a), (rawQuotedFormulaCode M b),
      (rawQuotedFormulaCode M (pAnd a b)), (raw_zero M),
      (rawQuotedProofCode M h), (raw_zero M), (raw_zero M).
    split; [reflexivity |].
    assert (hcode : rawQuotedProofCode M (RP_andE2 G a b h) =
        rawListCode M [rawNumeralValue M 7;
          rawQuotedContextCode M G; rawQuotedFormulaCode M a;
          rawQuotedFormulaCode M b; rawQuotedProofCode M h]).
    {
      cbn [rawQuotedProofCode].
      rewrite rawQuotedContextCode_standard by exact hPA. reflexivity.
    }
    unfold RawProofRuleValidCases. eauto 30.
  - destruct hvalid as [_ [hcontext hconclusion]].
    pose proof (raw_quotedProof_endpoint M hPA h) as hchild.
    rewrite hcontext, hconclusion in hchild.
    exists (rawQuotedContextCode M G),
      (rawQuotedFormulaCode M a), (rawQuotedFormulaCode M b),
      (raw_zero M), (raw_zero M),
      (rawQuotedProofCode M h), (raw_zero M), (raw_zero M).
    split; [reflexivity |].
    assert (hcode : rawQuotedProofCode M (RP_orI1 G a b h) =
        rawListCode M [rawNumeralValue M 8;
          rawQuotedContextCode M G; rawQuotedFormulaCode M a;
          rawQuotedFormulaCode M b; rawQuotedProofCode M h]).
    {
      cbn [rawQuotedProofCode].
      rewrite rawQuotedContextCode_standard by exact hPA. reflexivity.
    }
    unfold RawProofRuleValidCases. eauto 30.
  - destruct hvalid as [_ [hcontext hconclusion]].
    pose proof (raw_quotedProof_endpoint M hPA h) as hchild.
    rewrite hcontext, hconclusion in hchild.
    exists (rawQuotedContextCode M G),
      (rawQuotedFormulaCode M a), (rawQuotedFormulaCode M b),
      (raw_zero M), (raw_zero M),
      (rawQuotedProofCode M h), (raw_zero M), (raw_zero M).
    split; [reflexivity |].
    assert (hcode : rawQuotedProofCode M (RP_orI2 G a b h) =
        rawListCode M [rawNumeralValue M 9;
          rawQuotedContextCode M G; rawQuotedFormulaCode M a;
          rawQuotedFormulaCode M b; rawQuotedProofCode M h]).
    {
      cbn [rawQuotedProofCode].
      rewrite rawQuotedContextCode_standard by exact hPA. reflexivity.
    }
    unfold RawProofRuleValidCases. eauto 30.
  - destruct hvalid as
      [_ [hOrContext [hOrConclusion
        [_ [hAContext [hAConclusion [_ [hBContext hBConclusion]]]]]]]].
    pose proof (raw_quotedProof_endpoint M hPA hOr) as hOrEndpoint.
    pose proof (raw_quotedProof_endpoint M hPA hA) as hAEndpoint.
    pose proof (raw_quotedProof_endpoint M hPA hB) as hBEndpoint.
    rewrite hOrContext, hOrConclusion in hOrEndpoint.
    rewrite hAContext, hAConclusion in hAEndpoint.
    rewrite hBContext, hBConclusion in hBEndpoint.
    exists (rawQuotedContextCode M G),
      (rawQuotedFormulaCode M a), (rawQuotedFormulaCode M b),
      (rawQuotedFormulaCode M c),
      (rawQuotedFormulaCode M (pOr a b)),
      (rawQuotedProofCode M hOr), (rawQuotedProofCode M hA),
      (rawQuotedProofCode M hB).
    split; [reflexivity |].
    assert (hcode : rawQuotedProofCode M
        (RP_orE G a b c hOr hA hB) =
        rawListCode M [rawNumeralValue M 10;
          rawQuotedContextCode M G; rawQuotedFormulaCode M a;
          rawQuotedFormulaCode M b; rawQuotedFormulaCode M c;
          rawQuotedProofCode M hOr; rawQuotedProofCode M hA;
          rawQuotedProofCode M hB]).
    {
      cbn [rawQuotedProofCode].
      rewrite rawQuotedContextCode_standard by exact hPA. reflexivity.
    }
    unfold RawProofRuleValidCases. eauto 30.
  - destruct hvalid as [_ [hcontext hconclusion]].
    pose proof (raw_quotedProof_endpoint M hPA h) as hchild.
    rewrite hcontext, hconclusion in hchild.
    pose proof (raw_quotedContext_shift M hPA G) as hshift.
    exists (rawQuotedContextCode M G),
      (rawQuotedFormulaCode M a),
      (rawQuotedContextCode M (map (Formula.rename S) G)),
      (raw_zero M), (raw_zero M),
      (rawQuotedProofCode M h), (raw_zero M), (raw_zero M).
    split; [reflexivity |].
    assert (hcode : rawQuotedProofCode M (RP_allI G a h) =
        rawListCode M [rawNumeralValue M 11;
          rawQuotedContextCode M G; rawQuotedFormulaCode M a;
          rawQuotedProofCode M h]).
    {
      cbn [rawQuotedProofCode].
      rewrite rawQuotedContextCode_standard by exact hPA. reflexivity.
    }
    unfold RawProofRuleValidCases. eauto 30.
  - destruct hvalid as [_ [hcontext hconclusion]].
    pose proof (raw_quotedProof_endpoint M hPA h) as hchild.
    rewrite hcontext, hconclusion in hchild.
    pose proof (raw_codedFormulaSingleSubstitution_standard
      M hPA witness a) as hsubst.
    exists (rawQuotedContextCode M G),
      (rawQuotedFormulaCode M a),
      (rawQuotedFormulaCode M (pAll a)),
      (raw_zero M), (rawQuotedTermCode M witness),
      (rawQuotedProofCode M h), (raw_zero M), (raw_zero M).
    split; [reflexivity |].
    assert (hcode : rawQuotedProofCode M (RP_allE G a witness h) =
        rawListCode M [rawNumeralValue M 12;
          rawQuotedContextCode M G; rawQuotedFormulaCode M a;
          rawQuotedTermCode M witness; rawQuotedProofCode M h]).
    {
      cbn [rawQuotedProofCode].
      rewrite rawQuotedContextCode_standard by exact hPA. reflexivity.
    }
    unfold RawProofRuleValidCases. eauto 30.
  - destruct hvalid as [_ [hcontext hconclusion]].
    pose proof (raw_quotedProof_endpoint M hPA h) as hchild.
    rewrite hcontext, hconclusion in hchild.
    pose proof (raw_codedFormulaSingleSubstitution_standard
      M hPA witness a) as hsubst.
    exists (rawQuotedContextCode M G),
      (rawQuotedFormulaCode M a),
      (rawQuotedFormulaCode M
        (Formula.subst (Formula.instTerm witness) a)),
      (raw_zero M), (rawQuotedTermCode M witness),
      (rawQuotedProofCode M h), (raw_zero M), (raw_zero M).
    split; [reflexivity |].
    assert (hcode : rawQuotedProofCode M (RP_exI G a witness h) =
        rawListCode M [rawNumeralValue M 13;
          rawQuotedContextCode M G; rawQuotedFormulaCode M a;
          rawQuotedTermCode M witness; rawQuotedProofCode M h]).
    {
      cbn [rawQuotedProofCode].
      rewrite rawQuotedContextCode_standard by exact hPA. reflexivity.
    }
    unfold RawProofRuleValidCases. eauto 30.
  - destruct hvalid as
      [_ [hExContext [hExConclusion [_ [hBodyContext hBodyConclusion]]]]].
    pose proof (raw_quotedProof_endpoint M hPA hEx) as hExEndpoint.
    pose proof (raw_quotedProof_endpoint M hPA hBody) as hBodyEndpoint.
    rewrite hExContext, hExConclusion in hExEndpoint.
    rewrite hBodyContext, hBodyConclusion in hBodyEndpoint.
    pose proof (raw_quotedContext_shift M hPA G) as hshift.
    pose proof (raw_codedFormulaShift_standard_zero_one M hPA c) as hcShift.
    exists (rawQuotedContextCode M G),
      (rawQuotedFormulaCode M a), (rawQuotedFormulaCode M c),
      (rawQuotedContextCode M (map (Formula.rename S) G)),
      (rawQuotedFormulaCode M (Formula.rename S c)),
      (rawQuotedProofCode M hEx), (rawQuotedProofCode M hBody),
      (rawQuotedFormulaCode M (pEx a)).
    split; [reflexivity |].
    assert (hcode : rawQuotedProofCode M (RP_exE G a c hEx hBody) =
        rawListCode M [rawNumeralValue M 14;
          rawQuotedContextCode M G; rawQuotedFormulaCode M a;
          rawQuotedFormulaCode M c; rawQuotedProofCode M hEx;
          rawQuotedProofCode M hBody]).
    {
      cbn [rawQuotedProofCode].
      rewrite rawQuotedContextCode_standard by exact hPA. reflexivity.
    }
    unfold RawProofRuleValidCases. eauto 35.
  - exists (rawQuotedContextCode M G),
      (raw_zero M), (raw_zero M), (raw_zero M),
      (rawQuotedTermCode M witness),
      (raw_zero M), (raw_zero M), (raw_zero M).
    split; [reflexivity |].
    assert (hcode : rawQuotedProofCode M (RP_eqRefl G witness) =
        rawListCode M [rawNumeralValue M 15;
          rawQuotedContextCode M G; rawQuotedTermCode M witness]).
    {
      cbn [rawQuotedProofCode].
      rewrite rawQuotedContextCode_standard by exact hPA. reflexivity.
    }
    unfold RawProofRuleValidCases. eauto 30.
  - destruct hvalid as
      [_ [hEqContext [hEqConclusion [_ [hAContext hAConclusion]]]]].
    pose proof (raw_quotedProof_endpoint M hPA hEq) as hEqEndpoint.
    pose proof (raw_quotedProof_endpoint M hPA hA) as hAEndpoint.
    rewrite hEqContext, hEqConclusion in hEqEndpoint.
    rewrite hAContext, hAConclusion in hAEndpoint.
    pose proof (raw_codedFormulaSingleSubstitution_standard
      M hPA target a) as htargetSubst.
    pose proof (raw_codedFormulaSingleSubstitution_standard
      M hPA source a) as hsourceSubst.
    exists (rawQuotedContextCode M G),
      (rawQuotedTermCode M source), (rawQuotedTermCode M target),
      (rawQuotedFormulaCode M a),
      (rawQuotedFormulaCode M (pEq source target)),
      (rawQuotedProofCode M hEq), (rawQuotedProofCode M hA),
      (rawQuotedFormulaCode M
        (Formula.subst (Formula.instTerm source) a)).
    split; [reflexivity |].
    assert (hcode : rawQuotedProofCode M
        (RP_eqElim G source target a hEq hA) =
        rawListCode M [rawNumeralValue M 16;
          rawQuotedContextCode M G; rawQuotedTermCode M source;
          rawQuotedTermCode M target; rawQuotedFormulaCode M a;
          rawQuotedProofCode M hEq; rawQuotedProofCode M hA]).
    {
      cbn [rawQuotedProofCode].
      rewrite rawQuotedContextCode_standard by exact hPA. reflexivity.
    }
    unfold RawProofRuleValidCases. eauto 35.
Qed.


Lemma raw_quotedContext_realizable_direct : forall (M : RawPAModel),
  RawPASatisfies M -> forall context,
  RawContextListRealizable M (rawQuotedContextCode M context).
Proof.
  intros M hPA context. induction context as [|head tail IH].
  - apply raw_contextList_empty_realizable. exact hPA.
  - cbn. apply raw_contextList_cons_realizable; assumption.
Qed.

Lemma raw_quotedContext_member_direct : forall (M : RawPAModel),
  RawPASatisfies M -> forall context phi,
  In phi context ->
  RawContextListMember M
    (rawQuotedContextCode M context) (rawQuotedFormulaCode M phi).
Proof.
  intros M hPA context. induction context as [|head tail IH];
    intros phi hin; cbn in hin |- *.
  - contradiction.
  - destruct hin as [-> | hin].
    + apply raw_contextList_cons_head_member; [exact hPA |].
      apply raw_quotedContext_realizable. exact hPA.
    + apply raw_contextList_cons_tail_member; [exact hPA |].
      exact (IH phi hin).
Qed.

(** Every formula-operation row is, after forgetting the transformed formula
    and binder-depth columns, an ordinary syntax row for its source formula.
    This observation lets us reuse the already constructed standard shift
    trace as a well-formedness certificate for a quoted formula. *)
Lemma raw_formulaOperationTraversalRow_source_syntax : forall
    (M : RawPAModel) atom parameter
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    index input output depth,
  RawCodedFormulaOperationTraversalRow M atom parameter
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    index input output depth ->
  RawCodedFormulaSyntaxTraversalRow M
    sourceCode sourceStep index input.
Proof.
  intros M atom parameter sourceCode sourceStep targetCode targetStep
    depthCode depthStep index input output depth hrow.
  unfold RawCodedFormulaOperationTraversalRow in hrow.
  unfold RawCodedFormulaSyntaxTraversalRow.
  destruct hrow as
      [heq | [hbot | [himp | [hand | [hor | [hall | hex]]]]]].
  - left. destruct heq as
      (inputLeft & outputLeft & inputRight & outputRight &
       hinput & _ & _ & _).
    exists inputLeft, inputRight. exact hinput.
  - right; left. exact (proj1 hbot).
  - right; right; left.
    destruct himp as
      (leftIndex & inputLeft & outputLeft & leftDepth &
       rightIndex & inputRight & outputRight & rightDepth &
       hleftIndex & hleftLookup & _ & hrightIndex & hrightLookup & _ &
       hinput & _).
    exists leftIndex, inputLeft, rightIndex, inputRight.
    split; [exact hleftIndex |].
    split; [exact (proj1 hleftLookup) |].
    split; [exact hrightIndex |].
    split; [exact (proj1 hrightLookup) | exact hinput].
  - right; right; right; left.
    destruct hand as
      (leftIndex & inputLeft & outputLeft & leftDepth &
       rightIndex & inputRight & outputRight & rightDepth &
       hleftIndex & hleftLookup & _ & hrightIndex & hrightLookup & _ &
       hinput & _).
    exists leftIndex, inputLeft, rightIndex, inputRight.
    split; [exact hleftIndex |].
    split; [exact (proj1 hleftLookup) |].
    split; [exact hrightIndex |].
    split; [exact (proj1 hrightLookup) | exact hinput].
  - right; right; right; right; left.
    destruct hor as
      (leftIndex & inputLeft & outputLeft & leftDepth &
       rightIndex & inputRight & outputRight & rightDepth &
       hleftIndex & hleftLookup & _ & hrightIndex & hrightLookup & _ &
       hinput & _).
    exists leftIndex, inputLeft, rightIndex, inputRight.
    split; [exact hleftIndex |].
    split; [exact (proj1 hleftLookup) |].
    split; [exact hrightIndex |].
    split; [exact (proj1 hrightLookup) | exact hinput].
  - right; right; right; right; right; left.
    destruct hall as
      (childIndex & inputChild & outputChild & childDepth &
       hchildIndex & hchildLookup & _ & hinput & _).
    exists childIndex, inputChild.
    split; [exact hchildIndex |].
    split; [exact (proj1 hchildLookup) | exact hinput].
  - right; right; right; right; right; right.
    destruct hex as
      (childIndex & inputChild & outputChild & childDepth &
       hchildIndex & hchildLookup & _ & hinput & _).
    exists childIndex, inputChild.
    split; [exact hchildIndex |].
    split; [exact (proj1 hchildLookup) | exact hinput].
Qed.

Lemma raw_formulaOperationTrace_source_syntax : forall
    (M : RawPAModel) atom parameter rootDepth
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound rootIndex input output,
  RawCodedFormulaOperationTrace M atom parameter rootDepth
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound rootIndex input output ->
  RawCodedFormulaSyntaxTraversal M
    sourceCode sourceStep bound rootIndex input.
Proof.
  intros M atom parameter rootDepth sourceCode sourceStep
    targetCode targetStep depthCode depthStep bound rootIndex input output
    (hsourceDefined & htargetDefined & hdepthDefined & hrootBelow &
     hrootLookup & hrows).
  split; [exact hsourceDefined |].
  split; [exact hrootBelow |].
  split; [exact (proj1 hrootLookup) |].
  intros index code hindexBelow hsourceLookup.
  destruct (htargetDefined index hindexBelow) as [target htargetLookup].
  destruct (hdepthDefined index hindexBelow) as [depth hdepthLookup].
  apply (raw_formulaOperationTraversalRow_source_syntax M atom parameter
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    index code target depth).
  apply hrows; [exact hindexBelow |].
  split; [exact hsourceLookup |].
  split; assumption.
Qed.

Lemma raw_quotedFormula_wellformed : forall (M : RawPAModel),
  RawPASatisfies M -> forall phi,
  RawCodedWellFormedFormula M (rawQuotedFormulaCode M phi).
Proof.
  intros M hPA phi.
  pose proof (raw_codedFormulaShift_standard M hPA 0 0 phi) as hshift.
  unfold RawCodedFormulaShift, RawCodedFormulaOperation in hshift.
  destruct hshift as
    (sourceCode & sourceStep & targetCode & targetStep &
     depthCode & depthStep & bound & rootIndex & htrace).
  exists sourceCode, sourceStep, bound, rootIndex.
  eapply raw_formulaOperationTrace_source_syntax.
  exact htrace.
Qed.

(** The exact standard rank certificate used by context and occurrence
    boundedness. *)
Definition RawStandardFormulaRankQuotation (M : RawPAModel) : Prop :=
  forall phi,
    RawCodedFormulaRank M (rawQuotedFormulaCode M phi)
      (rawNumeralValue M (sigmaRank phi))
      (rawNumeralValue M (piRank phi)).

Arguments RawStandardFormulaRankQuotation M : clear implicits.

(** Rank totality applies to the source syntax traversal just extracted;
    standard-rank soundness then identifies its two outputs with the
    meta-level hierarchy ranks. *)
Theorem raw_standardFormulaRankQuotation : forall (M : RawPAModel),
  RawPASatisfies M -> RawStandardFormulaRankQuotation M.
Proof.
  intros M hPA phi.
  destruct (raw_codedWellFormedFormula_rank_exists M hPA
    (rawQuotedFormulaCode M phi)
    (raw_quotedFormula_wellformed M hPA phi)) as
      (sigma & pi & hrank).
  destruct (raw_codedFormulaRank_standard_sound
    polynomialPairInjectivityProof M hPA phi sigma pi hrank) as
      [hsigma hpi].
  subst sigma. subst pi. exact hrank.
Qed.

Lemma raw_quotedFormula_quantifier_bounded : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawStandardFormulaRankQuotation M ->
  forall level phi,
  quantifierGroups phi <= level ->
  RawFormulaQuantifierBounded M level (rawQuotedFormulaCode M phi).
Proof.
  intros M hPA hrank level phi hbounded.
  unfold RawFormulaQuantifierBounded.
  unfold quantifierGroups in hbounded.
  destruct (Nat.le_ge_cases (sigmaRank phi) (piRank phi)) as
      [hsigmaPi | hpiSigma].
  - left. exists (rawNumeralValue M (sigmaRank phi)),
      (rawNumeralValue M (piRank phi)).
    split; [apply hrank |].
    apply rawLe_numerals_of_le; [exact hPA |].
    rewrite Nat.min_l in hbounded by exact hsigmaPi. exact hbounded.
  - right. exists (rawNumeralValue M (sigmaRank phi)),
      (rawNumeralValue M (piRank phi)).
    split; [apply hrank |].
    apply rawLe_numerals_of_le; [exact hPA |].
    rewrite Nat.min_r in hbounded by exact hpiSigma. exact hbounded.
Qed.

Lemma raw_quotedContext_all_bounded : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawStandardFormulaRankQuotation M ->
  forall level context,
  contextRank context <= level ->
  RawContextAllBounded M level (rawQuotedContextCode M context).
Proof.
  intros M hPA hrank level context.
  induction context as [|head tail IH]; intro hbounded.
  - destruct (raw_contextList_zero_traversal_exists M hPA) as
      (tailCode & tailStep & htraversal).
    exists (raw_zero M), tailCode, tailStep, (raw_zero M), (raw_zero M).
    split; [exact htraversal |].
    intros index hindex code hlookup.
    exfalso. exact (raw_not_lt_zero M hPA index hindex).
  - cbn [rawQuotedContextCode].
    apply raw_contextAllBounded_cons; [exact hPA | |].
    + apply IH. cbn [contextRank] in hbounded. lia.
    + apply raw_quotedFormula_quantifier_bounded; try assumption.
      cbn [contextRank] in hbounded. lia.
Qed.

Lemma raw_quotedContext_shift_direct : forall (M : RawPAModel),
  RawPASatisfies M -> forall context,
  RawContextShift M
    (rawQuotedContextCode M context)
    (rawQuotedContextCode M (map (Formula.rename S) context)).
Proof.
  intros M hPA context. induction context as [|head tail IH].
  - cbn. apply raw_contextShift_empty. exact hPA.
  - cbn [rawQuotedContextCode map].
    apply raw_contextShift_cons; [exact hPA | exact IH |].
    apply raw_codedFormulaShift_standard_zero_one. exact hPA.
Qed.

(** Universal endpoint boundedness needs this property for arbitrary traces,
    not merely existence of the canonical trace. *)
Definition RawStandardSingleSubstitutionBounded (M : RawPAModel) : Prop :=
  forall level replacement phi output,
    quantifierGroups phi <= level ->
    RawCodedFormulaSingleSubstitution M
      (rawQuotedTermCode M replacement)
      (rawQuotedFormulaCode M phi) output ->
    RawFormulaQuantifierBounded M level output.

Arguments RawStandardSingleSubstitutionBounded M : clear implicits.

Theorem raw_standardSingleSubstitutionBounded : forall (M : RawPAModel),
  RawPASatisfies M -> RawStandardSingleSubstitutionBounded M.
Proof.
  intros M hPA level replacement phi output hbounded hsubstitution.
  unfold RawCodedFormulaSingleSubstitution in hsubstitution.
  exact (raw_codedFormulaOperation_quoted_quantifier_bounded
    polynomialPairInjectivityProof M hPA level phi
    (RawCodedFormulaSubstitutionAtom M)
    (rawQuotedTermCode M replacement) (raw_zero M) output
    hbounded hsubstitution).
Qed.

(** Every standard raw constructor has its canonical context/conclusion
    endpoint.  This theorem needs no validity premise: endpoints merely expose
    the conclusion determined by the constructor syntax. *)
Lemma raw_quotedProof_endpoint_direct : forall (M : RawPAModel),
  RawPASatisfies M -> forall derivation,
  RawProofEndpoint M (rawQuotedProofCode M derivation)
    (rawQuotedContextCode M (rawContext derivation))
    (rawQuotedFormulaCode M (rawConclusion derivation)).
Proof.
  intros M hPA derivation.
  destruct derivation as
    [G a | G a b h | G a b hImp hA | G a h | G a
    | G a b hA hB | G a b h | G a b h
    | G a b h | G a b h | G a b c hOr hA hB
    | G a h | G a witness h | G a witness h
    | G a c hEx hBody | G witness
    | G source target a hEq hA];
    cbn [rawContext rawConclusion rawQuotedProofCode rawQuotedFormulaCode];
    rewrite rawQuotedContextCode_standard by exact hPA.
  - exists (rawNumeralValue M (contextCode G)),
      (rawQuotedFormulaCode M a),
      (raw_zero M), (raw_zero M), (raw_zero M),
      (raw_zero M), (raw_zero M), (raw_zero M).
    split; [reflexivity |]. unfold RawProofEndpointCases. eauto 20.
  - exists (rawNumeralValue M (contextCode G)),
      (rawQuotedFormulaCode M a), (rawQuotedFormulaCode M b),
      (raw_zero M), (raw_zero M),
      (rawQuotedProofCode M h), (raw_zero M), (raw_zero M).
    split; [reflexivity |]. unfold RawProofEndpointCases. eauto 20.
  - exists (rawNumeralValue M (contextCode G)),
      (rawQuotedFormulaCode M a), (rawQuotedFormulaCode M b),
      (raw_zero M), (raw_zero M),
      (rawQuotedProofCode M hImp), (rawQuotedProofCode M hA),
      (raw_zero M).
    split; [reflexivity |]. unfold RawProofEndpointCases. eauto 20.
  - exists (rawNumeralValue M (contextCode G)),
      (rawQuotedFormulaCode M a),
      (raw_zero M), (raw_zero M), (raw_zero M),
      (rawQuotedProofCode M h), (raw_zero M), (raw_zero M).
    split; [reflexivity |]. unfold RawProofEndpointCases. eauto 20.
  - exists (rawNumeralValue M (contextCode G)),
      (rawQuotedFormulaCode M a),
      (rawFormulaImpCode M (rawQuotedFormulaCode M a)
        (rawFormulaBotCode M)),
      (rawFormulaBotCode M), (raw_zero M),
      (raw_zero M), (raw_zero M), (raw_zero M).
    split; [reflexivity |]. unfold RawProofEndpointCases. eauto 20.
  - exists (rawNumeralValue M (contextCode G)),
      (rawQuotedFormulaCode M a), (rawQuotedFormulaCode M b),
      (raw_zero M), (raw_zero M),
      (rawQuotedProofCode M hA), (rawQuotedProofCode M hB),
      (raw_zero M).
    split; [reflexivity |]. unfold RawProofEndpointCases. eauto 20.
  - exists (rawNumeralValue M (contextCode G)),
      (rawQuotedFormulaCode M a), (rawQuotedFormulaCode M b),
      (raw_zero M), (raw_zero M),
      (rawQuotedProofCode M h), (raw_zero M), (raw_zero M).
    split; [reflexivity |]. unfold RawProofEndpointCases. eauto 20.
  - exists (rawNumeralValue M (contextCode G)),
      (rawQuotedFormulaCode M a), (rawQuotedFormulaCode M b),
      (raw_zero M), (raw_zero M),
      (rawQuotedProofCode M h), (raw_zero M), (raw_zero M).
    split; [reflexivity |]. unfold RawProofEndpointCases. eauto 20.
  - exists (rawNumeralValue M (contextCode G)),
      (rawQuotedFormulaCode M a), (rawQuotedFormulaCode M b),
      (raw_zero M), (raw_zero M),
      (rawQuotedProofCode M h), (raw_zero M), (raw_zero M).
    split; [reflexivity |]. unfold RawProofEndpointCases. eauto 20.
  - exists (rawNumeralValue M (contextCode G)),
      (rawQuotedFormulaCode M a), (rawQuotedFormulaCode M b),
      (raw_zero M), (raw_zero M),
      (rawQuotedProofCode M h), (raw_zero M), (raw_zero M).
    split; [reflexivity |]. unfold RawProofEndpointCases. eauto 20.
  - exists (rawNumeralValue M (contextCode G)),
      (rawQuotedFormulaCode M a), (rawQuotedFormulaCode M b),
      (rawQuotedFormulaCode M c),
      (rawFormulaOrCode M (rawQuotedFormulaCode M a)
        (rawQuotedFormulaCode M b)),
      (rawQuotedProofCode M hOr), (rawQuotedProofCode M hA),
      (rawQuotedProofCode M hB).
    split; [reflexivity |]. unfold RawProofEndpointCases. eauto 20.
  - exists (rawNumeralValue M (contextCode G)),
      (rawQuotedFormulaCode M a),
      (raw_zero M), (raw_zero M), (raw_zero M),
      (rawQuotedProofCode M h), (raw_zero M), (raw_zero M).
    split; [reflexivity |]. unfold RawProofEndpointCases. eauto 20.
  - assert (hsubst := raw_codedFormulaSingleSubstitution_standard
      M hPA witness a).
    exists (rawNumeralValue M (contextCode G)),
      (rawQuotedFormulaCode M a),
      (rawFormulaAllCode M (rawQuotedFormulaCode M a)),
      (raw_zero M), (rawQuotedTermCode M witness),
      (rawQuotedProofCode M h), (raw_zero M), (raw_zero M).
    split; [reflexivity |]. unfold RawProofEndpointCases. eauto 20.
  - exists (rawNumeralValue M (contextCode G)),
      (rawQuotedFormulaCode M a),
      (rawQuotedFormulaCode M
        (Formula.subst (Formula.instTerm witness) a)),
      (raw_zero M), (rawQuotedTermCode M witness),
      (rawQuotedProofCode M h), (raw_zero M), (raw_zero M).
    split; [reflexivity |]. unfold RawProofEndpointCases. eauto 20.
  - exists (rawNumeralValue M (contextCode G)),
      (rawQuotedFormulaCode M a), (rawQuotedFormulaCode M c),
      (raw_zero M), (raw_zero M),
      (rawQuotedProofCode M hEx), (rawQuotedProofCode M hBody),
      (raw_zero M).
    split; [reflexivity |]. unfold RawProofEndpointCases. eauto 20.
  - exists (rawNumeralValue M (contextCode G)),
      (raw_zero M), (raw_zero M), (raw_zero M),
      (rawQuotedTermCode M witness),
      (raw_zero M), (raw_zero M), (raw_zero M).
    split; [reflexivity |]. unfold RawProofEndpointCases. eauto 20.
  - assert (hsubst := raw_codedFormulaSingleSubstitution_standard
      M hPA target a).
    exists (rawNumeralValue M (contextCode G)),
      (rawQuotedTermCode M source), (rawQuotedTermCode M target),
      (rawQuotedFormulaCode M a),
      (rawFormulaEqCode M (rawQuotedTermCode M source)
        (rawQuotedTermCode M target)),
      (rawQuotedProofCode M hEq), (rawQuotedProofCode M hA),
      (raw_zero M).
    split; [reflexivity |]. unfold RawProofEndpointCases. eauto 20.
Qed.

(** Validity and the external occurrence bound are inherited by each genuine
    recursive child.  These two elementary facts justify the restricted
    support table built below. *)
Lemma rawProofValid_child : forall derivation child,
  RawProofValid derivation ->
  In child (rawChildren derivation) ->
  RawProofValid child.
Proof.
  intros derivation child hvalid hchild.
  destruct derivation; cbn [RawProofValid rawChildren] in hvalid, hchild;
    cbn [In] in hchild;
    repeat match type of hchild with
    | _ \/ _ => destruct hchild as [hchild | hchild]
    end; try contradiction; subst child; tauto.
Qed.

Lemma rawProofOccurrenceRank_child_le : forall derivation child,
  In child (rawChildren derivation) ->
  rawProofOccurrenceRank child <= rawProofOccurrenceRank derivation.
Proof.
  intros derivation child hchild.
  destruct derivation;
    cbn [rawChildren] in hchild;
    cbn [In] in hchild;
    repeat match type of hchild with
    | _ \/ _ => destruct hchild as [hchild | hchild]
    end; try contradiction; subst child;
    cbn [rawProofOccurrenceRank rawContext rawConclusion]; lia.
Qed.

(** Every constructor occurrence for a standard quotation has the standard
    context and standard formula fields.  Complete-list injectivity handles
    arities uniformly; successor cancellation separates the constructor tag. *)
Lemma raw_quotedProof_constructor_occurrences_bounded : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawStandardFormulaRankQuotation M ->
  forall level derivation,
  rawProofOccurrenceRank derivation <= level ->
  RawProofConstructorOccurrencesBounded M level
    (rawQuotedProofCode M derivation).
Proof.
  intros M hPA hrank level derivation hbound
    context a b c t child1 child2 child3.
  apply Forall_forall. intros [constructorCode formulaFields] hentry.
  unfold rawProofOccurrenceCases in hentry.
  repeat destruct hentry as [hentry | hentry]; try contradiction.
  all: inversion hentry; subst constructorCode formulaFields; clear hentry.
  all: unfold RawProofOccurrenceCaseBounded; intro hcode.
  all: destruct derivation;
    cbn [rawProofOccurrenceRank rawContext rawConclusion] in hbound.
  all: cbn [rawQuotedProofCode rawListCode fst] in hcode.
  all: repeat match goal with
  | hnodes : rawListNode ?model ?head ?tail =
      rawListNode ?model ?head' ?tail' |- _ =>
      destruct (rawListNode_injective model hPA
        head tail head' tail' hnodes) as [? ?]; clear hnodes
  end.
  all: try match goal with
  | hnil : raw_zero ?model = rawListNode ?model ?head ?tail |- _ =>
      exfalso; exact (rawListNode_not_zero model hPA head tail hnil)
  | hnil : rawListNode ?model ?head ?tail = raw_zero ?model |- _ =>
      exfalso; apply (rawListNode_not_zero model hPA head tail);
      exact hnil
  end.
  all: subst.
  all: cbn [rawNumeralValue] in *.
  all: repeat match goal with
  | htag : raw_succ ?model ?left = raw_succ ?model ?right |- _ =>
      apply (raw_succ_injective_syntax model hPA) in htag
  end.
  all: try match goal with
  | htag : raw_zero ?model = raw_succ ?model ?value |- _ =>
      exfalso; exact (raw_zero_not_succ_syntax model hPA value htag)
  | htag : raw_succ ?model ?value = raw_zero ?model |- _ =>
      exfalso; apply (raw_zero_not_succ_syntax model hPA value);
      symmetry; exact htag
  end.
  all: split.
  all: try
    (rewrite <- rawQuotedContextCode_standard by exact hPA;
     apply raw_quotedContext_all_bounded; [exact hPA | exact hrank | lia]).
  all: apply Forall_forall.
  all: intros field hfield.
  all: cbn [snd In] in hfield.
  all: repeat match type of hfield with
  | _ \/ _ => destruct hfield as [hfield | hfield]
  end.
  all: try contradiction.
  all: subst field.
  all: apply raw_quotedFormula_quantifier_bounded;
    [exact hPA | exact hrank | lia].
Qed.

(** Endpoint occurrences are also unique up to the output of an advertised
    substitution trace.  Direct constructor outputs reduce to standard
    quotations; the two substitution cases use precisely the named
    cross-trace boundedness premise. *)
Lemma raw_quotedProof_endpoint_occurrences_bounded : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawStandardFormulaRankQuotation M ->
  RawStandardSingleSubstitutionBounded M ->
  forall level derivation,
  rawProofOccurrenceRank derivation <= level ->
  RawProofEndpointOccurrencesBounded M level
    (rawQuotedProofCode M derivation).
Proof.
  intros M hPA hrank hsubstitution level derivation hbound
    context conclusion hendpoint.
  destruct hendpoint as
    (rowContext & a & b & c & t & child1 & child2 & child3 &
      hrowContext & hcases).
  subst rowContext.
  unfold RawProofEndpointCases in hcases.
  repeat destruct hcases as [hcases | hcases]; try contradiction.
  all: destruct hcases as [hcode hrest].
  all: destruct derivation;
    cbn [rawProofOccurrenceRank rawContext rawConclusion] in hbound.
  all: cbn [rawQuotedProofCode rawListCode] in hcode.
  all: repeat match goal with
  | hnodes : rawListNode ?model ?head ?tail =
      rawListNode ?model ?head' ?tail' |- _ =>
      destruct (rawListNode_injective model hPA
        head tail head' tail' hnodes) as [? ?]; clear hnodes
  end.
  all: try match goal with
  | hnil : raw_zero ?model = rawListNode ?model ?head ?tail |- _ =>
      exfalso; exact (rawListNode_not_zero model hPA head tail hnil)
  | hnil : rawListNode ?model ?head ?tail = raw_zero ?model |- _ =>
      exfalso; apply (rawListNode_not_zero model hPA head tail);
      exact hnil
  end.
  all: subst.
  all: cbn [rawNumeralValue] in *.
  all: repeat match goal with
  | htag : raw_succ ?model ?left = raw_succ ?model ?right |- _ =>
      apply (raw_succ_injective_syntax model hPA) in htag
  end.
  all: try match goal with
  | htag : raw_zero ?model = raw_succ ?model ?value |- _ =>
      exfalso; exact (raw_zero_not_succ_syntax model hPA value htag)
  | htag : raw_succ ?model ?value = raw_zero ?model |- _ =>
      exfalso; apply (raw_zero_not_succ_syntax model hPA value);
      symmetry; exact htag
  end.
  all: split.
  all: try
    (rewrite <- rawQuotedContextCode_standard by exact hPA;
     apply raw_quotedContext_all_bounded; [exact hPA | exact hrank | lia]).
  all: repeat match type of hrest with
  | _ /\ _ => destruct hrest as [? hrest]
  end.
  all: subst.
  all: try match goal with
  | hop : RawCodedFormulaSingleSubstitution ?model
      (rawQuotedTermCode ?model ?replacement)
      (rawQuotedFormulaCode ?model ?phi) ?output
      |- RawFormulaQuantifierBounded ?model ?level ?output =>
      exact (hsubstitution level replacement phi output ltac:(lia) hop)
  end.
  all: match goal with
  | |- RawFormulaQuantifierBounded ?model ?current
      (rawFormulaEqCode ?model
        (rawQuotedTermCode ?model ?left)
        (rawQuotedTermCode ?model ?right)) =>
      change (RawFormulaQuantifierBounded model current
        (rawQuotedFormulaCode model (pEq left right)))
  | |- RawFormulaQuantifierBounded ?model ?current
      (rawFormulaBotCode ?model) =>
      change (RawFormulaQuantifierBounded model current
        (rawQuotedFormulaCode model pBot))
  | |- RawFormulaQuantifierBounded ?model ?current
      (rawFormulaImpCode ?model
        (rawQuotedFormulaCode ?model ?left)
        (rawQuotedFormulaCode ?model ?right)) =>
      change (RawFormulaQuantifierBounded model current
        (rawQuotedFormulaCode model (pImp left right)))
  | |- RawFormulaQuantifierBounded ?model ?current
      (rawFormulaAndCode ?model
        (rawQuotedFormulaCode ?model ?left)
        (rawQuotedFormulaCode ?model ?right)) =>
      change (RawFormulaQuantifierBounded model current
        (rawQuotedFormulaCode model (pAnd left right)))
  | |- RawFormulaQuantifierBounded ?model ?current
      (rawFormulaOrCode ?model
        (rawQuotedFormulaCode ?model ?body)
        (rawFormulaImpCode ?model
          (rawQuotedFormulaCode ?model ?body)
          (rawFormulaBotCode ?model))) =>
      change (RawFormulaQuantifierBounded model current
        (rawQuotedFormulaCode model (pOr body (pImp body pBot))))
  | |- RawFormulaQuantifierBounded ?model ?current
      (rawFormulaOrCode ?model
        (rawQuotedFormulaCode ?model ?left)
        (rawQuotedFormulaCode ?model ?right)) =>
      change (RawFormulaQuantifierBounded model current
        (rawQuotedFormulaCode model (pOr left right)))
  | |- RawFormulaQuantifierBounded ?model ?current
      (rawFormulaAllCode ?model (rawQuotedFormulaCode ?model ?child)) =>
      change (RawFormulaQuantifierBounded model current
        (rawQuotedFormulaCode model (pAll child)))
  | |- RawFormulaQuantifierBounded ?model ?current
      (rawFormulaExCode ?model (rawQuotedFormulaCode ?model ?child)) =>
      change (RawFormulaQuantifierBounded model current
        (rawQuotedFormulaCode model (pEx child)))
  | _ => idtac
  end.
  all: apply raw_quotedFormula_quantifier_bounded;
    [exact hPA | exact hrank | lia].
Qed.

(** ------------------------------------------------------------------
    Exact support for valid, externally bounded standard proof codes. *)

Definition canonicalRawRestrictedProofCodeb
    (level code : nat) : bool :=
  match decodeRawProof code with
  | Some derivation =>
      andb (Nat.eqb (rawProofCode derivation) code)
        (andb (rawProofValidb derivation)
          (rawProofAllBoundedb level derivation))
  | None => false
  end.

Lemma canonicalRawRestrictedProofCodeb_spec : forall level code,
  canonicalRawRestrictedProofCodeb level code = true <->
  exists derivation,
    decodeRawProof code = Some derivation /\
    rawProofCode derivation = code /\
    RawProofValid derivation /\
    rawProofOccurrenceRank derivation <= level.
Proof.
  intros level code. unfold canonicalRawRestrictedProofCodeb.
  destruct (decodeRawProof code) as [derivation |] eqn:hdecode.
  - rewrite !andb_true_iff, Nat.eqb_eq,
      rawProofValidb_spec, rawProofAllBoundedb_spec.
    split.
    + intros [hcode [hvalid hbounded]].
      exists derivation. repeat split; assumption.
    + intros [other [hother [hcode [hvalid hbounded]]]].
      inversion hother. subst other. repeat split; assumption.
  - split; [discriminate |].
    intros [derivation [hdecode' _]]. discriminate.
Qed.

Lemma canonicalRawRestrictedProofCodeb_quoted : forall level derivation,
  RawProofValid derivation ->
  rawProofOccurrenceRank derivation <= level ->
  canonicalRawRestrictedProofCodeb level (rawProofCode derivation) = true.
Proof.
  intros level derivation hvalid hbounded.
  apply canonicalRawRestrictedProofCodeb_spec.
  exists derivation. repeat split; try assumption.
  apply decodeRawProof_rawProofCode.
Qed.

Definition rawStandardRestrictedProofSupportValue
    (M : RawPAModel) (level code : nat) : M :=
  if canonicalRawRestrictedProofCodeb level code
  then rawNumeralValue M 1
  else raw_zero M.

Definition RawStandardRestrictedProofSupportTable (M : RawPAModel)
    (level bound : nat) (supportCode supportStep : M) : Prop :=
  RawCodedAssignmentDefinedThrough M supportCode supportStep
    (rawNumeralValue M bound) /\
  forall code,
    rawLt M code (rawNumeralValue M bound) ->
    (rawProofCodeSupported M supportCode supportStep code <->
     exists derivation,
       code = rawQuotedProofCode M derivation /\
       rawProofCode derivation < bound /\
       RawProofValid derivation /\
       rawProofOccurrenceRank derivation <= level).

Arguments RawStandardRestrictedProofSupportTable
  M level bound supportCode supportStep : clear implicits.

Theorem raw_standardRestrictedProofSupportTable_exists : forall
    (M : RawPAModel), RawPASatisfies M -> forall level bound,
  exists supportCode supportStep,
    RawStandardRestrictedProofSupportTable M level bound
      supportCode supportStep.
Proof.
  intros M hPA level bound.
  destruct (finite_vector_beta_code M hPA bound
    (rawStandardRestrictedProofSupportValue M level)) as
    (supportCode & supportStep & htable).
  exists supportCode, supportStep. split.
  - intros code hcode.
    destruct (raw_lt_numeralValue_cases M hPA code bound hcode) as
      (index & hindex & ->).
    exists (rawStandardRestrictedProofSupportValue M level index).
    exact (htable index hindex).
  - intros code hcode.
    destruct (raw_lt_numeralValue_cases M hPA code bound hcode) as
      (index & hindex & ->).
    specialize (htable index hindex). split.
    + intro hsupported.
      unfold rawProofCodeSupported in hsupported.
      assert (hvalue : rawStandardRestrictedProofSupportValue M level index =
          rawNumeralValue M 1).
      {
        symmetry. exact (raw_codedAssignmentLookup_functional M hPA
          supportCode supportStep (rawNumeralValue M index)
          (rawNumeralValue M 1)
          (rawStandardRestrictedProofSupportValue M level index)
          hsupported htable).
      }
      unfold rawStandardRestrictedProofSupportValue in hvalue.
      destruct (canonicalRawRestrictedProofCodeb level index)
        eqn:hcanonical.
      * apply canonicalRawRestrictedProofCodeb_spec in hcanonical.
        destruct hcanonical as
          (derivation & hdecode & hreencode & hvalid & hbounded).
        exists derivation. repeat split; try assumption.
        -- rewrite rawQuotedProofCode_standard by exact hPA.
           now rewrite hreencode.
        -- now rewrite hreencode.
      * exfalso.
        change (raw_zero M = raw_succ M (raw_zero M)) in hvalue.
        exact (raw_zero_not_succ_syntax M hPA (raw_zero M) hvalue).
    + intros (derivation & hquoted & hderivationBound & hvalid & hbounded).
      rewrite rawQuotedProofCode_standard in hquoted by exact hPA.
      pose proof (rawNumeralValue_injective M hPA
        index (rawProofCode derivation) hquoted) as hindexCode.
      subst index.
      unfold rawProofCodeSupported.
      unfold rawStandardRestrictedProofSupportValue in htable.
      rewrite (canonicalRawRestrictedProofCodeb_quoted
        level derivation hvalid hbounded) in htable.
      exact htable.
Qed.

Corollary raw_standardRestrictedProofSupportTable_for_quotation : forall
    (M : RawPAModel), RawPASatisfies M -> forall level derivation,
  RawProofValid derivation ->
  rawProofOccurrenceRank derivation <= level ->
  exists supportCode supportStep,
    RawStandardRestrictedProofSupportTable M level
      (S (rawProofCode derivation)) supportCode supportStep /\
    rawProofCodeSupported M supportCode supportStep
      (rawQuotedProofCode M derivation).
Proof.
  intros M hPA level derivation hvalid hbounded.
  destruct (raw_standardRestrictedProofSupportTable_exists M hPA
    level (S (rawProofCode derivation))) as
    (supportCode & supportStep & htable).
  exists supportCode, supportStep. split; [exact htable |].
  destruct htable as [_ hexact].
  assert (hrootBelow : rawLt M (rawQuotedProofCode M derivation)
      (rawNumeralValue M (S (rawProofCode derivation)))).
  {
    rewrite rawQuotedProofCode_standard by exact hPA.
    apply raw_lt_numeralValue_of_lt; [exact hPA | lia].
  }
  apply (proj2 (hexact (rawQuotedProofCode M derivation) hrootBelow)).
  exists derivation. repeat split; try assumption; lia.
Qed.

Corollary raw_standardRestrictedProofSupportTable_child : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    level bound supportCode supportStep,
  RawStandardRestrictedProofSupportTable M level bound
    supportCode supportStep ->
  forall derivation child,
  rawProofCode derivation < bound ->
  RawProofValid derivation ->
  rawProofOccurrenceRank derivation <= level ->
  In child (rawChildren derivation) ->
  rawProofCodeSupported M supportCode supportStep
    (rawQuotedProofCode M child).
Proof.
  intros M hPA level bound supportCode supportStep [_ hexact]
    derivation child hderivationBound hvalid hbounded hchild.
  assert (hchildCodeBound : rawProofCode child < bound).
  {
    eapply Nat.lt_trans; [apply rawProofCode_child_lt; exact hchild |].
    exact hderivationBound.
  }
  assert (hchildBelow : rawLt M (rawQuotedProofCode M child)
      (rawNumeralValue M bound)).
  {
    rewrite rawQuotedProofCode_standard by exact hPA.
    apply raw_lt_numeralValue_of_lt; assumption.
  }
  apply (proj2 (hexact (rawQuotedProofCode M child) hchildBelow)).
  exists child. repeat split; try assumption.
  - exact (rawProofValid_child derivation child hvalid hchild).
  - eapply Nat.le_trans.
    + exact (rawProofOccurrenceRank_child_le derivation child hchild).
    + exact hbounded.
Qed.

(** The syntax-row quotation proof only needs support of genuine children;
    it does not depend on how the surrounding table selected its live rows. *)
Lemma raw_quotedProof_syntax_step_of_children : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    supportCode supportStep derivation,
  (forall child,
    In child (rawChildren derivation) ->
    rawProofCodeSupported M supportCode supportStep
      (rawQuotedProofCode M child)) ->
  RawProofSyntaxStep M (rawQuotedProofCode M derivation)
    supportCode supportStep.
Proof.
  intros M hPA supportCode supportStep derivation hchildren.
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
        exact (hchildren child hchild).
      * exact (proj1 (@Forall_forall M
          (fun child => rawLt M child (rawQuotedProofCode M derivation))
          children) hcaseBelow advertisedChild hadvertised).
Qed.

Lemma raw_quotedProof_restricted_node : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawStandardFormulaRankQuotation M ->
  RawStandardSingleSubstitutionBounded M ->
  forall level bound supportCode supportStep derivation,
  RawStandardRestrictedProofSupportTable M level bound
    supportCode supportStep ->
  rawProofCode derivation < bound ->
  RawProofValid derivation ->
  rawProofOccurrenceRank derivation <= level ->
  RawRestrictedProofNode M level (rawQuotedProofCode M derivation)
    supportCode supportStep.
Proof.
  intros M hPA hrank hsubstitution level bound supportCode supportStep
    derivation htable hcodeBound hvalid hbounded.
  split.
  - apply raw_quotedProof_syntax_step_of_children; [exact hPA |].
    intros child hchild.
    exact (raw_standardRestrictedProofSupportTable_child M hPA
      level bound supportCode supportStep htable
      derivation child hcodeBound hvalid hbounded hchild).
  - split.
    + exists (rawQuotedContextCode M (rawContext derivation)),
        (rawQuotedFormulaCode M (rawConclusion derivation)).
      exact (raw_quotedProof_rule_valid M hPA derivation hvalid).
    + split.
      * exact (raw_quotedProof_constructor_occurrences_bounded
          M hPA hrank level derivation hbounded).
      * exact (raw_quotedProof_endpoint_occurrences_bounded
          M hPA hrank hsubstitution level derivation hbounded).
Qed.

Theorem raw_restrictedProof_of_quoted_rawProof_of_formula_properties : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawStandardFormulaRankQuotation M ->
  RawStandardSingleSubstitutionBounded M ->
  forall level derivation,
  RawProofValid derivation ->
  rawProofOccurrenceRank derivation <= level ->
  RawRestrictedProof M level (rawQuotedProofCode M derivation).
Proof.
  intros M hPA hrank hsubstitution level derivation hvalid hbounded.
  destruct (raw_standardRestrictedProofSupportTable_for_quotation
    M hPA level derivation hvalid hbounded) as
    (supportCode & supportStep & htable & hroot).
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
    destruct (proj1 (hexact code hcodeBound) hsupported) as
      (row & hrow & hrowCodeBound & hrowValid & hrowBounded).
    subst code.
    apply (raw_quotedProof_restricted_node M hPA hrank hsubstitution
      level (S (rawProofCode derivation)) supportCode supportStep row).
    + split; assumption.
    + exact hrowCodeBound.
    + exact hrowValid.
    + exact hrowBounded.
Qed.

(** The formula-level properties above are theorems of every raw PA model,
    so the public raw-proof quotation result has no residual premise. *)
Theorem raw_restrictedProof_of_quoted_rawProof : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall level derivation,
  RawProofValid derivation ->
  rawProofOccurrenceRank derivation <= level ->
  RawRestrictedProof M level (rawQuotedProofCode M derivation).
Proof.
  intros M hPA level derivation hvalid hbounded.
  exact (raw_restrictedProof_of_quoted_rawProof_of_formula_properties
    M hPA (raw_standardFormulaRankQuotation M hPA)
    (raw_standardSingleSubstitutionBounded M hPA)
    level derivation hvalid hbounded).
Qed.

(** Full discharge of the quotation-adequacy seam exported by
    [RawCodedRestrictedProofTraversal]. *)
Theorem raw_restrictedProvTree_quotation_adequacy : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawRestrictedProvTreeQuotationAdequacy M.
Proof.
  intros M hPA.
  unfold RawRestrictedProvTreeQuotationAdequacy.
  intros level G phi derivation hbounded.
  apply (raw_restrictedProof_of_quoted_rawProof M hPA
    level (rawOfProvTree derivation)).
  - apply RawProofValid_rawOfProvTree.
  - rewrite rawProofOccurrenceRank_rawOfProvTree. exact hbounded.
Qed.

Corollary raw_restrictedProof_of_quoted_provTree : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall level G phi (derivation : ProvTree G phi),
  ProofAllBounded level derivation ->
  RawRestrictedProof M level
    (rawQuotedProofCode M (rawOfProvTree derivation)).
Proof.
  intros M hPA level G phi derivation hbounded.
  exact (raw_restrictedProvTree_quotation_adequacy
    M hPA level G phi derivation hbounded).
Qed.

End PABoundedRawCodedRestrictedProofStandardAdequacy.
