(**
  Context and conclusion endpoints of arbitrary raw proof codes.

  A raw proof constructor stores its context and its rule parameters, but its
  conclusion is implicit in the constructor.  The graph below exposes that
  conclusion by an ordinary PA formula.  Most cases use only transparent
  polynomial formula-code constructors.  Universal elimination and equality
  elimination additionally use the arithmetized capture-avoiding single-
  substitution graph; no decoder is applied to a raw carrier element.

  This module is deliberately constructor-local.  It does not assert that a
  node is a valid inference or that its children have matching endpoints.
  Those conditions are assembled separately, while this small relation can
  already be reused for every child endpoint comparison.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedProofConstructors
  RawCodedFormulaOperations.

Import ListNotations.

Module PABoundedRawCodedProofEndpoints.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedFormulaOperations.

Definition proofEndpointAnd3 (a b c : formula) : formula :=
  pAnd a (pAnd b c).

Definition proofEndpointAnd4 (a b c d : formula) : formula :=
  pAnd a (pAnd b (pAnd c d)).

(** The eight fields use the same convention as the proof-syntax traversal:
    context, [a], [b], [c], term [t], and three recursive children. *)
Definition proofEndpointCasesTermAt
    (code context conclusion a b c t child1 child2 child3 : term)
    : formula :=
  proofFormulaDisjunction
    [pAnd
      (pEq code (proofAssCodeTerm context a))
      (pEq conclusion a);
     pAnd
      (pEq code (proofImpICodeTerm context a b child1))
      (formulaImpCodeTermAt conclusion a b);
     pAnd
      (pEq code (proofImpECodeTerm context a b child1 child2))
      (pEq conclusion b);
     pAnd
      (pEq code (proofBotECodeTerm context a child1))
      (pEq conclusion a);
     proofEndpointAnd4
      (pEq code (proofLemCodeTerm context a))
      (formulaBotCodeTermAt c)
      (formulaImpCodeTermAt b a c)
      (formulaOrCodeTermAt conclusion a b);
     pAnd
      (pEq code (proofAndICodeTerm context a b child1 child2))
      (formulaAndCodeTermAt conclusion a b);
     pAnd
      (pEq code (proofAndE1CodeTerm context a b child1))
      (pEq conclusion a);
     pAnd
      (pEq code (proofAndE2CodeTerm context a b child1))
      (pEq conclusion b);
     pAnd
      (pEq code (proofOrI1CodeTerm context a b child1))
      (formulaOrCodeTermAt conclusion a b);
     pAnd
      (pEq code (proofOrI2CodeTerm context a b child1))
      (formulaOrCodeTermAt conclusion a b);
     pAnd
      (pEq code (proofOrECodeTerm
        context a b c child1 child2 child3))
      (pEq conclusion c);
     pAnd
      (pEq code (proofAllICodeTerm context a child1))
      (formulaAllCodeTermAt conclusion a);
     pAnd
      (pEq code (proofAllECodeTerm context a t child1))
      (codedFormulaSingleSubstitutionTermAt t a conclusion);
     pAnd
      (pEq code (proofExICodeTerm context a t child1))
      (formulaExCodeTermAt conclusion a);
     pAnd
      (pEq code (proofExECodeTerm context a b child1 child2))
      (pEq conclusion b);
     pAnd
      (pEq code (proofEqReflCodeTerm context t))
      (formulaEqCodeTermAt conclusion t t);
     pAnd
      (pEq code (proofEqElimCodeTerm
        context a b c child1 child2))
      (codedFormulaSingleSubstitutionTermAt b c conclusion)].

Definition RawProofEndpointCases (M : RawPAModel)
    (code context conclusion a b c t child1 child2 child3 : M) : Prop :=
  (code = rawListCode M [rawNumeralValue M 0; context; a] /\
    conclusion = a) \/
  (code = rawListCode M
      [rawNumeralValue M 1; context; a; b; child1] /\
    conclusion = rawFormulaImpCode M a b) \/
  (code = rawListCode M
      [rawNumeralValue M 2; context; a; b; child1; child2] /\
    conclusion = b) \/
  (code = rawListCode M
      [rawNumeralValue M 3; context; a; child1] /\
    conclusion = a) \/
  (code = rawListCode M [rawNumeralValue M 4; context; a] /\
    c = rawFormulaBotCode M /\
    b = rawFormulaImpCode M a c /\
    conclusion = rawFormulaOrCode M a b) \/
  (code = rawListCode M
      [rawNumeralValue M 5; context; a; b; child1; child2] /\
    conclusion = rawFormulaAndCode M a b) \/
  (code = rawListCode M
      [rawNumeralValue M 6; context; a; b; child1] /\
    conclusion = a) \/
  (code = rawListCode M
      [rawNumeralValue M 7; context; a; b; child1] /\
    conclusion = b) \/
  (code = rawListCode M
      [rawNumeralValue M 8; context; a; b; child1] /\
    conclusion = rawFormulaOrCode M a b) \/
  (code = rawListCode M
      [rawNumeralValue M 9; context; a; b; child1] /\
    conclusion = rawFormulaOrCode M a b) \/
  (code = rawListCode M
      [rawNumeralValue M 10; context; a; b; c;
        child1; child2; child3] /\
    conclusion = c) \/
  (code = rawListCode M
      [rawNumeralValue M 11; context; a; child1] /\
    conclusion = rawFormulaAllCode M a) \/
  (code = rawListCode M
      [rawNumeralValue M 12; context; a; t; child1] /\
    RawCodedFormulaSingleSubstitution M t a conclusion) \/
  (code = rawListCode M
      [rawNumeralValue M 13; context; a; t; child1] /\
    conclusion = rawFormulaExCode M a) \/
  (code = rawListCode M
      [rawNumeralValue M 14; context; a; b; child1; child2] /\
    conclusion = b) \/
  (code = rawListCode M
      [rawNumeralValue M 15; context; t] /\
    conclusion = rawFormulaEqCode M t t) \/
  (code = rawListCode M
      [rawNumeralValue M 16; context; a; b; c; child1; child2] /\
    RawCodedFormulaSingleSubstitution M b c conclusion).

Arguments RawProofEndpointCases
  M code context conclusion a b c t child1 child2 child3
  : clear implicits.

Lemma raw_sat_proofEndpointCasesTermAt_iff : forall
    (M : RawPAModel) e
    code context conclusion a b c t child1 child2 child3,
  raw_formula_sat M e
    (proofEndpointCasesTermAt
      code context conclusion a b c t child1 child2 child3) <->
  RawProofEndpointCases M
    (raw_term_eval M e code) (raw_term_eval M e context)
    (raw_term_eval M e conclusion)
    (raw_term_eval M e a) (raw_term_eval M e b)
    (raw_term_eval M e c) (raw_term_eval M e t)
    (raw_term_eval M e child1) (raw_term_eval M e child2)
    (raw_term_eval M e child3).
Proof.
  intros. unfold proofEndpointCasesTermAt, RawProofEndpointCases,
    proofEndpointAnd3, proofEndpointAnd4,
    proofAssCodeTerm, proofImpICodeTerm, proofImpECodeTerm,
    proofBotECodeTerm, proofLemCodeTerm, proofAndICodeTerm,
    proofAndE1CodeTerm, proofAndE2CodeTerm,
    proofOrI1CodeTerm, proofOrI2CodeTerm, proofOrECodeTerm,
    proofAllICodeTerm, proofAllECodeTerm, proofExICodeTerm,
    proofExECodeTerm, proofEqReflCodeTerm, proofEqElimCodeTerm.
  cbn [proofFormulaDisjunction raw_formula_sat].
  repeat rewrite raw_eval_proofCodeFieldsTerm.
  repeat rewrite raw_sat_formulaBotCodeTermAt_iff.
  repeat rewrite raw_sat_formulaImpCodeTermAt_iff.
  repeat rewrite raw_sat_formulaAndCodeTermAt_iff.
  repeat rewrite raw_sat_formulaOrCodeTermAt_iff.
  repeat rewrite raw_sat_formulaAllCodeTermAt_iff.
  repeat rewrite raw_sat_formulaExCodeTermAt_iff.
  repeat rewrite raw_sat_formulaEqCodeTermAt_iff.
  repeat rewrite raw_sat_codedFormulaSingleSubstitutionTermAt_iff.
  repeat rewrite raw_term_eval_numeral.
  cbn [map]. tauto.
Qed.

Definition proofEndpointEx8 (body : formula) : formula :=
  pEx (pEx (pEx (pEx (pEx (pEx (pEx (pEx body))))))).

Definition proofEndpointTermAt
    (code context conclusion : term) : formula :=
  proofEndpointEx8
    (pAnd
      (pEq (tVar 7) (liftTerm 8 context))
      (proofEndpointCasesTermAt
        (liftTerm 8 code) (tVar 7) (liftTerm 8 conclusion)
        (tVar 6) (tVar 5) (tVar 4) (tVar 3)
        (tVar 2) (tVar 1) (tVar 0))).

Definition RawProofEndpoint (M : RawPAModel)
    (code context conclusion : M) : Prop :=
  exists rowContext a b c t child1 child2 child3 : M,
    rowContext = context /\
    RawProofEndpointCases M
      code rowContext conclusion a b c t child1 child2 child3.

Arguments RawProofEndpoint M code context conclusion : clear implicits.

Lemma raw_proofEndpoint_eval_liftTerm_eight : forall
    (M : RawPAModel) a b c d f g h i (e : nat -> M) t,
  raw_term_eval M
    (scons M a (scons M b (scons M c (scons M d
      (scons M f (scons M g (scons M h (scons M i e))))))))
    (liftTerm 8 t) = raw_term_eval M e t.
Proof.
  intros M a b c d f g h i e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro j.
  replace (j + 8) with (S (S (S (S (S (S (S (S j)))))))) by lia.
  reflexivity.
Qed.

Lemma raw_sat_proofEndpointTermAt_iff : forall
    (M : RawPAModel) e code context conclusion,
  raw_formula_sat M e
    (proofEndpointTermAt code context conclusion) <->
  RawProofEndpoint M
    (raw_term_eval M e code) (raw_term_eval M e context)
    (raw_term_eval M e conclusion).
Proof.
  intros M e code context conclusion.
  unfold proofEndpointTermAt, proofEndpointEx8, RawProofEndpoint.
  cbn [raw_formula_sat]. split.
  - intros (rowContext & a & b & c & t & child1 & child2 & child3 &
      [hcontext h]).
    exists rowContext, a, b, c, t, child1, child2, child3.
    split.
    + rewrite raw_proofEndpoint_eval_liftTerm_eight in hcontext.
      cbn [raw_term_eval scons] in hcontext. exact hcontext.
    +
    apply (proj1 (raw_sat_proofEndpointCasesTermAt_iff M
      (scons M child3 (scons M child2 (scons M child1
        (scons M t (scons M c (scons M b (scons M a
          (scons M rowContext e))))))))
      (liftTerm 8 code) (tVar 7) (liftTerm 8 conclusion)
      (tVar 6) (tVar 5) (tVar 4) (tVar 3)
      (tVar 2) (tVar 1) (tVar 0))) in h.
    repeat rewrite raw_proofEndpoint_eval_liftTerm_eight in h.
    cbn [raw_term_eval scons] in h. exact h.
  - intros (rowContext & a & b & c & t & child1 & child2 & child3 &
      [hcontext h]).
    exists rowContext, a, b, c, t, child1, child2, child3.
    split.
    + rewrite raw_proofEndpoint_eval_liftTerm_eight.
      cbn [raw_term_eval scons]. exact hcontext.
    +
    apply (proj2 (raw_sat_proofEndpointCasesTermAt_iff M
      (scons M child3 (scons M child2 (scons M child1
        (scons M t (scons M c (scons M b (scons M a
          (scons M rowContext e))))))))
      (liftTerm 8 code) (tVar 7) (liftTerm 8 conclusion)
      (tVar 6) (tVar 5) (tVar 4) (tVar 3)
      (tVar 2) (tVar 1) (tVar 0))).
    repeat rewrite raw_proofEndpoint_eval_liftTerm_eight.
    cbn [raw_term_eval scons]. exact h.
Qed.

(** The endpoint relation always exposes one of the same seventeen proof
    constructor occurrences used by the syntax traversal. *)
Theorem raw_proofEndpoint_constructor : forall
    (M : RawPAModel) code context conclusion,
  RawProofEndpoint M code context conclusion ->
  exists a b c t child1 child2 child3 : M,
    RawProofConstructorCode M
      code context a b c t child1 child2 child3.
Proof.
  intros M code context conclusion
    (rowContext & a & b & c & t & child1 & child2 & child3 &
      hcontext & h).
  subst rowContext.
  exists a, b, c, t, child1, child2, child3.
  unfold RawProofEndpointCases in h.
  unfold RawProofConstructorCode.
  tauto.
Qed.

End PABoundedRawCodedProofEndpoints.
