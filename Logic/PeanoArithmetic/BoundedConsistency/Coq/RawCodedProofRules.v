(**
  Local validity of every raw natural-deduction constructor.

  Proof-syntax traversal says which recursive proof codes occur and proves
  that they descend.  This file adds the orthogonal local side conditions:
  assumption membership, every premise context/conclusion endpoint,
  context shifting under binders, and capture-avoiding substitution.

  The relation is nonrecursive.  A later global certificate requires it at
  every supported proof code, while the existing proof traversal closes all
  recursive children.  Separating these concerns keeps the exact raw-model
  semantics readable and prevents a host-language decoder from entering the
  nonstandard argument.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedContextLists RawCodedContextShift
  RawCodedProofConstructors RawCodedFormulaOperations
  RawCodedProofEndpoints.

Import ListNotations.

Module PABoundedRawCodedProofRules.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedProofEndpoints.

Fixpoint proofRuleConjunction (cases : list formula) : formula :=
  match cases with
  | [] => pEq tZero tZero
  | head :: tail => pAnd head (proofRuleConjunction tail)
  end.

(** The eight exposed fields are context, three generic formula/term slots,
    one term slot, and three recursive children.  Unused slots are valuable:
    they name intermediate formula and shifted-context codes without changing
    the canonical proof-code format. *)
Definition proofRuleValidCasesTermAt
    (code context conclusion a b c t child1 child2 child3 : term)
    : formula :=
  proofFormulaDisjunction
    [proofRuleConjunction
      [pEq code (proofAssCodeTerm context a);
       pEq conclusion a;
       contextListMemberTermAt context a];
     proofRuleConjunction
      [pEq code (proofImpICodeTerm context a b child1);
       formulaImpCodeTermAt conclusion a b;
       proofEndpointTermAt child1 (nodeTerm a context) b];
     proofRuleConjunction
      [pEq code (proofImpECodeTerm context a b child1 child2);
       pEq conclusion b;
       formulaImpCodeTermAt c a b;
       proofEndpointTermAt child1 context c;
       proofEndpointTermAt child2 context a];
     proofRuleConjunction
      [pEq code (proofBotECodeTerm context a child1);
       pEq conclusion a;
       formulaBotCodeTermAt b;
       proofEndpointTermAt child1 context b];
     proofRuleConjunction
      [pEq code (proofLemCodeTerm context a);
       formulaBotCodeTermAt c;
       formulaImpCodeTermAt b a c;
       formulaOrCodeTermAt conclusion a b];
     proofRuleConjunction
      [pEq code (proofAndICodeTerm context a b child1 child2);
       formulaAndCodeTermAt conclusion a b;
       proofEndpointTermAt child1 context a;
       proofEndpointTermAt child2 context b];
     proofRuleConjunction
      [pEq code (proofAndE1CodeTerm context a b child1);
       pEq conclusion a;
       formulaAndCodeTermAt c a b;
       proofEndpointTermAt child1 context c];
     proofRuleConjunction
      [pEq code (proofAndE2CodeTerm context a b child1);
       pEq conclusion b;
       formulaAndCodeTermAt c a b;
       proofEndpointTermAt child1 context c];
     proofRuleConjunction
      [pEq code (proofOrI1CodeTerm context a b child1);
       formulaOrCodeTermAt conclusion a b;
       proofEndpointTermAt child1 context a];
     proofRuleConjunction
      [pEq code (proofOrI2CodeTerm context a b child1);
       formulaOrCodeTermAt conclusion a b;
       proofEndpointTermAt child1 context b];
     proofRuleConjunction
      [pEq code (proofOrECodeTerm
        context a b c child1 child2 child3);
       pEq conclusion c;
       formulaOrCodeTermAt t a b;
       proofEndpointTermAt child1 context t;
       proofEndpointTermAt child2 (nodeTerm a context) c;
       proofEndpointTermAt child3 (nodeTerm b context) c];
     proofRuleConjunction
      [pEq code (proofAllICodeTerm context a child1);
       formulaAllCodeTermAt conclusion a;
       contextShiftTermAt context b;
       proofEndpointTermAt child1 b a];
     proofRuleConjunction
      [pEq code (proofAllECodeTerm context a t child1);
       codedFormulaSingleSubstitutionTermAt t a conclusion;
       formulaAllCodeTermAt b a;
       proofEndpointTermAt child1 context b];
     proofRuleConjunction
      [pEq code (proofExICodeTerm context a t child1);
       formulaExCodeTermAt conclusion a;
       codedFormulaSingleSubstitutionTermAt t a b;
       proofEndpointTermAt child1 context b];
     proofRuleConjunction
      [pEq code (proofExECodeTerm context a b child1 child2);
       pEq conclusion b;
       formulaExCodeTermAt child3 a;
       proofEndpointTermAt child1 context child3;
       contextShiftTermAt context c;
       codedFormulaShiftTermAt tZero (Term.numeral 1) b t;
       proofEndpointTermAt child2 (nodeTerm a c) t];
     proofRuleConjunction
      [pEq code (proofEqReflCodeTerm context t);
       formulaEqCodeTermAt conclusion t t];
     proofRuleConjunction
      [pEq code (proofEqElimCodeTerm
        context a b c child1 child2);
       codedFormulaSingleSubstitutionTermAt b c conclusion;
       formulaEqCodeTermAt t a b;
       proofEndpointTermAt child1 context t;
       codedFormulaSingleSubstitutionTermAt a c child3;
       proofEndpointTermAt child2 context child3]].

Definition RawProofRuleValidCases (M : RawPAModel)
    (code context conclusion a b c t child1 child2 child3 : M) : Prop :=
  (code = rawListCode M [rawNumeralValue M 0; context; a] /\
    conclusion = a /\
    RawContextListMember M context a) \/
  (code = rawListCode M
      [rawNumeralValue M 1; context; a; b; child1] /\
    conclusion = rawFormulaImpCode M a b /\
    RawProofEndpoint M child1 (rawListNode M a context) b) \/
  (code = rawListCode M
      [rawNumeralValue M 2; context; a; b; child1; child2] /\
    conclusion = b /\
    c = rawFormulaImpCode M a b /\
    RawProofEndpoint M child1 context c /\
    RawProofEndpoint M child2 context a) \/
  (code = rawListCode M
      [rawNumeralValue M 3; context; a; child1] /\
    conclusion = a /\
    b = rawFormulaBotCode M /\
    RawProofEndpoint M child1 context b) \/
  (code = rawListCode M [rawNumeralValue M 4; context; a] /\
    c = rawFormulaBotCode M /\
    b = rawFormulaImpCode M a c /\
    conclusion = rawFormulaOrCode M a b) \/
  (code = rawListCode M
      [rawNumeralValue M 5; context; a; b; child1; child2] /\
    conclusion = rawFormulaAndCode M a b /\
    RawProofEndpoint M child1 context a /\
    RawProofEndpoint M child2 context b) \/
  (code = rawListCode M
      [rawNumeralValue M 6; context; a; b; child1] /\
    conclusion = a /\
    c = rawFormulaAndCode M a b /\
    RawProofEndpoint M child1 context c) \/
  (code = rawListCode M
      [rawNumeralValue M 7; context; a; b; child1] /\
    conclusion = b /\
    c = rawFormulaAndCode M a b /\
    RawProofEndpoint M child1 context c) \/
  (code = rawListCode M
      [rawNumeralValue M 8; context; a; b; child1] /\
    conclusion = rawFormulaOrCode M a b /\
    RawProofEndpoint M child1 context a) \/
  (code = rawListCode M
      [rawNumeralValue M 9; context; a; b; child1] /\
    conclusion = rawFormulaOrCode M a b /\
    RawProofEndpoint M child1 context b) \/
  (code = rawListCode M
      [rawNumeralValue M 10; context; a; b; c;
        child1; child2; child3] /\
    conclusion = c /\
    t = rawFormulaOrCode M a b /\
    RawProofEndpoint M child1 context t /\
    RawProofEndpoint M child2 (rawListNode M a context) c /\
    RawProofEndpoint M child3 (rawListNode M b context) c) \/
  (code = rawListCode M
      [rawNumeralValue M 11; context; a; child1] /\
    conclusion = rawFormulaAllCode M a /\
    RawContextShift M context b /\
    RawProofEndpoint M child1 b a) \/
  (code = rawListCode M
      [rawNumeralValue M 12; context; a; t; child1] /\
    RawCodedFormulaSingleSubstitution M t a conclusion /\
    b = rawFormulaAllCode M a /\
    RawProofEndpoint M child1 context b) \/
  (code = rawListCode M
      [rawNumeralValue M 13; context; a; t; child1] /\
    conclusion = rawFormulaExCode M a /\
    RawCodedFormulaSingleSubstitution M t a b /\
    RawProofEndpoint M child1 context b) \/
  (code = rawListCode M
      [rawNumeralValue M 14; context; a; b; child1; child2] /\
    conclusion = b /\
    child3 = rawFormulaExCode M a /\
    RawProofEndpoint M child1 context child3 /\
    RawContextShift M context c /\
    RawCodedFormulaShift M
      (raw_zero M) (rawNumeralValue M 1) b t /\
    RawProofEndpoint M child2 (rawListNode M a c) t) \/
  (code = rawListCode M
      [rawNumeralValue M 15; context; t] /\
    conclusion = rawFormulaEqCode M t t) \/
  (code = rawListCode M
      [rawNumeralValue M 16; context; a; b; c; child1; child2] /\
    RawCodedFormulaSingleSubstitution M b c conclusion /\
    t = rawFormulaEqCode M a b /\
    RawProofEndpoint M child1 context t /\
    RawCodedFormulaSingleSubstitution M a c child3 /\
    RawProofEndpoint M child2 context child3).

Arguments RawProofRuleValidCases
  M code context conclusion a b c t child1 child2 child3
  : clear implicits.

Lemma raw_sat_proofRuleValidCasesTermAt_iff : forall
    (M : RawPAModel) e
    code context conclusion a b c t child1 child2 child3,
  raw_formula_sat M e
    (proofRuleValidCasesTermAt
      code context conclusion a b c t child1 child2 child3) <->
  RawProofRuleValidCases M
    (raw_term_eval M e code) (raw_term_eval M e context)
    (raw_term_eval M e conclusion)
    (raw_term_eval M e a) (raw_term_eval M e b)
    (raw_term_eval M e c) (raw_term_eval M e t)
    (raw_term_eval M e child1) (raw_term_eval M e child2)
    (raw_term_eval M e child3).
Proof.
  intros. unfold proofRuleValidCasesTermAt, RawProofRuleValidCases,
    proofAssCodeTerm, proofImpICodeTerm, proofImpECodeTerm,
    proofBotECodeTerm, proofLemCodeTerm, proofAndICodeTerm,
    proofAndE1CodeTerm, proofAndE2CodeTerm,
    proofOrI1CodeTerm, proofOrI2CodeTerm, proofOrECodeTerm,
    proofAllICodeTerm, proofAllECodeTerm, proofExICodeTerm,
    proofExECodeTerm, proofEqReflCodeTerm, proofEqElimCodeTerm.
  cbn [proofFormulaDisjunction proofRuleConjunction raw_formula_sat].
  repeat rewrite raw_eval_proofCodeFieldsTerm.
  repeat rewrite raw_sat_formulaBotCodeTermAt_iff.
  repeat rewrite raw_sat_formulaImpCodeTermAt_iff.
  repeat rewrite raw_sat_formulaAndCodeTermAt_iff.
  repeat rewrite raw_sat_formulaOrCodeTermAt_iff.
  repeat rewrite raw_sat_formulaAllCodeTermAt_iff.
  repeat rewrite raw_sat_formulaExCodeTermAt_iff.
  repeat rewrite raw_sat_formulaEqCodeTermAt_iff.
  repeat rewrite raw_sat_codedFormulaSingleSubstitutionTermAt_iff.
  repeat rewrite raw_sat_codedFormulaShiftTermAt_iff.
  repeat rewrite raw_sat_contextListMemberTermAt_iff.
  repeat rewrite raw_sat_contextShiftTermAt_iff.
  repeat rewrite raw_sat_proofEndpointTermAt_iff.
  repeat rewrite raw_eval_nodeTerm.
  repeat rewrite raw_term_eval_numeral.
  cbn [map]. tauto.
Qed.

Definition proofRuleValidTermAt
    (code context conclusion : term) : formula :=
  proofEndpointEx8
    (pAnd
      (pEq (tVar 7) (liftTerm 8 context))
      (proofRuleValidCasesTermAt
        (liftTerm 8 code) (tVar 7) (liftTerm 8 conclusion)
        (tVar 6) (tVar 5) (tVar 4) (tVar 3)
        (tVar 2) (tVar 1) (tVar 0))).

Definition RawProofRuleValid (M : RawPAModel)
    (code context conclusion : M) : Prop :=
  exists rowContext a b c t child1 child2 child3 : M,
    rowContext = context /\
    RawProofRuleValidCases M
      code rowContext conclusion a b c t child1 child2 child3.

Arguments RawProofRuleValid M code context conclusion : clear implicits.

Lemma raw_sat_proofRuleValidTermAt_iff : forall
    (M : RawPAModel) e code context conclusion,
  raw_formula_sat M e
    (proofRuleValidTermAt code context conclusion) <->
  RawProofRuleValid M
    (raw_term_eval M e code) (raw_term_eval M e context)
    (raw_term_eval M e conclusion).
Proof.
  intros M e code context conclusion.
  unfold proofRuleValidTermAt, proofEndpointEx8, RawProofRuleValid.
  cbn [raw_formula_sat]. split.
  - intros (rowContext & a & b & c & t & child1 & child2 & child3 &
      [hcontext h]).
    exists rowContext, a, b, c, t, child1, child2, child3.
    split.
    + rewrite raw_proofEndpoint_eval_liftTerm_eight in hcontext.
      cbn [raw_term_eval scons] in hcontext. exact hcontext.
    + apply (proj1 (raw_sat_proofRuleValidCasesTermAt_iff M
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
    + apply (proj2 (raw_sat_proofRuleValidCasesTermAt_iff M
        (scons M child3 (scons M child2 (scons M child1
          (scons M t (scons M c (scons M b (scons M a
            (scons M rowContext e))))))))
        (liftTerm 8 code) (tVar 7) (liftTerm 8 conclusion)
        (tVar 6) (tVar 5) (tVar 4) (tVar 3)
        (tVar 2) (tVar 1) (tVar 0))).
      repeat rewrite raw_proofEndpoint_eval_liftTerm_eight.
      cbn [raw_term_eval scons]. exact h.
Qed.

Theorem raw_proofRuleValid_endpoint : forall
    (M : RawPAModel) code context conclusion,
  RawProofRuleValid M code context conclusion ->
  RawProofEndpoint M code context conclusion.
Proof.
  intros M code context conclusion
    (rowContext & a & b & c & t & child1 & child2 & child3 &
      hcontext & hvalid).
  exists rowContext, a, b, c, t, child1, child2, child3.
  split; [exact hcontext |].
  unfold RawProofRuleValidCases in hvalid.
  unfold RawProofEndpointCases.
  tauto.
Qed.

End PABoundedRawCodedProofRules.
