(**
  Global validity and occurrence bounds for arbitrary coded PA proofs.

  A carrier element of a nonstandard PA model cannot be decoded into the
  meta-theoretic [RawProof] datatype.  The certificate below therefore stays
  entirely inside raw arithmetic.  A beta support table marks the proof
  nodes.  Every marked node has

  - the existing syntax step, which closes every recursive constructor
    occurrence under the same support table and proves strict descent;
  - at least one context/conclusion endpoint accepted by
    [RawProofRuleValid], the arithmetized natural-deduction rules;
  - bounds for every matching constructor occurrence (not merely one chosen
    existential decomposition); and
  - bounds for every matching endpoint occurrence.

  The universal wording matters in a nonstandard model.  Until constructor
  and endpoint uniqueness have separately been proved, two arithmetic
  payload tuples might denote the same carrier element.  Requiring every
  matching occurrence to be bounded prevents an existential witness from
  hiding an unbounded alternative occurrence.

  The constructor table is deliberately aligned with [proofOccurrenceRank].
  It bounds the displayed context and conclusion and precisely the stored
  formula parameters.  In particular, witnesses in all/ex rules and the two
  source/target fields of equality elimination are term codes and are never
  passed to [formulaQuantifierBoundedTermAt].
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  BoundedConsistency CodedProof RawModelCompleteness RawCodedAssignment
  PolynomialPairInjectivity
  RawCodedSyntaxConstructors RawCodedProofConstructors
  RawCodedProofDescent RawCodedProofTraversal RawCodedProofEndpoints
  RawCodedProofRules RawCodedContextBounds.

Import ListNotations.

Module PABoundedRawCodedRestrictedProofTraversal.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedProof.
Import PABoundedConsistency.
Import PABoundedRawModelCompleteness.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedProofTraversal.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedContextBounds.

(** ------------------------------------------------------------------
    Small formula combinators and binder evaluation. *)

Definition restrictedProofAnd3 (first second third : formula) : formula :=
  pAnd first (pAnd second third).

Definition restrictedProofAnd4
    (first second third fourth : formula) : formula :=
  pAnd first (pAnd second (pAnd third fourth)).

Definition restrictedProofEx2 (body : formula) : formula :=
  pEx (pEx body).

Definition restrictedProofAll2 (body : formula) : formula :=
  pAll (pAll body).

Definition restrictedProofAll8 (body : formula) : formula :=
  pAll (pAll (pAll (pAll (pAll (pAll (pAll (pAll body))))))).

Lemma raw_restrictedProof_eval_liftTerm_one : forall
    (M : RawPAModel) value (e : nat -> M) t,
  raw_term_eval M (scons M value e) (liftTerm 1 t) =
  raw_term_eval M e t.
Proof.
  intros M value e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro i.
  replace (i + 1) with (S i) by lia. reflexivity.
Qed.

Lemma raw_restrictedProof_eval_liftTerm_two : forall
    (M : RawPAModel) first second (e : nat -> M) t,
  raw_term_eval M (scons M first (scons M second e)) (liftTerm 2 t) =
  raw_term_eval M e t.
Proof.
  intros M first second e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro i.
  replace (i + 2) with (S (S i)) by lia. reflexivity.
Qed.

Lemma raw_restrictedProof_eval_liftTerm_eight : forall
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

(** ------------------------------------------------------------------
    Bounding a finite list of formula-code fields. *)

Fixpoint proofFormulaFieldsBoundedTermAt
    (level : nat) (fields : list term) : formula :=
  match fields with
  | [] => pEq tZero tZero
  | field :: tail =>
      pAnd
        (formulaQuantifierBoundedTermAt level field)
        (proofFormulaFieldsBoundedTermAt level tail)
  end.

Lemma raw_sat_proofFormulaFieldsBoundedTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M) level fields,
  raw_formula_sat M e
    (proofFormulaFieldsBoundedTermAt level fields) <->
  Forall
    (fun field => RawFormulaQuantifierBounded M level
      (raw_term_eval M e field))
    fields.
Proof.
  intros M e level fields. induction fields as [|field tail IH].
  - cbn [proofFormulaFieldsBoundedTermAt raw_formula_sat].
    split; intro; [constructor | reflexivity].
  - cbn [proofFormulaFieldsBoundedTermAt raw_formula_sat].
    rewrite raw_sat_formulaQuantifierBoundedTermAt_iff, IH.
    split.
    + intros [hfield htail]. constructor; assumption.
    + intros hall. inversion hall; subst. split; assumption.
Qed.

(** Each entry contains the arithmetic constructor term and exactly the
    formula-valued fields counted at that constructor by
    [proofOccurrenceRank].  Empty fields for equality reflexivity are
    intentional. *)
Definition proofOccurrenceCasesTerms
    (context a b c t child1 child2 child3 : term)
    : list (term * list term) :=
  [(proofAssCodeTerm context a, [a]);
   (proofImpICodeTerm context a b child1, [a; b]);
   (proofImpECodeTerm context a b child1 child2, [a; b]);
   (proofBotECodeTerm context a child1, [a]);
   (proofLemCodeTerm context a, [a]);
   (proofAndICodeTerm context a b child1 child2, [a; b]);
   (proofAndE1CodeTerm context a b child1, [a; b]);
   (proofAndE2CodeTerm context a b child1, [a; b]);
   (proofOrI1CodeTerm context a b child1, [a; b]);
   (proofOrI2CodeTerm context a b child1, [a; b]);
   (proofOrECodeTerm context a b c child1 child2 child3, [a; b; c]);
   (proofAllICodeTerm context a child1, [a]);
   (** [t] is a term witness, not a formula code. *)
   (proofAllECodeTerm context a t child1, [a]);
   (proofExICodeTerm context a t child1, [a]);
   (proofExECodeTerm context a b child1 child2, [a; b]);
   (** Equality reflexivity has only a term witness. *)
   (proofEqReflCodeTerm context t, []);
   (** In equality elimination [a] and [b] are terms; only schema [c]
       is formula-valued. *)
   (proofEqElimCodeTerm context a b c child1 child2, [c])].

Definition rawProofOccurrenceCases (M : RawPAModel)
    (context a b c t child1 child2 child3 : M)
    : list (M * list M) :=
  [(rawListCode M [rawNumeralValue M 0; context; a], [a]);
   (rawListCode M
      [rawNumeralValue M 1; context; a; b; child1], [a; b]);
   (rawListCode M
      [rawNumeralValue M 2; context; a; b; child1; child2], [a; b]);
   (rawListCode M
      [rawNumeralValue M 3; context; a; child1], [a]);
   (rawListCode M [rawNumeralValue M 4; context; a], [a]);
   (rawListCode M
      [rawNumeralValue M 5; context; a; b; child1; child2], [a; b]);
   (rawListCode M
      [rawNumeralValue M 6; context; a; b; child1], [a; b]);
   (rawListCode M
      [rawNumeralValue M 7; context; a; b; child1], [a; b]);
   (rawListCode M
      [rawNumeralValue M 8; context; a; b; child1], [a; b]);
   (rawListCode M
      [rawNumeralValue M 9; context; a; b; child1], [a; b]);
   (rawListCode M
      [rawNumeralValue M 10; context; a; b; c;
        child1; child2; child3], [a; b; c]);
   (rawListCode M
      [rawNumeralValue M 11; context; a; child1], [a]);
   (rawListCode M
      [rawNumeralValue M 12; context; a; t; child1], [a]);
   (rawListCode M
      [rawNumeralValue M 13; context; a; t; child1], [a]);
   (rawListCode M
      [rawNumeralValue M 14; context; a; b; child1; child2], [a; b]);
   (rawListCode M [rawNumeralValue M 15; context; t], []);
   (rawListCode M
      [rawNumeralValue M 16; context; a; b; c; child1; child2], [c])].

Lemma raw_eval_proofOccurrenceCasesTerms : forall
    (M : RawPAModel) (e : nat -> M)
    context a b c t child1 child2 child3,
  map
    (fun entry =>
      (raw_term_eval M e (fst entry),
       map (raw_term_eval M e) (snd entry)))
    (proofOccurrenceCasesTerms
      context a b c t child1 child2 child3) =
  rawProofOccurrenceCases M
    (raw_term_eval M e context) (raw_term_eval M e a)
    (raw_term_eval M e b) (raw_term_eval M e c)
    (raw_term_eval M e t) (raw_term_eval M e child1)
    (raw_term_eval M e child2) (raw_term_eval M e child3).
Proof.
  intros.
  unfold proofOccurrenceCasesTerms, rawProofOccurrenceCases,
    proofAssCodeTerm, proofImpICodeTerm, proofImpECodeTerm,
    proofBotECodeTerm, proofLemCodeTerm, proofAndICodeTerm,
    proofAndE1CodeTerm, proofAndE2CodeTerm,
    proofOrI1CodeTerm, proofOrI2CodeTerm, proofOrECodeTerm,
    proofAllICodeTerm, proofAllECodeTerm, proofExICodeTerm,
    proofExECodeTerm, proofEqReflCodeTerm, proofEqElimCodeTerm.
  cbn [map]. repeat rewrite raw_eval_proofCodeFieldsTerm.
  repeat rewrite raw_term_eval_numeral. reflexivity.
Qed.

(** One case is an implication.  Consequently, if a nonstandard code has
    two constructor decompositions, both matching implications impose their
    respective context/field bounds. *)
Definition RawProofOccurrenceCaseBounded (M : RawPAModel)
    (level : nat) (code context : M) (entry : M * list M) : Prop :=
  code = fst entry ->
  RawContextAllBounded M level context /\
  Forall (RawFormulaQuantifierBounded M level) (snd entry).

Fixpoint proofOccurrenceCasesBoundedTermAt
    (level : nat) (code context : term)
    (cases : list (term * list term)) : formula :=
  match cases with
  | [] => pEq tZero tZero
  | (constructorCode, formulaFields) :: tail =>
      pAnd
        (pImp
          (pEq code constructorCode)
          (pAnd
            (contextAllBoundedTermAt level context)
            (proofFormulaFieldsBoundedTermAt level formulaFields)))
        (proofOccurrenceCasesBoundedTermAt level code context tail)
  end.

Lemma raw_sat_proofOccurrenceCasesBoundedTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M) level code context cases,
  raw_formula_sat M e
    (proofOccurrenceCasesBoundedTermAt level code context cases) <->
  Forall
    (RawProofOccurrenceCaseBounded M level
      (raw_term_eval M e code) (raw_term_eval M e context))
    (map
      (fun entry =>
        (raw_term_eval M e (fst entry),
         map (raw_term_eval M e) (snd entry)))
      cases).
Proof.
  intros M e level code context cases.
  induction cases as [|[constructorCode formulaFields] tail IH].
  - cbn [proofOccurrenceCasesBoundedTermAt raw_formula_sat].
    split; intro; [constructor | reflexivity].
  - cbn [proofOccurrenceCasesBoundedTermAt raw_formula_sat map].
    rewrite raw_sat_contextAllBoundedTermAt_iff,
      raw_sat_proofFormulaFieldsBoundedTermAt_iff, IH.
    split.
    + intros [hhead htail]. constructor.
      * unfold RawProofOccurrenceCaseBounded. cbn [fst snd].
        intros heq. destruct (hhead heq) as [hcontext hfields].
        split; [exact hcontext |].
        rewrite Forall_map. exact hfields.
      * exact htail.
    + intros hall. inversion hall; subst. split.
      * intros heq.
        unfold RawProofOccurrenceCaseBounded in H1.
        cbn [fst snd] in H1.
        destruct (H1 heq) as [hcontext hfields].
        split; [exact hcontext |].
        rewrite Forall_map in hfields. exact hfields.
      * assumption.
Qed.

(** The complete constructor-occurrence condition quantifies over all eight
    payload slots.  Unused slots are harmless because each case implication
    only mentions the fields stored by that constructor. *)
Definition proofConstructorOccurrencesBoundedTermAt
    (level : nat) (code : term) : formula :=
  restrictedProofAll8
    (proofOccurrenceCasesBoundedTermAt level
      (liftTerm 8 code) (tVar 7)
      (proofOccurrenceCasesTerms
        (tVar 7) (tVar 6) (tVar 5) (tVar 4)
        (tVar 3) (tVar 2) (tVar 1) (tVar 0))).

Definition RawProofConstructorOccurrencesBounded (M : RawPAModel)
    (level : nat) (code : M) : Prop :=
  forall context a b c t child1 child2 child3 : M,
    Forall
      (RawProofOccurrenceCaseBounded M level code context)
      (rawProofOccurrenceCases M
        context a b c t child1 child2 child3).

Arguments RawProofConstructorOccurrencesBounded M level code
  : clear implicits.

Lemma raw_sat_proofConstructorOccurrencesBoundedTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M) level code,
  raw_formula_sat M e
    (proofConstructorOccurrencesBoundedTermAt level code) <->
  RawProofConstructorOccurrencesBounded M level
    (raw_term_eval M e code).
Proof.
  intros M e level code.
  unfold proofConstructorOccurrencesBoundedTermAt,
    RawProofConstructorOccurrencesBounded, restrictedProofAll8.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_proofOccurrenceCasesBoundedTermAt_iff.
  repeat setoid_rewrite raw_restrictedProof_eval_liftTerm_eight.
  repeat setoid_rewrite raw_eval_proofOccurrenceCasesTerms.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** Conclusions are implicit in proof constructor codes, so they are handled
    through the endpoint graph.  Every endpoint occurrence is bounded, not
    just the endpoint selected by the valid-rule witness. *)
Definition proofEndpointOccurrencesBoundedTermAt
    (level : nat) (code : term) : formula :=
  restrictedProofAll2
    (pImp
      (proofEndpointTermAt
        (liftTerm 2 code) (tVar 1) (tVar 0))
      (pAnd
        (contextAllBoundedTermAt level (tVar 1))
        (formulaQuantifierBoundedTermAt level (tVar 0)))).

Definition RawProofEndpointOccurrencesBounded (M : RawPAModel)
    (level : nat) (code : M) : Prop :=
  forall context conclusion : M,
    RawProofEndpoint M code context conclusion ->
    RawContextAllBounded M level context /\
    RawFormulaQuantifierBounded M level conclusion.

Arguments RawProofEndpointOccurrencesBounded M level code
  : clear implicits.

Lemma raw_sat_proofEndpointOccurrencesBoundedTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M) level code,
  raw_formula_sat M e
    (proofEndpointOccurrencesBoundedTermAt level code) <->
  RawProofEndpointOccurrencesBounded M level
    (raw_term_eval M e code).
Proof.
  intros M e level code.
  unfold proofEndpointOccurrencesBoundedTermAt,
    RawProofEndpointOccurrencesBounded, restrictedProofAll2.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_proofEndpointTermAt_iff.
  setoid_rewrite raw_sat_contextAllBoundedTermAt_iff.
  setoid_rewrite raw_sat_formulaQuantifierBoundedTermAt_iff.
  repeat setoid_rewrite raw_restrictedProof_eval_liftTerm_two.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** ------------------------------------------------------------------
    One supported, valid, occurrence-bounded node. *)

Definition proofRuleEndpointExistsTermAt (code : term) : formula :=
  restrictedProofEx2
    (proofRuleValidTermAt (liftTerm 2 code) (tVar 1) (tVar 0)).

Definition RawProofRuleEndpointExists (M : RawPAModel) (code : M) : Prop :=
  exists context conclusion : M,
    RawProofRuleValid M code context conclusion.

Arguments RawProofRuleEndpointExists M code : clear implicits.

Lemma raw_sat_proofRuleEndpointExistsTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M) code,
  raw_formula_sat M e (proofRuleEndpointExistsTermAt code) <->
  RawProofRuleEndpointExists M (raw_term_eval M e code).
Proof.
  intros M e code.
  unfold proofRuleEndpointExistsTermAt, RawProofRuleEndpointExists,
    restrictedProofEx2.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_proofRuleValidTermAt_iff.
  repeat setoid_rewrite raw_restrictedProof_eval_liftTerm_two.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition restrictedProofNodeTermAt
    (level : nat) (code supportCode supportStep : term) : formula :=
  restrictedProofAnd4
    (proofSyntaxStepTermAt code supportCode supportStep)
    (proofRuleEndpointExistsTermAt code)
    (proofConstructorOccurrencesBoundedTermAt level code)
    (proofEndpointOccurrencesBoundedTermAt level code).

Definition RawRestrictedProofNode (M : RawPAModel)
    (level : nat) (code supportCode supportStep : M) : Prop :=
  RawProofSyntaxStep M code supportCode supportStep /\
  RawProofRuleEndpointExists M code /\
  RawProofConstructorOccurrencesBounded M level code /\
  RawProofEndpointOccurrencesBounded M level code.

Arguments RawRestrictedProofNode M level code supportCode supportStep
  : clear implicits.

Lemma raw_sat_restrictedProofNodeTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M) level code supportCode supportStep,
  raw_formula_sat M e
    (restrictedProofNodeTermAt level code supportCode supportStep) <->
  RawRestrictedProofNode M level
    (raw_term_eval M e code)
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep).
Proof.
  intros. unfold restrictedProofNodeTermAt,
    RawRestrictedProofNode, restrictedProofAnd4.
  cbn [raw_formula_sat].
  rewrite raw_sat_proofSyntaxStepTermAt_iff,
    raw_sat_proofRuleEndpointExistsTermAt_iff,
    raw_sat_proofConstructorOccurrencesBoundedTermAt_iff,
    raw_sat_proofEndpointOccurrencesBoundedTermAt_iff.
  reflexivity.
Qed.

Lemma raw_restrictedProofNode_syntax : forall
    (M : RawPAModel) level code supportCode supportStep,
  RawRestrictedProofNode M level code supportCode supportStep ->
  RawProofSyntaxStep M code supportCode supportStep.
Proof. intros M level code supportCode supportStep [h _]. exact h. Qed.

Lemma raw_restrictedProofNode_rule_endpoint : forall
    (M : RawPAModel) level code supportCode supportStep,
  RawRestrictedProofNode M level code supportCode supportStep ->
  exists context conclusion : M,
    RawProofRuleValid M code context conclusion /\
    RawContextAllBounded M level context /\
    RawFormulaQuantifierBounded M level conclusion.
Proof.
  intros M level code supportCode supportStep
    [_ [[context [conclusion hvalid]] [_ hendpoints]]].
  pose proof (raw_proofRuleValid_endpoint M
    code context conclusion hvalid) as hendpoint.
  destruct (hendpoints context conclusion hendpoint)
    as [hcontext hconclusion].
  exists context, conclusion. repeat split; assumption.
Qed.

Lemma raw_restrictedProofNode_constructor_occurrence : forall
    (M : RawPAModel) level code supportCode supportStep,
  RawRestrictedProofNode M level code supportCode supportStep ->
  forall context a b c t child1 child2 child3 constructorCode formulaFields,
  In (constructorCode, formulaFields)
    (rawProofOccurrenceCases M
      context a b c t child1 child2 child3) ->
  code = constructorCode ->
  RawContextAllBounded M level context /\
  Forall (RawFormulaQuantifierBounded M level) formulaFields.
Proof.
  intros M level code supportCode supportStep
    [_ [_ [hconstructors _]]]
    context a b c t child1 child2 child3
    constructorCode formulaFields hentry hcode.
  pose proof (proj1 (@Forall_forall (M * list M)
    (RawProofOccurrenceCaseBounded M level code context)
    (rawProofOccurrenceCases M
      context a b c t child1 child2 child3))
    (hconstructors context a b c t child1 child2 child3)
    (constructorCode, formulaFields) hentry) as hcase.
  exact (hcase hcode).
Qed.

Lemma raw_restrictedProofNode_endpoint_occurrence : forall
    (M : RawPAModel) level code supportCode supportStep,
  RawRestrictedProofNode M level code supportCode supportStep ->
  forall context conclusion,
  RawProofEndpoint M code context conclusion ->
  RawContextAllBounded M level context /\
  RawFormulaQuantifierBounded M level conclusion.
Proof.
  intros M level code supportCode supportStep
    [_ [_ [_ hendpoints]]]. exact hendpoints.
Qed.

(** Generic recursive-child elimination.  It ranges over the existing
    [rawProofRecursiveCases], so all fourteen recursive constructors are
    covered without duplicating a fragile constructor split. *)
Lemma raw_restrictedProofNode_recursive_child : forall
    (M : RawPAModel) level code supportCode supportStep,
  RawRestrictedProofNode M level code supportCode supportStep ->
  forall context a b c t child1 child2 child3,
  RawProofConstructorCode M
    code context a b c t child1 child2 child3 ->
  forall fields children,
  In (fields, children)
    (rawProofRecursiveCases M
      context a b c t child1 child2 child3) ->
  code = rawListCode M fields ->
  forall child, In child children ->
  rawProofCodeSupported M supportCode supportStep child /\
  rawLt M child code.
Proof.
  intros M level code supportCode supportStep hnode
    context a b c t child1 child2 child3 hconstructor
    fields children hentry hfields child hchild.
  pose proof (raw_proofSyntaxStep_closes_constructor M
    code supportCode supportStep
    (raw_restrictedProofNode_syntax M level
      code supportCode supportStep hnode)
    context a b c t child1 child2 child3 hconstructor) as hclosed.
  exact (raw_proofConstructorClosed_recursive_child M
    code supportCode supportStep context a b c t child1 child2 child3
    hclosed fields children hentry hfields child hchild).
Qed.

(** ------------------------------------------------------------------
    The global support traversal and root certificate. *)

Definition RawRestrictedProofTraversal (M : RawPAModel)
    (level : nat) (bound supportCode supportStep : M) : Prop :=
  RawCodedAssignmentDefinedThrough M supportCode supportStep bound /\
  forall code : M,
    rawLt M code bound ->
    rawProofCodeSupported M supportCode supportStep code ->
    RawRestrictedProofNode M level code supportCode supportStep.

Arguments RawRestrictedProofTraversal
  M level bound supportCode supportStep : clear implicits.

Definition restrictedProofTraversalTermAt
    (level : nat) (bound supportCode supportStep : term) : formula :=
  pAnd
    (codedAssignmentDefinedThroughTermAt supportCode supportStep bound)
    (pAll
      (pImp
        (Formula.ltTermAt (tVar 0) (liftTerm 1 bound))
        (pImp
          (proofCodeSupportedTermAt
            (liftTerm 1 supportCode) (liftTerm 1 supportStep) (tVar 0))
          (restrictedProofNodeTermAt level
            (tVar 0) (liftTerm 1 supportCode) (liftTerm 1 supportStep))))).

Lemma raw_sat_restrictedProofTraversalTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M) level bound supportCode supportStep,
  raw_formula_sat M e
    (restrictedProofTraversalTermAt
      level bound supportCode supportStep) <->
  RawRestrictedProofTraversal M level
    (raw_term_eval M e bound)
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep).
Proof.
  intros M e level bound supportCode supportStep.
  unfold restrictedProofTraversalTermAt, RawRestrictedProofTraversal.
  cbn [raw_formula_sat].
  rewrite raw_sat_codedAssignmentDefinedThroughTermAt_iff.
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_proofCodeSupportedTermAt_iff.
  setoid_rewrite raw_sat_restrictedProofNodeTermAt_iff.
  repeat setoid_rewrite raw_restrictedProof_eval_liftTerm_one.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_restrictedProofTraversal_syntax : forall
    (M : RawPAModel) level bound supportCode supportStep,
  RawRestrictedProofTraversal M level bound supportCode supportStep ->
  RawProofSyntaxTraversal M bound supportCode supportStep.
Proof.
  intros M level bound supportCode supportStep [hdefined hrows].
  split; [exact hdefined |].
  intros code hcode hsupported.
  exact (raw_restrictedProofNode_syntax M level code
    supportCode supportStep (hrows code hcode hsupported)).
Qed.

Lemma raw_restrictedProofTraversal_supported_node : forall
    (M : RawPAModel) level bound supportCode supportStep,
  RawRestrictedProofTraversal M level bound supportCode supportStep ->
  forall code,
  rawLt M code bound ->
  rawProofCodeSupported M supportCode supportStep code ->
  RawRestrictedProofNode M level code supportCode supportStep.
Proof. intros M level bound supportCode supportStep [_ hrows]; exact hrows. Qed.

Corollary raw_restrictedProofTraversal_supported_rule_endpoint : forall
    (M : RawPAModel) level bound supportCode supportStep,
  RawRestrictedProofTraversal M level bound supportCode supportStep ->
  forall code,
  rawLt M code bound ->
  rawProofCodeSupported M supportCode supportStep code ->
  exists context conclusion : M,
    RawProofRuleValid M code context conclusion /\
    RawContextAllBounded M level context /\
    RawFormulaQuantifierBounded M level conclusion.
Proof.
  intros M level bound supportCode supportStep htraversal
    code hcode hsupported.
  exact (raw_restrictedProofNode_rule_endpoint M level code
    supportCode supportStep
    (raw_restrictedProofTraversal_supported_node M level bound
      supportCode supportStep htraversal code hcode hsupported)).
Qed.

Theorem raw_restrictedProofTraversal_weaken : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall level large small supportCode supportStep,
  RawRestrictedProofTraversal M level large supportCode supportStep ->
  rawLe M small large ->
  RawRestrictedProofTraversal M level small supportCode supportStep.
Proof.
  intros M hPA level large small supportCode supportStep
    [hdefined hrows] hsmall. split.
  - intros index hindex. apply hdefined.
    exact (raw_lt_le_trans_pair M hPA index small large hindex hsmall).
  - intros code hcode hsupported. apply hrows; [| exact hsupported].
    exact (raw_lt_le_trans_pair M hPA code small large hcode hsmall).
Qed.

Definition RawRestrictedProofCertificateWithSupport (M : RawPAModel)
    (level : nat) (root supportCode supportStep : M) : Prop :=
  RawRestrictedProofTraversal M level
    (raw_succ M root) supportCode supportStep /\
  rawProofCodeSupported M supportCode supportStep root.

Arguments RawRestrictedProofCertificateWithSupport
  M level root supportCode supportStep : clear implicits.

Definition restrictedProofCertificateWithSupportTermAt
    (level : nat) (root supportCode supportStep : term) : formula :=
  pAnd
    (restrictedProofTraversalTermAt
      level (tSucc root) supportCode supportStep)
    (proofCodeSupportedTermAt supportCode supportStep root).

Lemma raw_sat_restrictedProofCertificateWithSupportTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M) level root supportCode supportStep,
  raw_formula_sat M e
    (restrictedProofCertificateWithSupportTermAt
      level root supportCode supportStep) <->
  RawRestrictedProofCertificateWithSupport M level
    (raw_term_eval M e root)
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep).
Proof.
  intros. unfold restrictedProofCertificateWithSupportTermAt,
    RawRestrictedProofCertificateWithSupport.
  cbn [raw_formula_sat].
  rewrite raw_sat_restrictedProofTraversalTermAt_iff,
    raw_sat_proofCodeSupportedTermAt_iff.
  reflexivity.
Qed.

Definition RawRestrictedProof (M : RawPAModel)
    (level : nat) (root : M) : Prop :=
  exists supportCode supportStep : M,
    RawRestrictedProofCertificateWithSupport M
      level root supportCode supportStep.

Arguments RawRestrictedProof M level root : clear implicits.

Definition restrictedProofTermAt (level : nat) (root : term) : formula :=
  restrictedProofEx2
    (restrictedProofCertificateWithSupportTermAt
      level (liftTerm 2 root) (tVar 1) (tVar 0)).

Lemma raw_sat_restrictedProofTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M) level root,
  raw_formula_sat M e (restrictedProofTermAt level root) <->
  RawRestrictedProof M level (raw_term_eval M e root).
Proof.
  intros M e level root.
  unfold restrictedProofTermAt, RawRestrictedProof, restrictedProofEx2.
  cbn [raw_formula_sat].
  setoid_rewrite
    raw_sat_restrictedProofCertificateWithSupportTermAt_iff.
  repeat setoid_rewrite raw_restrictedProof_eval_liftTerm_two.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_restrictedProofCertificate_syntax : forall
    (M : RawPAModel) level root supportCode supportStep,
  RawRestrictedProofCertificateWithSupport M
    level root supportCode supportStep ->
  RawProofSyntaxCertificateWithSupport M root supportCode supportStep.
Proof.
  intros M level root supportCode supportStep [htraversal hroot].
  split; [| exact hroot].
  exact (raw_restrictedProofTraversal_syntax M level
    (raw_succ M root) supportCode supportStep htraversal).
Qed.

Theorem raw_restrictedProofCertificate_root_node : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall level root supportCode supportStep,
  RawRestrictedProofCertificateWithSupport M
    level root supportCode supportStep ->
  RawRestrictedProofNode M level root supportCode supportStep.
Proof.
  intros M hPA level root supportCode supportStep
    [htraversal hroot].
  exact (raw_restrictedProofTraversal_supported_node M level
    (raw_succ M root) supportCode supportStep htraversal root
    (raw_assignment_lt_self_succ M hPA root) hroot).
Qed.

Theorem raw_restrictedProofCertificate_root_rule_endpoint : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall level root supportCode supportStep,
  RawRestrictedProofCertificateWithSupport M
    level root supportCode supportStep ->
  exists context conclusion : M,
    RawProofRuleValid M root context conclusion /\
    RawContextAllBounded M level context /\
    RawFormulaQuantifierBounded M level conclusion.
Proof.
  intros M hPA level root supportCode supportStep hcertificate.
  exact (raw_restrictedProofNode_rule_endpoint M level root
    supportCode supportStep
    (raw_restrictedProofCertificate_root_node M hPA level root
      supportCode supportStep hcertificate)).
Qed.

Corollary raw_restrictedProof_root_rule_endpoint : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall level root,
  RawRestrictedProof M level root ->
  exists context conclusion : M,
    RawProofRuleValid M root context conclusion /\
    RawContextAllBounded M level context /\
    RawFormulaQuantifierBounded M level conclusion.
Proof.
  intros M hPA level root [supportCode [supportStep hcertificate]].
  exact (raw_restrictedProofCertificate_root_rule_endpoint M hPA
    level root supportCode supportStep hcertificate).
Qed.

(** Every recursive premise receives the same global validity/boundedness
    certificate, restricted arithmetically to its successor prefix. *)
Theorem raw_restrictedProofCertificate_recursive_child : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall level root supportCode supportStep,
  RawRestrictedProofCertificateWithSupport M
    level root supportCode supportStep ->
  forall context a b c t child1 child2 child3,
  RawProofConstructorCode M
    root context a b c t child1 child2 child3 ->
  forall fields children,
  In (fields, children)
    (rawProofRecursiveCases M
      context a b c t child1 child2 child3) ->
  root = rawListCode M fields ->
  forall child, In child children ->
  RawRestrictedProofCertificateWithSupport M
    level child supportCode supportStep /\
  rawLt M child root.
Proof.
  intros M hPA level root supportCode supportStep
    hcertificate context a b c t child1 child2 child3 hconstructor
    fields children hentry hfields child hchild.
  destruct hcertificate as [htraversal hroot].
  assert (hsyntaxCertificate : RawProofSyntaxCertificateWithSupport M
      root supportCode supportStep).
  {
    split; [| exact hroot].
    exact (raw_restrictedProofTraversal_syntax M level
      (raw_succ M root) supportCode supportStep htraversal).
  }
  destruct (raw_proofSyntaxCertificate_recursive_child M hPA
    root supportCode supportStep hsyntaxCertificate
    context a b c t child1 child2 child3 hconstructor
    fields children hentry hfields child hchild)
    as [[_ hchildSupported] hchildBelow].
  split; [split | exact hchildBelow].
  - apply (raw_restrictedProofTraversal_weaken M hPA level
      (raw_succ M root) (raw_succ M child)
      supportCode supportStep htraversal).
    eapply raw_le_trans; [exact hPA | |].
    + exact (raw_succ_le_of_lt_pair M hPA child root hchildBelow).
    + exact (raw_lt_to_le M root (raw_succ M root)
        (raw_assignment_lt_self_succ M hPA root)).
  - exact hchildSupported.
Qed.

Corollary raw_restrictedProof_recursive_child : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall level root,
  RawRestrictedProof M level root ->
  forall context a b c t child1 child2 child3,
  RawProofConstructorCode M
    root context a b c t child1 child2 child3 ->
  forall fields children,
  In (fields, children)
    (rawProofRecursiveCases M
      context a b c t child1 child2 child3) ->
  root = rawListCode M fields ->
  forall child, In child children ->
  RawRestrictedProof M level child /\ rawLt M child root.
Proof.
  intros M hPA level root
    [supportCode [supportStep hcertificate]]
    context a b c t child1 child2 child3 hconstructor
    fields children hentry hfields child hchild.
  destruct (raw_restrictedProofCertificate_recursive_child M hPA
    level root supportCode supportStep hcertificate
    context a b c t child1 child2 child3 hconstructor
    fields children hentry hfields child hchild)
    as [hchildCertificate hbelow].
  split; [| exact hbelow].
  exists supportCode, supportStep. exact hchildCertificate.
Qed.

Corollary raw_restrictedProof_syntax_realizable : forall
    (M : RawPAModel) level root,
  RawRestrictedProof M level root ->
  RawProofSyntaxRealizable M root.
Proof.
  intros M level root [supportCode [supportStep hcertificate]].
  exists supportCode, supportStep.
  exact (raw_restrictedProofCertificate_syntax M level root
    supportCode supportStep hcertificate).
Qed.

(** ------------------------------------------------------------------
    Closed arithmetic consequences and their PA proofs. *)

Definition RawRestrictedProofSupportedNodeLaw
    (M : RawPAModel) (level : nat) : Prop :=
  forall root supportCode supportStep code : M,
    RawRestrictedProofCertificateWithSupport M
      level root supportCode supportStep ->
    rawLt M code (raw_succ M root) ->
    rawProofCodeSupported M supportCode supportStep code ->
    RawRestrictedProofNode M level code supportCode supportStep.

Definition restrictedProofSupportedNodeBodyFormula (level : nat) : formula :=
  pAll (pAll (pAll (pAll
    (pImp
      (restrictedProofCertificateWithSupportTermAt level
        (tVar 3) (tVar 2) (tVar 1))
      (pImp
        (Formula.ltTermAt (tVar 0) (tSucc (tVar 3)))
        (pImp
          (proofCodeSupportedTermAt (tVar 2) (tVar 1) (tVar 0))
          (restrictedProofNodeTermAt level
            (tVar 0) (tVar 2) (tVar 1)))))))).

Lemma raw_sat_restrictedProofSupportedNodeBodyFormula_iff : forall
    (M : RawPAModel) (e : nat -> M) level,
  raw_formula_sat M e (restrictedProofSupportedNodeBodyFormula level) <->
  RawRestrictedProofSupportedNodeLaw M level.
Proof.
  intros M e level.
  unfold restrictedProofSupportedNodeBodyFormula,
    RawRestrictedProofSupportedNodeLaw.
  cbn [raw_formula_sat].
  setoid_rewrite
    raw_sat_restrictedProofCertificateWithSupportTermAt_iff.
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_proofCodeSupportedTermAt_iff.
  setoid_rewrite raw_sat_restrictedProofNodeTermAt_iff.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition restrictedProofSupportedNodeFormula (level : nat) : formula :=
  Formula.sealPA (restrictedProofSupportedNodeBodyFormula level).

Theorem restrictedProofSupportedNodeFormula_sentence : forall level,
  Formula.Sentence (restrictedProofSupportedNodeFormula level).
Proof.
  intro level. unfold restrictedProofSupportedNodeFormula.
  apply Formula.sealPA_sentence.
Qed.

Theorem restrictedProofSupportedNodeFormula_raw_valid : forall level
    (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e (restrictedProofSupportedNodeFormula level).
Proof.
  intros level M hPA e.
  assert (hlaw : RawRestrictedProofSupportedNodeLaw M level).
  {
    intros root supportCode supportStep code
      [htraversal _] hcode hsupported.
    exact (raw_restrictedProofTraversal_supported_node M level
      (raw_succ M root) supportCode supportStep
      htraversal code hcode hsupported).
  }
  unfold restrictedProofSupportedNodeFormula.
  exact (raw_formula_sat_sealPA_of_valid M
    (restrictedProofSupportedNodeBodyFormula level)
    (fun e' => proj2
      (raw_sat_restrictedProofSupportedNodeBodyFormula_iff M e' level)
      hlaw) e).
Qed.

Theorem PA_proves_restrictedProofSupportedNodeFormula : forall level,
  Formula.BProv Formula.Ax_s []
    (restrictedProofSupportedNodeFormula level).
Proof.
  intro level. apply PA_BProv_of_raw_valid.
  - exact (restrictedProofSupportedNodeFormula_sentence level).
  - exact (restrictedProofSupportedNodeFormula_raw_valid level).
Qed.

Definition RawRestrictedProofRootEndpointBoundedLaw
    (M : RawPAModel) (level : nat) : Prop :=
  forall root : M,
    RawRestrictedProof M level root ->
    exists context conclusion : M,
      RawProofRuleValid M root context conclusion /\
      RawContextAllBounded M level context /\
      RawFormulaQuantifierBounded M level conclusion.

Definition restrictedProofRootEndpointBoundedBodyFormula
    (level : nat) : formula :=
  pAll
    (pImp
      (restrictedProofTermAt level (tVar 0))
      (restrictedProofEx2
        (restrictedProofAnd3
          (proofRuleValidTermAt
            (liftTerm 2 (tVar 0)) (tVar 1) (tVar 0))
          (contextAllBoundedTermAt level (tVar 1))
          (formulaQuantifierBoundedTermAt level (tVar 0))))).

Lemma raw_sat_restrictedProofRootEndpointBoundedBodyFormula_iff : forall
    (M : RawPAModel) (e : nat -> M) level,
  raw_formula_sat M e
    (restrictedProofRootEndpointBoundedBodyFormula level) <->
  RawRestrictedProofRootEndpointBoundedLaw M level.
Proof.
  intros M e level.
  unfold restrictedProofRootEndpointBoundedBodyFormula,
    RawRestrictedProofRootEndpointBoundedLaw,
    restrictedProofEx2, restrictedProofAnd3.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_restrictedProofTermAt_iff.
  setoid_rewrite raw_sat_proofRuleValidTermAt_iff.
  setoid_rewrite raw_sat_contextAllBoundedTermAt_iff.
  setoid_rewrite raw_sat_formulaQuantifierBoundedTermAt_iff.
  repeat setoid_rewrite raw_restrictedProof_eval_liftTerm_two.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition restrictedProofRootEndpointBoundedFormula
    (level : nat) : formula :=
  Formula.sealPA (restrictedProofRootEndpointBoundedBodyFormula level).

Theorem restrictedProofRootEndpointBoundedFormula_sentence : forall level,
  Formula.Sentence (restrictedProofRootEndpointBoundedFormula level).
Proof.
  intro level. unfold restrictedProofRootEndpointBoundedFormula.
  apply Formula.sealPA_sentence.
Qed.

Theorem restrictedProofRootEndpointBoundedFormula_raw_valid : forall level
    (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e
    (restrictedProofRootEndpointBoundedFormula level).
Proof.
  intros level M hPA e.
  assert (hlaw : RawRestrictedProofRootEndpointBoundedLaw M level).
  {
    intros root [supportCode [supportStep hcertificate]].
    exact (raw_restrictedProofCertificate_root_rule_endpoint M hPA
      level root supportCode supportStep hcertificate).
  }
  unfold restrictedProofRootEndpointBoundedFormula.
  exact (raw_formula_sat_sealPA_of_valid M
    (restrictedProofRootEndpointBoundedBodyFormula level)
    (fun e' => proj2
      (raw_sat_restrictedProofRootEndpointBoundedBodyFormula_iff
        M e' level) hlaw) e).
Qed.

Theorem PA_proves_restrictedProofRootEndpointBoundedFormula : forall level,
  Formula.BProv Formula.Ax_s []
    (restrictedProofRootEndpointBoundedFormula level).
Proof.
  intro level. apply PA_BProv_of_raw_valid.
  - exact (restrictedProofRootEndpointBoundedFormula_sentence level).
  - exact (restrictedProofRootEndpointBoundedFormula_raw_valid level).
Qed.

Definition restrictedProofImpliesSyntaxBodyFormula
    (level : nat) : formula :=
  pAll
    (pImp
      (restrictedProofTermAt level (tVar 0))
      (proofSyntaxRealizableTermAt (tVar 0))).

Lemma raw_sat_restrictedProofImpliesSyntaxBodyFormula_iff : forall
    (M : RawPAModel) (e : nat -> M) level,
  raw_formula_sat M e (restrictedProofImpliesSyntaxBodyFormula level) <->
  forall root : M,
    RawRestrictedProof M level root -> RawProofSyntaxRealizable M root.
Proof.
  intros M e level.
  unfold restrictedProofImpliesSyntaxBodyFormula.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_restrictedProofTermAt_iff.
  setoid_rewrite raw_sat_proofSyntaxRealizableTermAt_iff.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition restrictedProofImpliesSyntaxFormula (level : nat) : formula :=
  Formula.sealPA (restrictedProofImpliesSyntaxBodyFormula level).

Theorem restrictedProofImpliesSyntaxFormula_sentence : forall level,
  Formula.Sentence (restrictedProofImpliesSyntaxFormula level).
Proof.
  intro level. unfold restrictedProofImpliesSyntaxFormula.
  apply Formula.sealPA_sentence.
Qed.

Theorem restrictedProofImpliesSyntaxFormula_raw_valid : forall level
    (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e (restrictedProofImpliesSyntaxFormula level).
Proof.
  intros level M hPA e.
  unfold restrictedProofImpliesSyntaxFormula.
  exact (raw_formula_sat_sealPA_of_valid M
    (restrictedProofImpliesSyntaxBodyFormula level)
    (fun e' => proj2
      (raw_sat_restrictedProofImpliesSyntaxBodyFormula_iff M e' level)
      (raw_restrictedProof_syntax_realizable M level)) e).
Qed.

Theorem PA_proves_restrictedProofImpliesSyntaxFormula : forall level,
  Formula.BProv Formula.Ax_s []
    (restrictedProofImpliesSyntaxFormula level).
Proof.
  intro level. apply PA_BProv_of_raw_valid.
  - exact (restrictedProofImpliesSyntaxFormula_sentence level).
  - exact (restrictedProofImpliesSyntaxFormula_raw_valid level).
Qed.

(** ------------------------------------------------------------------
    Explicit standard-quotation seam.

    This file intentionally does not claim the following property.  Building
    a certificate for every quoted standard proof needs realization of the
    context tables and of the formula shift/substitution graphs used by
    [RawProofRuleValid].  Their nonstandard functionality is available, but
    the corresponding quotation-realization theorem is not yet part of the
    repository.  Naming the exact missing bridge is preferable to hiding it
    behind a decoder or a new axiom. *)
Definition RawRestrictedProvTreeQuotationAdequacy
    (M : RawPAModel) : Prop :=
  forall level G phi (derivation : ProvTree G phi),
    proofOccurrenceRank derivation <= level ->
    RawRestrictedProof M level
      (rawQuotedProofCode M (rawOfProvTree derivation)).

Arguments RawRestrictedProvTreeQuotationAdequacy M : clear implicits.

Theorem raw_restrictedProof_of_quoted_provTree_under_adequacy : forall
    (M : RawPAModel),
  RawRestrictedProvTreeQuotationAdequacy M ->
  forall level G phi (derivation : ProvTree G phi),
  ProofAllBounded level derivation ->
  RawRestrictedProof M level
    (rawQuotedProofCode M (rawOfProvTree derivation)).
Proof.
  intros M hadequacy level G phi derivation hbounded.
  exact (hadequacy level G phi derivation hbounded).
Qed.

End PABoundedRawCodedRestrictedProofTraversal.
