(**
  Proof-wide atomic-term adequacy for model-internal proof codes.

  Hierarchy ranks intentionally treat the two payloads of an equality as
  opaque numbers: quantifier alternation does not depend on term syntax.
  Fixed-level truth, however, can evaluate an equality only when both
  payloads carry honest coded-term traversals under the current assignment.
  Thus quantifier boundedness alone is not a sufficient soundness domain.

  This module records the missing orthogonal condition.  Every supported
  proof node has an endpoint; every formula in that endpoint's context and
  its conclusion is atomically adequate.  The support table is shared with a
  complete proof-syntax certificate, so the universal row condition cannot
  be made vacuous by omitting a recursive premise.  All definitions are PA
  formulae with exact arbitrary-model semantics.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import ListCode Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  PolynomialPairInjectivity RawCodedSyntaxConstructors
  RawCodedAssignment RawCodedContextLists
  RawCodedProofConstructors
  RawCodedProofDescent RawCodedProofTraversal
  RawCodedProofEndpoints RawCodedFixedLevelTruthTotality.

Module PABoundedRawCodedProofAtomicAdequacy.

Import PA.
Import PAListCode.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedProofTraversal.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedFixedLevelTruthTotality.

Definition proofAtomicEx2 (body : formula) : formula := pEx (pEx body).

Lemma raw_proofAtomic_eval_liftTerm_one : forall
    (M : RawPAModel) value (e : nat -> M) t,
  raw_term_eval M (scons M value e) (liftTerm 1 t) =
  raw_term_eval M e t.
Proof.
  intros M value e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro index.
  replace (index + 1) with (S index) by lia. reflexivity.
Qed.

Lemma raw_proofAtomic_eval_liftTerm_two : forall
    (M : RawPAModel) first second (e : nat -> M) t,
  raw_term_eval M (scons M first (scons M second e)) (liftTerm 2 t) =
  raw_term_eval M e t.
Proof.
  intros M first second e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro index.
  replace (index + 2) with (S (S index)) by lia. reflexivity.
Qed.

(** ------------------------------------------------------------------
    Atomic adequacy of every member of one honest context traversal. *)

Definition RawContextAllAtomicallyAdequateWithTables (M : RawPAModel)
    (bound headCode headStep : M) : Prop :=
  forall index,
    rawLt M index bound ->
    forall code,
      RawCodedAssignmentLookup M headCode headStep index code ->
      RawCodedFormulaAtomicallyAdequate M code.

Arguments RawContextAllAtomicallyAdequateWithTables
  M bound headCode headStep : clear implicits.

Definition contextAllAtomicallyAdequateWithTablesTermAt
    (bound headCode headStep : term) : formula :=
  pAll
    (pImp
      (Formula.ltTermAt (tVar 0) (liftTerm 1 bound))
      (pAll
        (pImp
          (codedAssignmentLookupTermAt
            (liftTerm 2 headCode) (liftTerm 2 headStep)
            (tVar 1) (tVar 0))
          (codedFormulaAtomicallyAdequateTermAt (tVar 0))))).

Lemma raw_sat_contextAllAtomicallyAdequateWithTablesTermAt_iff : forall
    (M : RawPAModel) e bound headCode headStep,
  raw_formula_sat M e
    (contextAllAtomicallyAdequateWithTablesTermAt
      bound headCode headStep) <->
  RawContextAllAtomicallyAdequateWithTables M
    (raw_term_eval M e bound)
    (raw_term_eval M e headCode) (raw_term_eval M e headStep).
Proof.
  intros M e bound headCode headStep.
  unfold contextAllAtomicallyAdequateWithTablesTermAt,
    RawContextAllAtomicallyAdequateWithTables.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedAssignmentLookupTermAt_iff.
  setoid_rewrite raw_sat_codedFormulaAtomicallyAdequateTermAt_iff.
  repeat setoid_rewrite raw_proofAtomic_eval_liftTerm_one.
  repeat setoid_rewrite raw_proofAtomic_eval_liftTerm_two.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition RawContextAllAtomicallyAdequate (M : RawPAModel)
    (root : M) : Prop :=
  exists bound tailCode tailStep headCode headStep : M,
    RawContextListTraversal M
      root bound tailCode tailStep headCode headStep /\
    RawContextAllAtomicallyAdequateWithTables M
      bound headCode headStep.

Arguments RawContextAllAtomicallyAdequate M root : clear implicits.

Definition contextAllAtomicallyAdequateTermAt (root : term) : formula :=
  contextListEx5
    (pAnd
      (contextListTraversalTermAt
        (liftTerm 5 root) (tVar 4) (tVar 3) (tVar 2) (tVar 1) (tVar 0))
      (contextAllAtomicallyAdequateWithTablesTermAt
        (tVar 4) (tVar 1) (tVar 0))).

Lemma raw_sat_contextAllAtomicallyAdequateTermAt_iff : forall
    (M : RawPAModel) e root,
  raw_formula_sat M e (contextAllAtomicallyAdequateTermAt root) <->
  RawContextAllAtomicallyAdequate M (raw_term_eval M e root).
Proof.
  intros M e root.
  unfold contextAllAtomicallyAdequateTermAt, contextListEx5,
    RawContextAllAtomicallyAdequate.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_contextListTraversalTermAt_iff.
  setoid_rewrite
    raw_sat_contextAllAtomicallyAdequateWithTablesTermAt_iff.
  repeat setoid_rewrite raw_contextList_eval_liftTerm_five.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** ------------------------------------------------------------------
    Endpoint and proof-wide certificates. *)

Definition RawProofEndpointAtomicallyAdequate (M : RawPAModel)
    (code : M) : Prop :=
  forall context conclusion : M,
    RawProofEndpoint M code context conclusion ->
    RawContextAllAtomicallyAdequate M context /\
    RawCodedFormulaAtomicallyAdequate M conclusion.

Arguments RawProofEndpointAtomicallyAdequate M code : clear implicits.

Definition proofEndpointAtomicallyAdequateTermAt (code : term) : formula :=
  pAll (pAll
    (pImp
      (proofEndpointTermAt (liftTerm 2 code) (tVar 1) (tVar 0))
      (pAnd
        (contextAllAtomicallyAdequateTermAt (tVar 1))
        (codedFormulaAtomicallyAdequateTermAt (tVar 0))))).

Lemma raw_sat_proofEndpointAtomicallyAdequateTermAt_iff : forall
    (M : RawPAModel) e code,
  raw_formula_sat M e
    (proofEndpointAtomicallyAdequateTermAt code) <->
  RawProofEndpointAtomicallyAdequate M (raw_term_eval M e code).
Proof.
  intros M e code.
  unfold proofEndpointAtomicallyAdequateTermAt,
    RawProofEndpointAtomicallyAdequate.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_proofEndpointTermAt_iff.
  setoid_rewrite raw_sat_contextAllAtomicallyAdequateTermAt_iff.
  setoid_rewrite raw_sat_codedFormulaAtomicallyAdequateTermAt_iff.
  repeat setoid_rewrite raw_proofAtomic_eval_liftTerm_two.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** The syntax certificate closes recursive support.  The second conjunct
    places atomic adequacy on every marked node in exactly that support
    table, including all nonstandard nodes below the root. *)
Definition RawProofAtomicAdequacyWithSupport (M : RawPAModel)
    (root supportCode supportStep : M) : Prop :=
  RawProofSyntaxCertificateWithSupport M root supportCode supportStep /\
  forall code : M,
    rawLt M code (raw_succ M root) ->
    rawProofCodeSupported M supportCode supportStep code ->
    RawProofEndpointAtomicallyAdequate M code.

Arguments RawProofAtomicAdequacyWithSupport
  M root supportCode supportStep : clear implicits.

Definition proofAtomicAdequacyWithSupportTermAt
    (root supportCode supportStep : term) : formula :=
  pAnd
    (proofSyntaxCertificateWithSupportTermAt root supportCode supportStep)
    (pAll
      (pImp
        (Formula.ltTermAt (tVar 0) (liftTerm 1 (tSucc root)))
        (pImp
          (proofCodeSupportedTermAt
            (liftTerm 1 supportCode) (liftTerm 1 supportStep) (tVar 0))
          (proofEndpointAtomicallyAdequateTermAt (tVar 0))))).

Lemma raw_sat_proofAtomicAdequacyWithSupportTermAt_iff : forall
    (M : RawPAModel) e root supportCode supportStep,
  raw_formula_sat M e
    (proofAtomicAdequacyWithSupportTermAt
      root supportCode supportStep) <->
  RawProofAtomicAdequacyWithSupport M
    (raw_term_eval M e root)
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep).
Proof.
  intros M e root supportCode supportStep.
  unfold proofAtomicAdequacyWithSupportTermAt,
    RawProofAtomicAdequacyWithSupport.
  cbn [raw_formula_sat].
  rewrite raw_sat_proofSyntaxCertificateWithSupportTermAt_iff.
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_proofCodeSupportedTermAt_iff.
  setoid_rewrite raw_sat_proofEndpointAtomicallyAdequateTermAt_iff.
  repeat setoid_rewrite raw_proofAtomic_eval_liftTerm_one.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition RawProofAtomicallyAdequate (M : RawPAModel)
    (root : M) : Prop :=
  exists supportCode supportStep : M,
    RawProofAtomicAdequacyWithSupport M root supportCode supportStep.

Arguments RawProofAtomicallyAdequate M root : clear implicits.

Definition proofAtomicallyAdequateTermAt (root : term) : formula :=
  proofAtomicEx2
    (proofAtomicAdequacyWithSupportTermAt
      (liftTerm 2 root) (tVar 1) (tVar 0)).

Lemma raw_sat_proofAtomicallyAdequateTermAt_iff : forall
    (M : RawPAModel) e root,
  raw_formula_sat M e (proofAtomicallyAdequateTermAt root) <->
  RawProofAtomicallyAdequate M (raw_term_eval M e root).
Proof.
  intros M e root.
  unfold proofAtomicallyAdequateTermAt, proofAtomicEx2,
    RawProofAtomicallyAdequate.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_proofAtomicAdequacyWithSupportTermAt_iff.
  repeat setoid_rewrite raw_proofAtomic_eval_liftTerm_two.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** The root endpoint is covered because the syntax certificate explicitly
    marks the root and arithmetic proves [root < S root]. *)
Theorem raw_proofAtomicAdequacy_root_endpoint : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      root supportCode supportStep,
  RawProofAtomicAdequacyWithSupport M root supportCode supportStep ->
  RawProofEndpointAtomicallyAdequate M root.
Proof.
  intros M hPA root supportCode supportStep
    [[_ hrootSupported] hrows].
  exact (hrows root (raw_assignment_lt_self_succ M hPA root)
    hrootSupported).
Qed.

Corollary raw_proofAtomicallyAdequate_root_endpoint : forall
    (M : RawPAModel), RawPASatisfies M -> forall root,
  RawProofAtomicallyAdequate M root ->
  RawProofEndpointAtomicallyAdequate M root.
Proof.
  intros M hPA root
    (supportCode & supportStep & hadequate).
  exact (raw_proofAtomicAdequacy_root_endpoint M hPA
    root supportCode supportStep hadequate).
Qed.

(** Restricting to a recursive child preserves both halves.  Syntax closure
    gives the child's root marker, and every code below [S child] was already
    below [S root] because constructor descent gives [child < root]. *)
Theorem raw_proofAtomicAdequacy_recursive_child : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      root supportCode supportStep,
  RawProofAtomicAdequacyWithSupport M root supportCode supportStep ->
  forall context a b c t child1 child2 child3,
  RawProofConstructorCode M
    root context a b c t child1 child2 child3 ->
  forall fields children,
  In (fields, children)
    (rawProofRecursiveCases M
      context a b c t child1 child2 child3) ->
  root = rawListCode M fields ->
  forall child, In child children ->
  RawProofAtomicAdequacyWithSupport M
    child supportCode supportStep /\
  rawLt M child root.
Proof.
  intros M hPA root supportCode supportStep
    [hsyntax hrows]
    context a b c t child1 child2 child3 hconstructor
    fields children hentry hfields child hchild.
  destruct (raw_proofSyntaxCertificate_recursive_child M hPA
    root supportCode supportStep hsyntax
    context a b c t child1 child2 child3 hconstructor
    fields children hentry hfields child hchild)
    as [hchildSyntax hchildBelow].
  split; [split | exact hchildBelow].
  - exact hchildSyntax.
  - intros code hcode hsupported. apply hrows; [| exact hsupported].
    eapply raw_lt_le_trans_pair; [exact hPA | exact hcode |].
    eapply raw_le_trans; [exact hPA | |].
    + exact (raw_succ_le_of_lt_pair M hPA child root hchildBelow).
    + exact (raw_lt_to_le M root (raw_succ M root)
        (raw_assignment_lt_self_succ M hPA root)).
Qed.

End PABoundedRawCodedProofAtomicAdequacy.
