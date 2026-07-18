(**
  One numeric assignment-coverage bound for every formula in a raw proof.

  Fixed-level truth uses beta-coded environments which are defined through
  a numeric bound.  At quantifier rules the environment is extended and then
  reused throughout an entire premise derivation, so merely covering the
  quantified root formula is not enough: intermediate premise formula codes
  may be larger.  This module records one common carrier bound strictly above
  every conclusion and every displayed context member at every supported
  proof node.

  The condition shares a support table with a complete proof-syntax
  certificate.  Thus its universal rows cannot evade a recursive child by
  leaving that child unmarked.  As elsewhere, no model element is decoded
  into a metatheoretic list or proof tree.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import ListCode Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  PolynomialPairInjectivity
  RawCodedSyntaxConstructors RawCodedAssignment RawCodedContextLists
  RawCodedProofConstructors RawCodedProofDescent RawCodedProofTraversal
  RawCodedProofEndpoints.

Module PABoundedRawCodedProofFormulaCoverage.

Import PA.
Import PAListCode.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedProofTraversal.
Import PABoundedRawCodedProofEndpoints.

Definition proofCoverageEx2 (body : formula) : formula := pEx (pEx body).

Lemma raw_proofCoverage_eval_liftTerm_one : forall
    (M : RawPAModel) value (e : nat -> M) t,
  raw_term_eval M (scons M value e) (liftTerm 1 t) =
  raw_term_eval M e t.
Proof.
  intros M value e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro index.
  replace (index + 1) with (S index) by lia. reflexivity.
Qed.

Lemma raw_proofCoverage_eval_liftTerm_two : forall
    (M : RawPAModel) first second (e : nat -> M) t,
  raw_term_eval M (scons M first (scons M second e)) (liftTerm 2 t) =
  raw_term_eval M e t.
Proof.
  intros M first second e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro index.
  replace (index + 2) with (S (S index)) by lia. reflexivity.
Qed.

(** ------------------------------------------------------------------
    Numeric coverage of one coded context. *)

Definition RawContextAllCodesBelowWithTables (M : RawPAModel)
    (contextLength headCode headStep coverageBound : M) : Prop :=
  forall index,
    rawLt M index contextLength ->
    forall code,
      RawCodedAssignmentLookup M headCode headStep index code ->
      rawLt M code coverageBound.

Arguments RawContextAllCodesBelowWithTables
  M contextLength headCode headStep coverageBound : clear implicits.

Definition contextAllCodesBelowWithTablesTermAt
    (contextLength headCode headStep coverageBound : term) : formula :=
  pAll
    (pImp
      (Formula.ltTermAt (tVar 0) (liftTerm 1 contextLength))
      (pAll
        (pImp
          (codedAssignmentLookupTermAt
            (liftTerm 2 headCode) (liftTerm 2 headStep)
            (tVar 1) (tVar 0))
          (Formula.ltTermAt (tVar 0) (liftTerm 2 coverageBound))))).

Lemma raw_sat_contextAllCodesBelowWithTablesTermAt_iff : forall
    (M : RawPAModel) e contextLength headCode headStep coverageBound,
  raw_formula_sat M e
    (contextAllCodesBelowWithTablesTermAt
      contextLength headCode headStep coverageBound) <->
  RawContextAllCodesBelowWithTables M
    (raw_term_eval M e contextLength)
    (raw_term_eval M e headCode) (raw_term_eval M e headStep)
    (raw_term_eval M e coverageBound).
Proof.
  intros M e contextLength headCode headStep coverageBound.
  unfold contextAllCodesBelowWithTablesTermAt,
    RawContextAllCodesBelowWithTables.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedAssignmentLookupTermAt_iff.
  repeat setoid_rewrite raw_proofCoverage_eval_liftTerm_one.
  repeat setoid_rewrite raw_proofCoverage_eval_liftTerm_two.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition RawContextAllCodesBelow (M : RawPAModel)
    (context coverageBound : M) : Prop :=
  exists contextLength tailCode tailStep headCode headStep : M,
    RawContextListTraversal M context contextLength
      tailCode tailStep headCode headStep /\
    RawContextAllCodesBelowWithTables M
      contextLength headCode headStep coverageBound.

Arguments RawContextAllCodesBelow M context coverageBound : clear implicits.

Definition contextAllCodesBelowTermAt
    (context coverageBound : term) : formula :=
  contextListEx5
    (pAnd
      (contextListTraversalTermAt
        (liftTerm 5 context) (tVar 4) (tVar 3) (tVar 2)
        (tVar 1) (tVar 0))
      (contextAllCodesBelowWithTablesTermAt
        (tVar 4) (tVar 1) (tVar 0) (liftTerm 5 coverageBound))).

Lemma raw_sat_contextAllCodesBelowTermAt_iff : forall
    (M : RawPAModel) e context coverageBound,
  raw_formula_sat M e
    (contextAllCodesBelowTermAt context coverageBound) <->
  RawContextAllCodesBelow M
    (raw_term_eval M e context) (raw_term_eval M e coverageBound).
Proof.
  intros M e context coverageBound.
  unfold contextAllCodesBelowTermAt, contextListEx5,
    RawContextAllCodesBelow.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_contextListTraversalTermAt_iff.
  setoid_rewrite raw_sat_contextAllCodesBelowWithTablesTermAt_iff.
  repeat setoid_rewrite raw_contextList_eval_liftTerm_five.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** ------------------------------------------------------------------
    Endpoint and proof-wide coverage. *)

Definition RawProofEndpointFormulaCoverage (M : RawPAModel)
    (code coverageBound : M) : Prop :=
  forall context conclusion : M,
    RawProofEndpoint M code context conclusion ->
    RawContextAllCodesBelow M context coverageBound /\
    rawLt M conclusion coverageBound.

Arguments RawProofEndpointFormulaCoverage
  M code coverageBound : clear implicits.

Definition proofEndpointFormulaCoverageTermAt
    (code coverageBound : term) : formula :=
  pAll (pAll
    (pImp
      (proofEndpointTermAt (liftTerm 2 code) (tVar 1) (tVar 0))
      (pAnd
        (contextAllCodesBelowTermAt
          (tVar 1) (liftTerm 2 coverageBound))
        (Formula.ltTermAt (tVar 0) (liftTerm 2 coverageBound))))).

Lemma raw_sat_proofEndpointFormulaCoverageTermAt_iff : forall
    (M : RawPAModel) e code coverageBound,
  raw_formula_sat M e
    (proofEndpointFormulaCoverageTermAt code coverageBound) <->
  RawProofEndpointFormulaCoverage M
    (raw_term_eval M e code) (raw_term_eval M e coverageBound).
Proof.
  intros M e code coverageBound.
  unfold proofEndpointFormulaCoverageTermAt,
    RawProofEndpointFormulaCoverage.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_proofEndpointTermAt_iff.
  setoid_rewrite raw_sat_contextAllCodesBelowTermAt_iff.
  setoid_rewrite raw_sat_ltTermAt_iff.
  repeat setoid_rewrite raw_proofCoverage_eval_liftTerm_two.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition RawProofFormulaCoverageWithSupport (M : RawPAModel)
    (root coverageBound supportCode supportStep : M) : Prop :=
  RawProofSyntaxCertificateWithSupport M root supportCode supportStep /\
  forall code : M,
    rawLt M code (raw_succ M root) ->
    rawProofCodeSupported M supportCode supportStep code ->
    RawProofEndpointFormulaCoverage M code coverageBound.

Arguments RawProofFormulaCoverageWithSupport
  M root coverageBound supportCode supportStep : clear implicits.

Definition proofFormulaCoverageWithSupportTermAt
    (root coverageBound supportCode supportStep : term) : formula :=
  pAnd
    (proofSyntaxCertificateWithSupportTermAt root supportCode supportStep)
    (pAll
      (pImp
        (Formula.ltTermAt (tVar 0) (liftTerm 1 (tSucc root)))
        (pImp
          (proofCodeSupportedTermAt
            (liftTerm 1 supportCode) (liftTerm 1 supportStep) (tVar 0))
          (proofEndpointFormulaCoverageTermAt
            (tVar 0) (liftTerm 1 coverageBound))))).

Lemma raw_sat_proofFormulaCoverageWithSupportTermAt_iff : forall
    (M : RawPAModel) e root coverageBound supportCode supportStep,
  raw_formula_sat M e
    (proofFormulaCoverageWithSupportTermAt
      root coverageBound supportCode supportStep) <->
  RawProofFormulaCoverageWithSupport M
    (raw_term_eval M e root) (raw_term_eval M e coverageBound)
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep).
Proof.
  intros M e root coverageBound supportCode supportStep.
  unfold proofFormulaCoverageWithSupportTermAt,
    RawProofFormulaCoverageWithSupport.
  cbn [raw_formula_sat].
  rewrite raw_sat_proofSyntaxCertificateWithSupportTermAt_iff.
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_proofCodeSupportedTermAt_iff.
  setoid_rewrite raw_sat_proofEndpointFormulaCoverageTermAt_iff.
  repeat setoid_rewrite raw_proofCoverage_eval_liftTerm_one.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition RawProofFormulaCoverage (M : RawPAModel)
    (root coverageBound : M) : Prop :=
  exists supportCode supportStep : M,
    RawProofFormulaCoverageWithSupport M
      root coverageBound supportCode supportStep.

Arguments RawProofFormulaCoverage M root coverageBound : clear implicits.

Definition proofFormulaCoverageTermAt
    (root coverageBound : term) : formula :=
  proofCoverageEx2
    (proofFormulaCoverageWithSupportTermAt
      (liftTerm 2 root) (liftTerm 2 coverageBound) (tVar 1) (tVar 0)).

Lemma raw_sat_proofFormulaCoverageTermAt_iff : forall
    (M : RawPAModel) e root coverageBound,
  raw_formula_sat M e
    (proofFormulaCoverageTermAt root coverageBound) <->
  RawProofFormulaCoverage M
    (raw_term_eval M e root) (raw_term_eval M e coverageBound).
Proof.
  intros M e root coverageBound.
  unfold proofFormulaCoverageTermAt, proofCoverageEx2,
    RawProofFormulaCoverage.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_proofFormulaCoverageWithSupportTermAt_iff.
  repeat setoid_rewrite raw_proofCoverage_eval_liftTerm_two.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** The root is explicitly marked by its syntax certificate. *)
Theorem raw_proofFormulaCoverage_root_endpoint : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      root coverageBound supportCode supportStep,
  RawProofFormulaCoverageWithSupport M
    root coverageBound supportCode supportStep ->
  RawProofEndpointFormulaCoverage M root coverageBound.
Proof.
  intros M hPA root coverageBound supportCode supportStep
    [[_ hrootSupported] hrows].
  exact (hrows root (raw_assignment_lt_self_succ M hPA root)
    hrootSupported).
Qed.

Corollary raw_proofFormulaCoverage_public_root_endpoint : forall
    (M : RawPAModel), RawPASatisfies M -> forall root coverageBound,
  RawProofFormulaCoverage M root coverageBound ->
  RawProofEndpointFormulaCoverage M root coverageBound.
Proof.
  intros M hPA root coverageBound
    (supportCode & supportStep & hcoverage).
  exact (raw_proofFormulaCoverage_root_endpoint M hPA
    root coverageBound supportCode supportStep hcoverage).
Qed.

(** The same support table can be rerooted at a genuine recursive child.
    Its endpoint rows were already required by the parent's universal
    condition, and the common numeric bound is unchanged. *)
Theorem raw_proofFormulaCoverage_recursive_child : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      root coverageBound supportCode supportStep,
  RawProofFormulaCoverageWithSupport M
    root coverageBound supportCode supportStep ->
  forall context a b c t child1 child2 child3,
  RawProofConstructorCode M
    root context a b c t child1 child2 child3 ->
  forall fields children,
  In (fields, children)
    (rawProofRecursiveCases M
      context a b c t child1 child2 child3) ->
  root = rawListCode M fields ->
  forall child, In child children ->
  RawProofFormulaCoverageWithSupport M
    child coverageBound supportCode supportStep /\
  rawLt M child root.
Proof.
  intros M hPA root coverageBound supportCode supportStep
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

Corollary raw_proofFormulaCoverage_public_recursive_child : forall
    (M : RawPAModel), RawPASatisfies M -> forall root coverageBound,
  RawProofFormulaCoverage M root coverageBound ->
  forall context a b c t child1 child2 child3,
  RawProofConstructorCode M
    root context a b c t child1 child2 child3 ->
  forall fields children,
  In (fields, children)
    (rawProofRecursiveCases M
      context a b c t child1 child2 child3) ->
  root = rawListCode M fields ->
  forall child, In child children ->
  RawProofFormulaCoverage M child coverageBound /\
  rawLt M child root.
Proof.
  intros M hPA root coverageBound
    (supportCode & supportStep & hcoverage)
    context a b c t child1 child2 child3 hconstructor
    fields children hentry hfields child hchild.
  destruct (raw_proofFormulaCoverage_recursive_child M hPA
    root coverageBound supportCode supportStep hcoverage
    context a b c t child1 child2 child3 hconstructor
    fields children hentry hfields child hchild)
    as [hchildCoverage hchildBelow].
  split.
  - exists supportCode, supportStep. exact hchildCoverage.
  - exact hchildBelow.
Qed.

End PABoundedRawCodedProofFormulaCoverage.
