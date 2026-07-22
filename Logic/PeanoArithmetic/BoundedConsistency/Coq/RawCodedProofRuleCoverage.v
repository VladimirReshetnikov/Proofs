(**
  Proof-wide validity for every advertised endpoint of a raw proof code.

  A constructor code normally determines its context and conclusion.  For
  the two constructors whose conclusion is produced by the arithmetized
  substitution graph, however, using that fact in a nonstandard model would
  require a separate cross-trace functionality theorem.  Soundness does not
  need to take that detour.  Instead, the proof certificate can state the
  exact property it uses: every endpoint advertised by every supported node
  satisfies the complete local rule graph at that same endpoint.

  The property below is represented by a PA formula and shares its support
  table with a complete proof-syntax certificate.  It therefore reaches all
  recursive children, including nonstandard ones, and reroots without
  changing tables.  Standard quoted proofs satisfy the property because
  their endpoint graph is functional against the external quotation.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import ListCode Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  PolynomialPairInjectivity RawCodedSyntaxConstructors RawCodedAssignment
  RawCodedProofConstructors RawCodedProofDescent
  RawCodedProofTraversal RawCodedProofEndpoints RawCodedProofRules
  RawCodedProofFormulaCoverage.

Module PABoundedRawCodedProofRuleCoverage.

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
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedProofTraversal.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedProofFormulaCoverage.

Definition proofRuleCoverageEx2 (body : formula) : formula :=
  pEx (pEx body).

(** One node is complete when every endpoint view, rather than merely one
    existentially selected endpoint, is accepted by the local rule graph. *)
Definition RawProofEndpointRuleComplete (M : RawPAModel)
    (code : M) : Prop :=
  forall context conclusion : M,
    RawProofEndpoint M code context conclusion ->
    RawProofRuleValid M code context conclusion.

Arguments RawProofEndpointRuleComplete M code : clear implicits.

Definition proofEndpointRuleCompleteTermAt (code : term) : formula :=
  pAll (pAll
    (pImp
      (proofEndpointTermAt (liftTerm 2 code) (tVar 1) (tVar 0))
      (proofRuleValidTermAt (liftTerm 2 code) (tVar 1) (tVar 0)))).

Lemma raw_sat_proofEndpointRuleCompleteTermAt_iff : forall
    (M : RawPAModel) e code,
  raw_formula_sat M e (proofEndpointRuleCompleteTermAt code) <->
  RawProofEndpointRuleComplete M (raw_term_eval M e code).
Proof.
  intros M e code.
  unfold proofEndpointRuleCompleteTermAt,
    RawProofEndpointRuleComplete.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_proofEndpointTermAt_iff.
  setoid_rewrite raw_sat_proofRuleValidTermAt_iff.
  repeat setoid_rewrite raw_proofCoverage_eval_liftTerm_two.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** The support table is deliberately bundled with a complete syntax
    certificate.  Thus a universal endpoint-validity row cannot omit a
    recursive child by choosing an incomplete support predicate. *)
Definition RawProofRuleCoverageWithSupport (M : RawPAModel)
    (root supportCode supportStep : M) : Prop :=
  RawProofSyntaxCertificateWithSupport M root supportCode supportStep /\
  forall code : M,
    rawLt M code (raw_succ M root) ->
    rawProofCodeSupported M supportCode supportStep code ->
    RawProofEndpointRuleComplete M code.

Arguments RawProofRuleCoverageWithSupport
  M root supportCode supportStep : clear implicits.

Definition proofRuleCoverageWithSupportTermAt
    (root supportCode supportStep : term) : formula :=
  pAnd
    (proofSyntaxCertificateWithSupportTermAt root supportCode supportStep)
    (pAll
      (pImp
        (Formula.ltTermAt (tVar 0) (liftTerm 1 (tSucc root)))
        (pImp
          (proofCodeSupportedTermAt
            (liftTerm 1 supportCode) (liftTerm 1 supportStep) (tVar 0))
          (proofEndpointRuleCompleteTermAt (tVar 0))))).

Lemma raw_sat_proofRuleCoverageWithSupportTermAt_iff : forall
    (M : RawPAModel) e root supportCode supportStep,
  raw_formula_sat M e
    (proofRuleCoverageWithSupportTermAt root supportCode supportStep) <->
  RawProofRuleCoverageWithSupport M
    (raw_term_eval M e root)
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep).
Proof.
  intros M e root supportCode supportStep.
  unfold proofRuleCoverageWithSupportTermAt,
    RawProofRuleCoverageWithSupport.
  cbn [raw_formula_sat].
  rewrite raw_sat_proofSyntaxCertificateWithSupportTermAt_iff.
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_proofCodeSupportedTermAt_iff.
  setoid_rewrite raw_sat_proofEndpointRuleCompleteTermAt_iff.
  repeat setoid_rewrite raw_proofCoverage_eval_liftTerm_one.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition RawProofRuleCoverage (M : RawPAModel) (root : M) : Prop :=
  exists supportCode supportStep : M,
    RawProofRuleCoverageWithSupport M root supportCode supportStep.

Arguments RawProofRuleCoverage M root : clear implicits.

Definition proofRuleCoverageTermAt (root : term) : formula :=
  proofRuleCoverageEx2
    (proofRuleCoverageWithSupportTermAt
      (liftTerm 2 root) (tVar 1) (tVar 0)).

Lemma raw_sat_proofRuleCoverageTermAt_iff : forall
    (M : RawPAModel) e root,
  raw_formula_sat M e (proofRuleCoverageTermAt root) <->
  RawProofRuleCoverage M (raw_term_eval M e root).
Proof.
  intros M e root.
  unfold proofRuleCoverageTermAt, proofRuleCoverageEx2,
    RawProofRuleCoverage.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_proofRuleCoverageWithSupportTermAt_iff.
  repeat setoid_rewrite raw_proofCoverage_eval_liftTerm_two.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** The root is marked by the syntax certificate, so its exact advertised
    endpoint immediately has a valid rule row. *)
Theorem raw_proofRuleCoverage_root_complete : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      root supportCode supportStep,
  RawProofRuleCoverageWithSupport M root supportCode supportStep ->
  RawProofEndpointRuleComplete M root.
Proof.
  intros M hPA root supportCode supportStep
    [[_ hrootSupported] hrows].
  exact (hrows root (raw_assignment_lt_self_succ M hPA root)
    hrootSupported).
Qed.

Corollary raw_proofRuleCoverage_public_root_complete : forall
    (M : RawPAModel), RawPASatisfies M -> forall root,
  RawProofRuleCoverage M root ->
  RawProofEndpointRuleComplete M root.
Proof.
  intros M hPA root (supportCode & supportStep & hcoverage).
  exact (raw_proofRuleCoverage_root_complete M hPA
    root supportCode supportStep hcoverage).
Qed.

(** Recursive descent preserves the same support table and all of its
    endpoint-validity rows.  Only the syntax-certificate root changes. *)
Theorem raw_proofRuleCoverage_recursive_child : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      root supportCode supportStep,
  RawProofRuleCoverageWithSupport M root supportCode supportStep ->
  forall context a b c t child1 child2 child3,
  RawProofConstructorCode M
    root context a b c t child1 child2 child3 ->
  forall fields children,
  In (fields, children)
    (rawProofRecursiveCases M
      context a b c t child1 child2 child3) ->
  root = rawListCode M fields ->
  forall child, In child children ->
  RawProofRuleCoverageWithSupport M child supportCode supportStep /\
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

Corollary raw_proofRuleCoverage_public_recursive_child : forall
    (M : RawPAModel), RawPASatisfies M -> forall root,
  RawProofRuleCoverage M root ->
  forall context a b c t child1 child2 child3,
  RawProofConstructorCode M
    root context a b c t child1 child2 child3 ->
  forall fields children,
  In (fields, children)
    (rawProofRecursiveCases M
      context a b c t child1 child2 child3) ->
  root = rawListCode M fields ->
  forall child, In child children ->
  RawProofRuleCoverage M child /\ rawLt M child root.
Proof.
  intros M hPA root (supportCode & supportStep & hcoverage)
    context a b c t child1 child2 child3 hconstructor
    fields children hentry hfields child hchild.
  destruct (raw_proofRuleCoverage_recursive_child M hPA
    root supportCode supportStep hcoverage
    context a b c t child1 child2 child3 hconstructor
    fields children hentry hfields child hchild)
    as [hchildCoverage hchildBelow].
  split.
  - exists supportCode, supportStep. exact hchildCoverage.
  - exact hchildBelow.
Qed.

End PABoundedRawCodedProofRuleCoverage.
