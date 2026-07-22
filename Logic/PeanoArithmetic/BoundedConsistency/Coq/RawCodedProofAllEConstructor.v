(**
  Coverage-certified universal elimination for model-coded PA proofs.

  Both the quantified body and its substitution result may be genuinely
  nonstandard formula codes.  The represented single-substitution graph is
  therefore retained explicitly; no metatheoretic decoding is used.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedAssignment RawCodedSyntaxConstructors RawCodedFormulaOperations
  RawCodedProofConstructors RawCodedProofDescent RawCodedProofTraversal
  RawCodedProofEndpoints RawCodedProofRules RawCodedProofRuleCoverage
  RawCodedListInjectivity RawCodedProofUnaryCoverage.

Import ListNotations.

Module PABoundedRawCodedProofAllEConstructor.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedProofTraversal.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedListInjectivity.
Import PABoundedRawCodedProofUnaryCoverage.

Definition rawProofAllERoot (M : RawPAModel)
    (context body replacement child : M) : M :=
  rawListCode M
    [rawNumeralValue M 12; context; body; replacement; child].

Arguments rawProofAllERoot M context body replacement child
  : clear implicits.

Lemma raw_proofAllERoot_child_lt : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context body replacement child,
  rawLt M child (rawProofAllERoot M context body replacement child).
Proof.
  intros M hPA context body replacement child.
  unfold rawProofAllERoot.
  apply rawProofListCode_member_lt; [exact hPA |].
  cbn. tauto.
Qed.

Lemma raw_proofAllERoot_list_view : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context body replacement child tag payload,
  rawProofAllERoot M context body replacement child =
    rawListCode M (rawNumeralValue M tag :: payload) ->
  tag = 12 /\ payload = [context; body; replacement; child].
Proof.
  intros M hPA context body replacement child tag payload hcode.
  unfold rawProofAllERoot in hcode.
  pose proof (rawListCode_injective M hPA
    [rawNumeralValue M 12; context; body; replacement; child]
    (rawNumeralValue M tag :: payload) hcode) as hfields.
  assert (hhead : rawNumeralValue M 12 = rawNumeralValue M tag).
  { now inversion hfields. }
  assert (htail : [context; body; replacement; child] = payload).
  { now inversion hfields. }
  split.
  - symmetry. exact (rawNumeralValue_injective M hPA _ _ hhead).
  - symmetry. exact htail.
Qed.

Lemma raw_proofAllERoot_recursive_children : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context body replacement child
      rowContext a b c t child1 child2 child3 fields children,
  In (fields, children)
    (rawProofRecursiveCases M
      rowContext a b c t child1 child2 child3) ->
  rawProofAllERoot M context body replacement child =
    rawListCode M fields ->
  children = [child].
Proof.
  intros M hPA context body replacement child
    rowContext a b c t child1 child2 child3 fields children
    hentry hcode.
  unfold rawProofRecursiveCases in hentry. cbn in hentry.
  repeat match type of hentry with
  | _ \/ _ => destruct hentry as [hentry | hentry]
  end; try contradiction.
  all: inversion hentry; subst fields children; clear hentry.
  all: unfold rawProofAllERoot in hcode.
  all: pose proof (rawListCode_injective M hPA _ _ hcode) as hfields.
  all: try discriminate hfields.
  all: inversion hfields; reflexivity.
Qed.

Lemma raw_proofAllE_syntax_step : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context body replacement child supportCode supportStep,
  rawProofCodeSupported M supportCode supportStep child ->
  RawProofSyntaxStep M
    (rawProofAllERoot M context body replacement child)
    supportCode supportStep.
Proof.
  intros M hPA context body replacement child
    supportCode supportStep hchildSupported.
  split.
  - exists context, body, (raw_zero M), (raw_zero M), replacement,
      child, (raw_zero M), (raw_zero M).
    unfold RawProofConstructorCode, rawProofAllERoot.
    do 12 right. left. reflexivity.
  - intros rowContext a b c t child1 child2 child3 hconstructor.
    split.
    + exact (raw_proofConstructorCode_descent M hPA
        (rawProofAllERoot M context body replacement child)
        rowContext a b c t child1 child2 child3 hconstructor).
    + apply Forall_forall. intros [fields children] hentry.
      unfold RawProofChildrenClosedCase.
      intro hcode.
      pose proof (raw_proofAllERoot_recursive_children M hPA
        context body replacement child
        rowContext a b c t child1 child2 child3 fields children
        hentry hcode) as ->.
      constructor.
      * split; [exact hchildSupported |].
        exact (raw_proofAllERoot_child_lt M hPA
          context body replacement child).
      * constructor.
Qed.

(** Endpoint completeness uses the substitution graph carried by each
    endpoint view itself.  Hence functionality of substitution is not needed
    merely to certify the proof rule. *)
Lemma raw_proofAllE_endpoint_rule_complete : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context body replacement child,
  RawProofEndpoint M child context (rawFormulaAllCode M body) ->
  RawProofEndpointRuleComplete M
    (rawProofAllERoot M context body replacement child).
Proof.
  intros M hPA context body replacement child hchildEndpoint
    endpointContext endpointConclusion hendpoint.
  destruct hendpoint as
    (rowContext & a & b & c & t & child1 & child2 & child3 &
      hcontext & hcases).
  subst rowContext.
  unfold RawProofEndpointCases in hcases.
  repeat match type of hcases with
  | _ \/ _ => destruct hcases as [hcases | hcases]
  end; try contradiction.
  all: destruct hcases as [hhead hrest].
  all: pose proof (raw_proofAllERoot_list_view M hPA
    context body replacement child _ _ hhead) as hview.
  all: destruct hview as [htag hpayload].
  all: try discriminate htag.
  inversion hpayload; subst endpointContext a t child1.
  exists context, body, (rawFormulaAllCode M body),
    (raw_zero M), replacement, child, (raw_zero M), (raw_zero M).
  split; [reflexivity |].
  unfold RawProofRuleValidCases, rawProofAllERoot.
  do 12 right. left.
  repeat split; assumption || reflexivity.
Qed.

Lemma raw_proofAllE_endpoint : forall
    (M : RawPAModel) context body replacement conclusion child,
  RawCodedFormulaSingleSubstitution M replacement body conclusion ->
  RawProofEndpoint M
    (rawProofAllERoot M context body replacement child)
    context conclusion.
Proof.
  intros M context body replacement conclusion child hsubstitution.
  exists context, body, (raw_zero M), (raw_zero M), replacement,
    child, (raw_zero M), (raw_zero M).
  split; [reflexivity |].
  unfold RawProofEndpointCases, rawProofAllERoot.
  do 12 right. left. split; [reflexivity | exact hsubstitution].
Qed.

Theorem raw_proofAllE_ruleCoverage : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context body replacement child,
  RawProofRuleCoverage M child ->
  RawProofEndpoint M child context (rawFormulaAllCode M body) ->
  RawProofRuleCoverage M
    (rawProofAllERoot M context body replacement child).
Proof.
  intros M hPA context body replacement child
    hchildCoverage hchildEndpoint.
  exact (raw_proofUnary_ruleCoverage M hPA child
    (rawProofAllERoot M context body replacement child)
    hchildCoverage
    (raw_proofAllERoot_child_lt M hPA
      context body replacement child)
    (raw_proofAllE_syntax_step M hPA
      context body replacement child)
    (raw_proofAllE_endpoint_rule_complete M hPA
      context body replacement child hchildEndpoint)).
Qed.

End PABoundedRawCodedProofAllEConstructor.
