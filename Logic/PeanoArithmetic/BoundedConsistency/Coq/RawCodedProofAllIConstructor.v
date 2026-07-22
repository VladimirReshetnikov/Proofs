(**
  Coverage-certified universal introduction for model-coded PA proofs.

  Universal introduction is unary at the proof-tree level but carries the
  eigenvariable context side condition: the premise context must be the
  pointwise de Bruijn shift of the conclusion context.  This module keeps
  that [RawContextShift] witness explicit and uses the exact unary support
  extension to retain the premise tree beneath the new [RP_allI] root.
*)

From Stdlib Require Import List Arith Lia.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedAssignment RawCodedSyntaxConstructors RawCodedContextShift
  RawCodedProofConstructors RawCodedProofDescent RawCodedProofTraversal
  RawCodedProofEndpoints RawCodedProofRules RawCodedProofRuleCoverage
  RawCodedListInjectivity RawCodedProofSupportExtension.

Import ListNotations.

Module PABoundedRawCodedProofAllIConstructor.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedProofTraversal.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedListInjectivity.
Import PABoundedRawCodedProofSupportExtension.

Definition rawProofAllIRoot
    (M : RawPAModel) (context body child : M) : M :=
  rawListCode M [rawNumeralValue M 11; context; body; child].

Arguments rawProofAllIRoot M context body child : clear implicits.

Lemma raw_proofAllIRoot_child_lt : forall
    (M : RawPAModel), RawPASatisfies M -> forall context body child,
  rawLt M child (rawProofAllIRoot M context body child).
Proof.
  intros M hPA context body child.
  unfold rawProofAllIRoot.
  apply rawProofListCode_member_lt; [exact hPA |].
  cbn. tauto.
Qed.

Lemma raw_proofAllIRoot_list_view : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context body child tag payload,
  rawProofAllIRoot M context body child =
    rawListCode M (rawNumeralValue M tag :: payload) ->
  tag = 11 /\ payload = [context; body; child].
Proof.
  intros M hPA context body child tag payload hcode.
  unfold rawProofAllIRoot in hcode.
  pose proof (rawListCode_injective M hPA
    [rawNumeralValue M 11; context; body; child]
    (rawNumeralValue M tag :: payload) hcode) as hfields.
  assert (hhead : rawNumeralValue M 11 = rawNumeralValue M tag).
  { now inversion hfields. }
  assert (htail : [context; body; child] = payload).
  { now inversion hfields. }
  split.
  - symmetry. exact (rawNumeralValue_injective M hPA _ _ hhead).
  - symmetry. exact htail.
Qed.

Lemma raw_proofAllIRoot_recursive_children : forall
    (M : RawPAModel), RawPASatisfies M -> forall context body child
      rowContext a b c t child1 child2 child3 fields children,
  In (fields, children)
    (rawProofRecursiveCases M
      rowContext a b c t child1 child2 child3) ->
  rawProofAllIRoot M context body child = rawListCode M fields ->
  children = [child].
Proof.
  intros M hPA context body child rowContext a b c t
    child1 child2 child3 fields children hentry hcode.
  unfold rawProofRecursiveCases in hentry. cbn in hentry.
  repeat match type of hentry with
  | _ \/ _ => destruct hentry as [hentry | hentry]
  end; try contradiction.
  all: inversion hentry; subst fields children; clear hentry.
  all: unfold rawProofAllIRoot in hcode.
  all: pose proof (rawListCode_injective M hPA _ _ hcode) as hfields.
  all: try discriminate hfields.
  all: inversion hfields; reflexivity.
Qed.

Lemma raw_proofAllI_syntax_step : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context body child supportCode supportStep,
  rawProofCodeSupported M supportCode supportStep child ->
  RawProofSyntaxStep M
    (rawProofAllIRoot M context body child) supportCode supportStep.
Proof.
  intros M hPA context body child supportCode supportStep hchildSupported.
  split.
  - exists context, body,
      (raw_zero M), (raw_zero M), (raw_zero M), child,
      (raw_zero M), (raw_zero M).
    unfold RawProofConstructorCode, rawProofAllIRoot.
    right. right. right. right. right. right. right. right. right.
    right. right. left. reflexivity.
  - intros rowContext a b c t child1 child2 child3 hconstructor.
    split.
    + exact (raw_proofConstructorCode_descent M hPA
        (rawProofAllIRoot M context body child)
        rowContext a b c t child1 child2 child3 hconstructor).
    + apply Forall_forall. intros [fields children] hentry.
      unfold RawProofChildrenClosedCase.
      intro hcode.
      pose proof (raw_proofAllIRoot_recursive_children M hPA
        context body child rowContext a b c t
        child1 child2 child3 fields children hentry hcode) as ->.
      constructor.
      * split; [exact hchildSupported |].
        exact (raw_proofAllIRoot_child_lt M hPA context body child).
      * constructor.
Qed.

Lemma raw_proofAllI_endpoint_rule_complete : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context shiftedContext body child,
  RawContextShift M context shiftedContext ->
  RawProofEndpoint M child shiftedContext body ->
  RawProofEndpointRuleComplete M
    (rawProofAllIRoot M context body child).
Proof.
  intros M hPA context shiftedContext body child
    hcontextShift hchildEndpoint
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
  all: pose proof (raw_proofAllIRoot_list_view M hPA
    context body child _ _ hhead) as hview.
  all: destruct hview as [htag hpayload].
  all: try discriminate htag.
  inversion hpayload; subst endpointContext a child1.
  subst endpointConclusion.
  exists context, body, shiftedContext,
    (raw_zero M), (raw_zero M), child,
    (raw_zero M), (raw_zero M).
  split; [reflexivity |].
  unfold RawProofRuleValidCases, rawProofAllIRoot.
  eauto 30.
Qed.

Corollary raw_proofAllI_endpoint : forall
    (M : RawPAModel) context body child,
  RawProofEndpoint M
    (rawProofAllIRoot M context body child)
    context (rawFormulaAllCode M body).
Proof.
  intros M context body child.
  exists context, body,
    (raw_zero M), (raw_zero M), (raw_zero M), child,
    (raw_zero M), (raw_zero M).
  split; [reflexivity |].
  unfold RawProofEndpointCases, rawProofAllIRoot.
  right. right. right. right. right. right. right. right. right.
  right. right. left.
  split; reflexivity.
Qed.

Theorem raw_proofAllI_ruleCoverage : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context shiftedContext body child,
  RawContextShift M context shiftedContext ->
  RawProofRuleCoverage M child ->
  RawProofEndpoint M child shiftedContext body ->
  RawProofRuleCoverage M (rawProofAllIRoot M context body child).
Proof.
  intros M hPA context shiftedContext body child hcontextShift
    (oldCode & oldStep & [[[holdDefined holdRows] hchildOldSupported]
      holdEndpointRows])
    hchildEndpoint.
  set (parent := rawProofAllIRoot M context body child).
  destruct (raw_proofSupportExtension_to_parent M hPA
    child oldCode oldStep parent)
    as (newCode & newStep & [hnewDefined hnewExact]).
  assert (hchildBelow : rawLt M child parent).
  {
    unfold parent.
    exact (raw_proofAllIRoot_child_lt M hPA context body child).
  }
  assert (hchildBelowBound : rawLt M child (raw_succ M parent)).
  {
    exact (raw_assignment_lt_trans M hPA
      child parent (raw_succ M parent)
      hchildBelow (raw_assignment_lt_self_succ M hPA parent)).
  }
  assert (hchildNewSupported :
      rawProofCodeSupported M newCode newStep child).
  {
    apply (proj2 (hnewExact child hchildBelowBound)).
    left. split.
    - exact (raw_assignment_lt_self_succ M hPA child).
    - exact hchildOldSupported.
  }
  exists newCode, newStep. split.
  - split.
    + split; [exact hnewDefined |].
      intros code hbelow hsupported.
      pose proof (proj1 (hnewExact code hbelow) hsupported) as hshape.
      destruct hshape as [[hbelowChild holdSupported] | ->].
      * exact (raw_proofSyntaxStep_support_extension M hPA
          child oldCode oldStep parent newCode newStep code
          (conj hnewDefined hnewExact)
          (holdRows code hbelowChild holdSupported)
          hbelowChild hbelow).
      * unfold parent.
        exact (raw_proofAllI_syntax_step M hPA
          context body child newCode newStep hchildNewSupported).
    + apply (proj2 (hnewExact parent
        (raw_assignment_lt_self_succ M hPA parent))).
      right. reflexivity.
  - intros code hbelow hsupported.
    pose proof (proj1 (hnewExact code hbelow) hsupported) as hshape.
    destruct hshape as [[hbelowChild holdSupported] | ->].
    + exact (holdEndpointRows code hbelowChild holdSupported).
    + unfold parent.
      exact (raw_proofAllI_endpoint_rule_complete M hPA
        context shiftedContext body child
        hcontextShift hchildEndpoint).
Qed.

End PABoundedRawCodedProofAllIConstructor.
