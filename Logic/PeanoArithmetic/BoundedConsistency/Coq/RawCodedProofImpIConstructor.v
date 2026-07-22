(**
  Coverage-certified implication introduction for model-coded PA proofs.

  The premise tree is rooted in the context obtained by adjoining the
  antecedent to the parent's context.  As with bottom elimination, an exact
  unary support extension retains the entire premise tree and adds only the
  new parent, even when all relevant codes are nonstandard model elements.
*)

From Stdlib Require Import List Arith Lia.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedAssignment RawCodedSyntaxConstructors
  RawCodedProofConstructors RawCodedProofDescent RawCodedProofTraversal
  RawCodedProofEndpoints RawCodedProofRules RawCodedProofRuleCoverage
  RawCodedListInjectivity RawCodedProofSupportExtension.

Import ListNotations.

Module PABoundedRawCodedProofImpIConstructor.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedProofTraversal.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedListInjectivity.
Import PABoundedRawCodedProofSupportExtension.

Definition rawProofImpIRoot (M : RawPAModel)
    (context antecedent consequent child : M) : M :=
  rawListCode M
    [rawNumeralValue M 1; context; antecedent; consequent; child].

Arguments rawProofImpIRoot
  M context antecedent consequent child : clear implicits.

Lemma raw_proofImpIRoot_child_lt : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context antecedent consequent child,
  rawLt M child
    (rawProofImpIRoot M context antecedent consequent child).
Proof.
  intros M hPA context antecedent consequent child.
  unfold rawProofImpIRoot.
  apply rawProofListCode_member_lt; [exact hPA |].
  cbn. tauto.
Qed.

Lemma raw_proofImpIRoot_list_view : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context antecedent consequent child tag payload,
  rawProofImpIRoot M context antecedent consequent child =
    rawListCode M (rawNumeralValue M tag :: payload) ->
  tag = 1 /\ payload = [context; antecedent; consequent; child].
Proof.
  intros M hPA context antecedent consequent child tag payload hcode.
  unfold rawProofImpIRoot in hcode.
  pose proof (rawListCode_injective M hPA
    [rawNumeralValue M 1; context; antecedent; consequent; child]
    (rawNumeralValue M tag :: payload) hcode) as hfields.
  assert (hhead : rawNumeralValue M 1 = rawNumeralValue M tag).
  { now inversion hfields. }
  assert (htail : [context; antecedent; consequent; child] = payload).
  { now inversion hfields. }
  split.
  - symmetry. exact (rawNumeralValue_injective M hPA _ _ hhead).
  - symmetry. exact htail.
Qed.

Lemma raw_proofImpIRoot_recursive_children : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context antecedent consequent child
      rowContext a b c t child1 child2 child3 fields children,
  In (fields, children)
    (rawProofRecursiveCases M
      rowContext a b c t child1 child2 child3) ->
  rawProofImpIRoot M context antecedent consequent child =
    rawListCode M fields ->
  children = [child].
Proof.
  intros M hPA context antecedent consequent child
    rowContext a b c t child1 child2 child3 fields children
    hentry hcode.
  unfold rawProofRecursiveCases in hentry. cbn in hentry.
  repeat match type of hentry with
  | _ \/ _ => destruct hentry as [hentry | hentry]
  end; try contradiction.
  all: inversion hentry; subst fields children; clear hentry.
  all: unfold rawProofImpIRoot in hcode.
  all: pose proof (rawListCode_injective M hPA _ _ hcode) as hfields.
  all: try discriminate hfields.
  all: inversion hfields; reflexivity.
Qed.

Lemma raw_proofImpI_syntax_step : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context antecedent consequent child supportCode supportStep,
  rawProofCodeSupported M supportCode supportStep child ->
  RawProofSyntaxStep M
    (rawProofImpIRoot M context antecedent consequent child)
    supportCode supportStep.
Proof.
  intros M hPA context antecedent consequent child supportCode supportStep
    hchildSupported.
  split.
  - exists context, antecedent, consequent,
      (raw_zero M), (raw_zero M), child,
      (raw_zero M), (raw_zero M).
    unfold RawProofConstructorCode, rawProofImpIRoot.
    right. left. reflexivity.
  - intros rowContext a b c t child1 child2 child3 hconstructor.
    split.
    + exact (raw_proofConstructorCode_descent M hPA
        (rawProofImpIRoot M context antecedent consequent child)
        rowContext a b c t child1 child2 child3 hconstructor).
    + apply Forall_forall. intros [fields children] hentry.
      unfold RawProofChildrenClosedCase.
      intro hcode.
      pose proof (raw_proofImpIRoot_recursive_children M hPA
        context antecedent consequent child
        rowContext a b c t child1 child2 child3 fields children
        hentry hcode) as ->.
      constructor.
      * split; [exact hchildSupported |].
        exact (raw_proofImpIRoot_child_lt M hPA
          context antecedent consequent child).
      * constructor.
Qed.

Lemma raw_proofImpI_endpoint_rule_complete : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context antecedent consequent child,
  RawProofEndpoint M child
    (rawListNode M antecedent context) consequent ->
  RawProofEndpointRuleComplete M
    (rawProofImpIRoot M context antecedent consequent child).
Proof.
  intros M hPA context antecedent consequent child hchildEndpoint
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
  all: pose proof (raw_proofImpIRoot_list_view M hPA
    context antecedent consequent child _ _ hhead) as hview.
  all: destruct hview as [htag hpayload].
  all: try discriminate htag.
  inversion hpayload; subst endpointContext a b child1.
  subst endpointConclusion.
  exists context, antecedent, consequent,
    (raw_zero M), (raw_zero M), child,
    (raw_zero M), (raw_zero M).
  split; [reflexivity |].
  unfold RawProofRuleValidCases, rawProofImpIRoot.
  right. left.
  repeat split; assumption || reflexivity.
Qed.

Corollary raw_proofImpI_endpoint : forall
    (M : RawPAModel) context antecedent consequent child,
  RawProofEndpoint M
    (rawProofImpIRoot M context antecedent consequent child)
    context (rawFormulaImpCode M antecedent consequent).
Proof.
  intros M context antecedent consequent child.
  exists context, antecedent, consequent,
    (raw_zero M), (raw_zero M), child,
    (raw_zero M), (raw_zero M).
  split; [reflexivity |].
  unfold RawProofEndpointCases, rawProofImpIRoot.
  right. left.
  split; reflexivity.
Qed.

Theorem raw_proofImpI_ruleCoverage : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context antecedent consequent child,
  RawProofRuleCoverage M child ->
  RawProofEndpoint M child
    (rawListNode M antecedent context) consequent ->
  RawProofRuleCoverage M
    (rawProofImpIRoot M context antecedent consequent child).
Proof.
  intros M hPA context antecedent consequent child
    (oldCode & oldStep & [[[holdDefined holdRows] hchildOldSupported]
      holdEndpointRows])
    hchildEndpoint.
  set (parent := rawProofImpIRoot M context antecedent consequent child).
  destruct (raw_proofSupportExtension_to_parent M hPA
    child oldCode oldStep parent)
    as (newCode & newStep & [hnewDefined hnewExact]).
  assert (hchildBelow : rawLt M child parent).
  {
    unfold parent.
    exact (raw_proofImpIRoot_child_lt M hPA
      context antecedent consequent child).
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
        exact (raw_proofImpI_syntax_step M hPA
          context antecedent consequent child
          newCode newStep hchildNewSupported).
    + apply (proj2 (hnewExact parent
        (raw_assignment_lt_self_succ M hPA parent))).
      right. reflexivity.
  - intros code hbelow hsupported.
    pose proof (proj1 (hnewExact code hbelow) hsupported) as hshape.
    destruct hshape as [[hbelowChild holdSupported] | ->].
    + exact (holdEndpointRows code hbelowChild holdSupported).
    + unfold parent.
      exact (raw_proofImpI_endpoint_rule_complete M hPA
        context antecedent consequent child hchildEndpoint).
Qed.

End PABoundedRawCodedProofImpIConstructor.
