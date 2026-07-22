(**
  Coverage-certified binary constructors for model-coded PA proofs.

  Implication elimination is the first genuine proof-tree composition
  operation used by the uniform compiler.  Its two premise certificates may
  carry unrelated nonstandard support assignments.  The exact binary union
  table retains both trees and adds one parent, while constructor injectivity
  proves that every view of that parent names precisely those two children.
*)

From Stdlib Require Import List Arith Lia.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedAssignment RawCodedSyntaxConstructors
  RawCodedProofConstructors RawCodedProofDescent RawCodedProofTraversal
  RawCodedProofEndpoints RawCodedProofRules RawCodedProofRuleCoverage
  RawCodedListInjectivity RawCodedProofSupportExtension
  RawCodedProofBinarySupportUnion.

Import ListNotations.

Module PABoundedRawCodedProofBinaryConstructors.

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
Import PABoundedRawCodedProofBinarySupportUnion.

Definition rawProofImpERoot (M : RawPAModel)
    (context antecedent consequent impChild antecedentChild : M) : M :=
  rawListCode M
    [rawNumeralValue M 2; context; antecedent; consequent;
      impChild; antecedentChild].

Arguments rawProofImpERoot
  M context antecedent consequent impChild antecedentChild
  : clear implicits.

Lemma raw_proofImpERoot_imp_child_lt : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context antecedent consequent impChild antecedentChild,
  rawLt M impChild
    (rawProofImpERoot M context antecedent consequent
      impChild antecedentChild).
Proof.
  intros M hPA context antecedent consequent impChild antecedentChild.
  unfold rawProofImpERoot.
  apply rawProofListCode_member_lt; [exact hPA |].
  cbn. tauto.
Qed.

Lemma raw_proofImpERoot_antecedent_child_lt : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context antecedent consequent impChild antecedentChild,
  rawLt M antecedentChild
    (rawProofImpERoot M context antecedent consequent
      impChild antecedentChild).
Proof.
  intros M hPA context antecedent consequent impChild antecedentChild.
  unfold rawProofImpERoot.
  apply rawProofListCode_member_lt; [exact hPA |].
  cbn. tauto.
Qed.

Lemma raw_proofImpERoot_list_view : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context antecedent consequent impChild antecedentChild tag payload,
  rawProofImpERoot M context antecedent consequent
      impChild antecedentChild =
    rawListCode M (rawNumeralValue M tag :: payload) ->
  tag = 2 /\
  payload =
    [context; antecedent; consequent; impChild; antecedentChild].
Proof.
  intros M hPA context antecedent consequent impChild antecedentChild
    tag payload hcode.
  unfold rawProofImpERoot in hcode.
  pose proof (rawListCode_injective M hPA
    [rawNumeralValue M 2; context; antecedent; consequent;
      impChild; antecedentChild]
    (rawNumeralValue M tag :: payload) hcode) as hfields.
  assert (hhead : rawNumeralValue M 2 = rawNumeralValue M tag).
  { now inversion hfields. }
  assert (htail :
      [context; antecedent; consequent; impChild; antecedentChild] =
      payload).
  { now inversion hfields. }
  split.
  - symmetry. exact (rawNumeralValue_injective M hPA _ _ hhead).
  - symmetry. exact htail.
Qed.

Lemma raw_proofImpERoot_recursive_children : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context antecedent consequent impChild antecedentChild
      rowContext a b c t child1 child2 child3 fields children,
  In (fields, children)
    (rawProofRecursiveCases M
      rowContext a b c t child1 child2 child3) ->
  rawProofImpERoot M context antecedent consequent
      impChild antecedentChild = rawListCode M fields ->
  children = [impChild; antecedentChild].
Proof.
  intros M hPA context antecedent consequent impChild antecedentChild
    rowContext a b c t child1 child2 child3 fields children
    hentry hcode.
  unfold rawProofRecursiveCases in hentry. cbn in hentry.
  repeat match type of hentry with
  | _ \/ _ => destruct hentry as [hentry | hentry]
  end; try contradiction.
  all: inversion hentry; subst fields children; clear hentry.
  all: unfold rawProofImpERoot in hcode.
  all: pose proof (rawListCode_injective M hPA _ _ hcode) as hfields.
  all: try discriminate hfields.
  all: inversion hfields; reflexivity.
Qed.

Lemma raw_proofImpE_syntax_step : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context antecedent consequent impChild antecedentChild
      supportCode supportStep,
  rawProofCodeSupported M supportCode supportStep impChild ->
  rawProofCodeSupported M supportCode supportStep antecedentChild ->
  RawProofSyntaxStep M
    (rawProofImpERoot M context antecedent consequent
      impChild antecedentChild)
    supportCode supportStep.
Proof.
  intros M hPA context antecedent consequent impChild antecedentChild
    supportCode supportStep himpSupported hantecedentSupported.
  split.
  - exists context, antecedent, consequent,
      (raw_zero M), (raw_zero M), impChild, antecedentChild,
      (raw_zero M).
    unfold RawProofConstructorCode, rawProofImpERoot.
    right. right. left. reflexivity.
  - intros rowContext a b c t child1 child2 child3 hconstructor.
    split.
    + exact (raw_proofConstructorCode_descent M hPA
        (rawProofImpERoot M context antecedent consequent
          impChild antecedentChild)
        rowContext a b c t child1 child2 child3 hconstructor).
    + apply Forall_forall. intros [fields children] hentry.
      unfold RawProofChildrenClosedCase.
      intro hcode.
      pose proof (raw_proofImpERoot_recursive_children M hPA
        context antecedent consequent impChild antecedentChild
        rowContext a b c t child1 child2 child3 fields children
        hentry hcode) as ->.
      constructor.
      * split; [exact himpSupported |].
        exact (raw_proofImpERoot_imp_child_lt M hPA
          context antecedent consequent impChild antecedentChild).
      * constructor.
        -- split; [exact hantecedentSupported |].
           exact (raw_proofImpERoot_antecedent_child_lt M hPA
             context antecedent consequent impChild antecedentChild).
        -- constructor.
Qed.

Lemma raw_proofImpE_endpoint_rule_complete : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context antecedent consequent impChild antecedentChild,
  RawProofEndpoint M impChild context
    (rawFormulaImpCode M antecedent consequent) ->
  RawProofEndpoint M antecedentChild context antecedent ->
  RawProofEndpointRuleComplete M
    (rawProofImpERoot M context antecedent consequent
      impChild antecedentChild).
Proof.
  intros M hPA context antecedent consequent impChild antecedentChild
    himpEndpoint hantecedentEndpoint
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
  all: pose proof (raw_proofImpERoot_list_view M hPA
    context antecedent consequent impChild antecedentChild
    _ _ hhead) as hview.
  all: destruct hview as [htag hpayload].
  all: try discriminate htag.
  inversion hpayload; subst endpointContext a b child1 child2.
  subst endpointConclusion.
  exists context, antecedent, consequent,
    (rawFormulaImpCode M antecedent consequent),
    (raw_zero M), impChild, antecedentChild, (raw_zero M).
  split; [reflexivity |].
  unfold RawProofRuleValidCases, rawProofImpERoot.
  right. right. left.
  repeat split; assumption || reflexivity.
Qed.

Corollary raw_proofImpE_endpoint : forall
    (M : RawPAModel) context antecedent consequent
      impChild antecedentChild,
  RawProofEndpoint M
    (rawProofImpERoot M context antecedent consequent
      impChild antecedentChild)
    context consequent.
Proof.
  intros M context antecedent consequent impChild antecedentChild.
  exists context, antecedent, consequent,
    (raw_zero M), (raw_zero M), impChild, antecedentChild,
    (raw_zero M).
  split; [reflexivity |].
  unfold RawProofEndpointCases, rawProofImpERoot.
  right. right. left.
  split; reflexivity.
Qed.

Theorem raw_proofImpE_ruleCoverage : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context antecedent consequent impChild antecedentChild,
  RawProofRuleCoverage M impChild ->
  RawProofEndpoint M impChild context
    (rawFormulaImpCode M antecedent consequent) ->
  RawProofRuleCoverage M antecedentChild ->
  RawProofEndpoint M antecedentChild context antecedent ->
  RawProofRuleCoverage M
    (rawProofImpERoot M context antecedent consequent
      impChild antecedentChild).
Proof.
  intros M hPA context antecedent consequent impChild antecedentChild
    (leftCode & leftStep & [[[hleftDefined hleftRows]
      himpOldSupported] hleftEndpointRows])
    himpEndpoint
    (rightCode & rightStep & [[[hrightDefined hrightRows]
      hantecedentOldSupported] hrightEndpointRows])
    hantecedentEndpoint.
  set (parent := rawProofImpERoot M context antecedent consequent
    impChild antecedentChild).
  destruct (raw_proofBinarySupport_to_parent M hPA
    impChild leftCode leftStep
    antecedentChild rightCode rightStep parent)
    as (newCode & newStep & [hnewDefined hnewExact]).
  assert (himpBelow : rawLt M impChild parent).
  {
    unfold parent.
    exact (raw_proofImpERoot_imp_child_lt M hPA
      context antecedent consequent impChild antecedentChild).
  }
  assert (hantecedentBelow : rawLt M antecedentChild parent).
  {
    unfold parent.
    exact (raw_proofImpERoot_antecedent_child_lt M hPA
      context antecedent consequent impChild antecedentChild).
  }
  assert (himpNewSupported :
      rawProofCodeSupported M newCode newStep impChild).
  {
    apply (proj2 (hnewExact impChild
      (raw_assignment_lt_trans M hPA
        impChild parent (raw_succ M parent) himpBelow
        (raw_assignment_lt_self_succ M hPA parent)))).
    left. split.
    - exact (raw_assignment_lt_self_succ M hPA impChild).
    - exact himpOldSupported.
  }
  assert (hantecedentNewSupported :
      rawProofCodeSupported M newCode newStep antecedentChild).
  {
    apply (proj2 (hnewExact antecedentChild
      (raw_assignment_lt_trans M hPA
        antecedentChild parent (raw_succ M parent) hantecedentBelow
        (raw_assignment_lt_self_succ M hPA parent)))).
    right. left. split.
    - exact (raw_assignment_lt_self_succ M hPA antecedentChild).
    - exact hantecedentOldSupported.
  }
  exists newCode, newStep. split.
  - split.
    + split; [exact hnewDefined |].
      intros code hbelow hsupported.
      pose proof (proj1 (hnewExact code hbelow) hsupported) as hshape.
      destruct hshape as
        [[hbelowLeft hleftSupported] |
          [[hbelowRight hrightSupported] | ->]].
      * apply (raw_proofSyntaxStep_change_support M
          code leftCode leftStep newCode newStep
          (hleftRows code hbelowLeft hleftSupported)).
        intros nested hnestedBelow hnestedSupported.
        apply (proj2 (hnewExact nested
          (raw_assignment_lt_trans M hPA
            nested code (raw_succ M parent) hnestedBelow hbelow))).
        left. split.
        -- exact (raw_assignment_lt_trans M hPA
             nested code (raw_succ M impChild)
             hnestedBelow hbelowLeft).
        -- exact hnestedSupported.
      * apply (raw_proofSyntaxStep_change_support M
          code rightCode rightStep newCode newStep
          (hrightRows code hbelowRight hrightSupported)).
        intros nested hnestedBelow hnestedSupported.
        apply (proj2 (hnewExact nested
          (raw_assignment_lt_trans M hPA
            nested code (raw_succ M parent) hnestedBelow hbelow))).
        right. left. split.
        -- exact (raw_assignment_lt_trans M hPA
             nested code (raw_succ M antecedentChild)
             hnestedBelow hbelowRight).
        -- exact hnestedSupported.
      * unfold parent.
        exact (raw_proofImpE_syntax_step M hPA
          context antecedent consequent impChild antecedentChild
          newCode newStep himpNewSupported hantecedentNewSupported).
    + apply (proj2 (hnewExact parent
        (raw_assignment_lt_self_succ M hPA parent))).
      right. right. reflexivity.
  - intros code hbelow hsupported.
    pose proof (proj1 (hnewExact code hbelow) hsupported) as hshape.
    destruct hshape as
      [[hbelowLeft hleftSupported] |
        [[hbelowRight hrightSupported] | ->]].
    + exact (hleftEndpointRows code hbelowLeft hleftSupported).
    + exact (hrightEndpointRows code hbelowRight hrightSupported).
    + unfold parent.
      exact (raw_proofImpE_endpoint_rule_complete M hPA
        context antecedent consequent impChild antecedentChild
        himpEndpoint hantecedentEndpoint).
Qed.

End PABoundedRawCodedProofBinaryConstructors.
