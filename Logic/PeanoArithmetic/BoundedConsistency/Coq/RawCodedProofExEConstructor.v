(**
  Coverage-certified existential elimination for model-coded PA proofs.

  [RP_exE] is the binder-sensitive binary constructor required to unpack the
  three existential fields of a restricted-proof assumption.  Its first
  child proves [exists x, body] in the parent context.  Its second child
  proves the shifted conclusion from [body] added to the pointwise-shifted
  parent context.

  All shift relations remain explicit inputs.  The work performed here is
  purely proof-producing: union the two child support tables, add the exact
  tag-14 parent, and certify every syntax and endpoint row.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedAssignment RawCodedSyntaxConstructors
  RawCodedFormulaOperations RawCodedContextShift
  RawCodedProofConstructors RawCodedProofDescent RawCodedProofTraversal
  RawCodedProofEndpoints RawCodedProofRules RawCodedProofRuleCoverage
  RawCodedListInjectivity RawCodedProofSupportExtension
  RawCodedProofBinarySupportUnion.

Import ListNotations.

Module PABoundedRawCodedProofExEConstructor.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedProofTraversal.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedListInjectivity.
Import PABoundedRawCodedProofSupportExtension.
Import PABoundedRawCodedProofBinarySupportUnion.

Definition rawProofExERoot (M : RawPAModel)
    (context body conclusion existentialChild bodyChild : M) : M :=
  rawListCode M
    [rawNumeralValue M 14; context; body; conclusion;
      existentialChild; bodyChild].

Arguments rawProofExERoot
  M context body conclusion existentialChild bodyChild : clear implicits.

Lemma raw_proofExERoot_existential_child_lt : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context body conclusion existentialChild bodyChild,
  rawLt M existentialChild
    (rawProofExERoot M context body conclusion
      existentialChild bodyChild).
Proof.
  intros M hPA context body conclusion existentialChild bodyChild.
  unfold rawProofExERoot.
  apply rawProofListCode_member_lt; [exact hPA |].
  cbn. tauto.
Qed.

Lemma raw_proofExERoot_body_child_lt : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context body conclusion existentialChild bodyChild,
  rawLt M bodyChild
    (rawProofExERoot M context body conclusion
      existentialChild bodyChild).
Proof.
  intros M hPA context body conclusion existentialChild bodyChild.
  unfold rawProofExERoot.
  apply rawProofListCode_member_lt; [exact hPA |].
  cbn. tauto.
Qed.

Lemma raw_proofExERoot_list_view : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context body conclusion existentialChild bodyChild tag payload,
  rawProofExERoot M context body conclusion existentialChild bodyChild =
    rawListCode M (rawNumeralValue M tag :: payload) ->
  tag = 14 /\
  payload = [context; body; conclusion; existentialChild; bodyChild].
Proof.
  intros M hPA context body conclusion existentialChild bodyChild
    tag payload hcode.
  unfold rawProofExERoot in hcode.
  pose proof (rawListCode_injective M hPA
    [rawNumeralValue M 14; context; body; conclusion;
      existentialChild; bodyChild]
    (rawNumeralValue M tag :: payload) hcode) as hfields.
  assert (hhead : rawNumeralValue M 14 = rawNumeralValue M tag).
  { now inversion hfields. }
  assert (htail :
      [context; body; conclusion; existentialChild; bodyChild] = payload).
  { now inversion hfields. }
  split.
  - symmetry. exact (rawNumeralValue_injective M hPA _ _ hhead).
  - symmetry. exact htail.
Qed.

Lemma raw_proofExERoot_recursive_children : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context body conclusion existentialChild bodyChild
      rowContext a b c t child1 child2 child3 fields children,
  In (fields, children)
    (rawProofRecursiveCases M
      rowContext a b c t child1 child2 child3) ->
  rawProofExERoot M context body conclusion existentialChild bodyChild =
    rawListCode M fields ->
  children = [existentialChild; bodyChild].
Proof.
  intros M hPA context body conclusion existentialChild bodyChild
    rowContext a b c t child1 child2 child3 fields children
    hentry hcode.
  unfold rawProofRecursiveCases in hentry. cbn in hentry.
  repeat match type of hentry with
  | _ \/ _ => destruct hentry as [hentry | hentry]
  end; try contradiction.
  all: inversion hentry; subst fields children; clear hentry.
  all: unfold rawProofExERoot in hcode.
  all: pose proof (rawListCode_injective M hPA _ _ hcode) as hfields.
  all: try discriminate hfields.
  all: inversion hfields; reflexivity.
Qed.

Lemma raw_proofExE_syntax_step : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context body conclusion existentialChild bodyChild
      supportCode supportStep,
  rawProofCodeSupported M supportCode supportStep existentialChild ->
  rawProofCodeSupported M supportCode supportStep bodyChild ->
  RawProofSyntaxStep M
    (rawProofExERoot M context body conclusion
      existentialChild bodyChild)
    supportCode supportStep.
Proof.
  intros M hPA context body conclusion existentialChild bodyChild
    supportCode supportStep hexSupported hbodySupported.
  split.
  - exists context, body, conclusion,
      (raw_zero M), (raw_zero M), existentialChild, bodyChild,
      (raw_zero M).
    unfold RawProofConstructorCode, rawProofExERoot.
    do 14 right. left. reflexivity.
  - intros rowContext a b c t child1 child2 child3 hconstructor.
    split.
    + exact (raw_proofConstructorCode_descent M hPA
        (rawProofExERoot M context body conclusion
          existentialChild bodyChild)
        rowContext a b c t child1 child2 child3 hconstructor).
    + apply Forall_forall. intros [fields children] hentry.
      unfold RawProofChildrenClosedCase.
      intro hcode.
      pose proof (raw_proofExERoot_recursive_children M hPA
        context body conclusion existentialChild bodyChild
        rowContext a b c t child1 child2 child3 fields children
        hentry hcode) as ->.
      constructor.
      * split; [exact hexSupported |].
        exact (raw_proofExERoot_existential_child_lt M hPA
          context body conclusion existentialChild bodyChild).
      * constructor.
        -- split; [exact hbodySupported |].
           exact (raw_proofExERoot_body_child_lt M hPA
             context body conclusion existentialChild bodyChild).
        -- constructor.
Qed.

Lemma raw_proofExE_endpoint_rule_complete : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context shiftedContext body conclusion shiftedConclusion
      existentialChild bodyChild,
  RawProofEndpoint M existentialChild context
    (rawFormulaExCode M body) ->
  RawContextShift M context shiftedContext ->
  RawCodedFormulaShift M
    (raw_zero M) (rawNumeralValue M 1)
    conclusion shiftedConclusion ->
  RawProofEndpoint M bodyChild
    (rawListNode M body shiftedContext) shiftedConclusion ->
  RawProofEndpointRuleComplete M
    (rawProofExERoot M context body conclusion
      existentialChild bodyChild).
Proof.
  intros M hPA context shiftedContext body conclusion shiftedConclusion
    existentialChild bodyChild hexEndpoint hcontextShift
    hconclusionShift hbodyEndpoint
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
  all: pose proof (raw_proofExERoot_list_view M hPA
    context body conclusion existentialChild bodyChild
    _ _ hhead) as hview.
  all: destruct hview as [htag hpayload].
  all: try discriminate htag.
  inversion hpayload;
    subst endpointContext a b child1 child2.
  subst endpointConclusion.
  exists context, body, conclusion, shiftedContext, shiftedConclusion,
    existentialChild, bodyChild, (rawFormulaExCode M body).
  split; [reflexivity |].
  unfold RawProofRuleValidCases, rawProofExERoot.
  do 14 right. left.
  repeat split; assumption || reflexivity.
Qed.

Corollary raw_proofExE_endpoint : forall
    (M : RawPAModel) context body conclusion
      existentialChild bodyChild,
  RawProofEndpoint M
    (rawProofExERoot M context body conclusion
      existentialChild bodyChild)
    context conclusion.
Proof.
  intros M context body conclusion existentialChild bodyChild.
  exists context, body, conclusion,
    (raw_zero M), (raw_zero M), existentialChild, bodyChild,
    (raw_zero M).
  split; [reflexivity |].
  unfold RawProofEndpointCases, rawProofExERoot.
  do 14 right. left. split; reflexivity.
Qed.

Theorem raw_proofExE_ruleCoverage : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context shiftedContext body conclusion shiftedConclusion
      existentialChild bodyChild,
  RawProofRuleCoverage M existentialChild ->
  RawProofEndpoint M existentialChild context
    (rawFormulaExCode M body) ->
  RawContextShift M context shiftedContext ->
  RawCodedFormulaShift M
    (raw_zero M) (rawNumeralValue M 1)
    conclusion shiftedConclusion ->
  RawProofRuleCoverage M bodyChild ->
  RawProofEndpoint M bodyChild
    (rawListNode M body shiftedContext) shiftedConclusion ->
  RawProofRuleCoverage M
    (rawProofExERoot M context body conclusion
      existentialChild bodyChild).
Proof.
  intros M hPA context shiftedContext body conclusion shiftedConclusion
    existentialChild bodyChild
    (leftCode & leftStep & [[[hleftDefined hleftRows]
      hexOldSupported] hleftEndpointRows])
    hexEndpoint hcontextShift hconclusionShift
    (rightCode & rightStep & [[[hrightDefined hrightRows]
      hbodyOldSupported] hrightEndpointRows])
    hbodyEndpoint.
  set (parent := rawProofExERoot M context body conclusion
    existentialChild bodyChild).
  destruct (raw_proofBinarySupport_to_parent M hPA
    existentialChild leftCode leftStep
    bodyChild rightCode rightStep parent)
    as (newCode & newStep & [hnewDefined hnewExact]).
  assert (hexBelow : rawLt M existentialChild parent).
  {
    unfold parent.
    exact (raw_proofExERoot_existential_child_lt M hPA
      context body conclusion existentialChild bodyChild).
  }
  assert (hbodyBelow : rawLt M bodyChild parent).
  {
    unfold parent.
    exact (raw_proofExERoot_body_child_lt M hPA
      context body conclusion existentialChild bodyChild).
  }
  assert (hexNewSupported :
      rawProofCodeSupported M newCode newStep existentialChild).
  {
    apply (proj2 (hnewExact existentialChild
      (raw_assignment_lt_trans M hPA
        existentialChild parent (raw_succ M parent) hexBelow
        (raw_assignment_lt_self_succ M hPA parent)))).
    left. split.
    - exact (raw_assignment_lt_self_succ M hPA existentialChild).
    - exact hexOldSupported.
  }
  assert (hbodyNewSupported :
      rawProofCodeSupported M newCode newStep bodyChild).
  {
    apply (proj2 (hnewExact bodyChild
      (raw_assignment_lt_trans M hPA
        bodyChild parent (raw_succ M parent) hbodyBelow
        (raw_assignment_lt_self_succ M hPA parent)))).
    right. left. split.
    - exact (raw_assignment_lt_self_succ M hPA bodyChild).
    - exact hbodyOldSupported.
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
             nested code (raw_succ M existentialChild)
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
             nested code (raw_succ M bodyChild)
             hnestedBelow hbelowRight).
        -- exact hnestedSupported.
      * unfold parent.
        exact (raw_proofExE_syntax_step M hPA
          context body conclusion existentialChild bodyChild
          newCode newStep hexNewSupported hbodyNewSupported).
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
      exact (raw_proofExE_endpoint_rule_complete M hPA
        context shiftedContext body conclusion shiftedConclusion
        existentialChild bodyChild hexEndpoint hcontextShift
        hconclusionShift hbodyEndpoint).
Qed.

End PABoundedRawCodedProofExEConstructor.
