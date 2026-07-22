(**
  Coverage-certified conjunction-elimination constructors.

  A restricted-proof certificate is represented by three existential
  witnesses followed by a right-associated conjunction of seven fields.
  Before its soundness data can be used by an open contradiction compiler,
  those fields must be projected by honest raw proof nodes.  This module
  supplies both [RP_andE1] and [RP_andE2] uniformly.

  As with the earlier bottom- and implication-elimination constructors, the
  support table is extended exactly through the new parent.  Constructor-code
  injectivity rules out every alternative recursive or endpoint view.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedAssignment RawCodedSyntaxConstructors
  RawCodedProofConstructors RawCodedProofDescent
  RawCodedProofTraversal RawCodedProofEndpoints RawCodedProofRules
  RawCodedProofRuleCoverage RawCodedListInjectivity
  RawCodedProofSupportExtension.

Import ListNotations.

Module PABoundedRawCodedProofAndEConstructors.

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

Inductive RawAndProjection : Type :=
| RawAndLeft
| RawAndRight.

Definition rawAndProjectionTag (projection : RawAndProjection) : nat :=
  match projection with
  | RawAndLeft => 6
  | RawAndRight => 7
  end.

Definition rawAndProjectionConclusion (M : RawPAModel)
    (projection : RawAndProjection) (left right : M) : M :=
  match projection with
  | RawAndLeft => left
  | RawAndRight => right
  end.

Definition rawProofAndERoot (M : RawPAModel)
    (projection : RawAndProjection)
    (context left right child : M) : M :=
  rawListCode M
    [rawNumeralValue M (rawAndProjectionTag projection);
      context; left; right; child].

Arguments rawAndProjectionConclusion M projection left right
  : clear implicits.
Arguments rawProofAndERoot M projection context left right child
  : clear implicits.

Lemma raw_proofAndERoot_child_lt : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      projection context left right child,
  rawLt M child
    (rawProofAndERoot M projection context left right child).
Proof.
  intros M hPA projection context left right child.
  unfold rawProofAndERoot.
  apply rawProofListCode_member_lt; [exact hPA |].
  cbn. tauto.
Qed.

Lemma raw_proofAndERoot_list_view : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      projection context left right child tag payload,
  rawProofAndERoot M projection context left right child =
    rawListCode M (rawNumeralValue M tag :: payload) ->
  tag = rawAndProjectionTag projection /\
  payload = [context; left; right; child].
Proof.
  intros M hPA projection context left right child tag payload hcode.
  unfold rawProofAndERoot in hcode.
  pose proof (rawListCode_injective M hPA
    [rawNumeralValue M (rawAndProjectionTag projection);
      context; left; right; child]
    (rawNumeralValue M tag :: payload) hcode) as hfields.
  assert (hhead :
      rawNumeralValue M (rawAndProjectionTag projection) =
      rawNumeralValue M tag).
  { now inversion hfields. }
  assert (htail : [context; left; right; child] = payload).
  { now inversion hfields. }
  split.
  - symmetry. exact (rawNumeralValue_injective M hPA _ _ hhead).
  - symmetry. exact htail.
Qed.

Lemma raw_proofAndERoot_recursive_children : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      projection context left right child
      rowContext a b c t child1 child2 child3 fields children,
  In (fields, children)
    (rawProofRecursiveCases M
      rowContext a b c t child1 child2 child3) ->
  rawProofAndERoot M projection context left right child =
    rawListCode M fields ->
  children = [child].
Proof.
  intros M hPA projection context left right child
    rowContext a b c t child1 child2 child3 fields children
    hentry hcode.
  unfold rawProofRecursiveCases in hentry. cbn in hentry.
  repeat match type of hentry with
  | _ \/ _ => destruct hentry as [hentry | hentry]
  end; try contradiction.
  all: inversion hentry; subst fields children; clear hentry.
  all: unfold rawProofAndERoot in hcode.
  all: destruct projection.
  all: cbn [rawAndProjectionTag] in hcode.
  all: pose proof (rawListCode_injective M hPA _ _ hcode) as hfields.
  all: try discriminate hfields.
  all: inversion hfields; reflexivity.
Qed.

Lemma raw_proofAndERoot_constructor : forall
    (M : RawPAModel) projection context left right child,
  RawProofConstructorCode M
    (rawProofAndERoot M projection context left right child)
    context left right (raw_zero M) (raw_zero M)
    child (raw_zero M) (raw_zero M).
Proof.
  intros M [|] context left right child;
    unfold RawProofConstructorCode, rawProofAndERoot,
      rawAndProjectionTag.
  - right. right. right. right. right. right. left. reflexivity.
  - right. right. right. right. right. right. right. left. reflexivity.
Qed.

Lemma raw_proofAndE_syntax_step : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      projection context left right child supportCode supportStep,
  rawProofCodeSupported M supportCode supportStep child ->
  RawProofSyntaxStep M
    (rawProofAndERoot M projection context left right child)
    supportCode supportStep.
Proof.
  intros M hPA projection context left right child
    supportCode supportStep hchildSupported.
  split.
  - exists context, left, right,
      (raw_zero M), (raw_zero M), child,
      (raw_zero M), (raw_zero M).
    apply raw_proofAndERoot_constructor.
  - intros rowContext a b c t child1 child2 child3 hconstructor.
    split.
    + exact (raw_proofConstructorCode_descent M hPA
        (rawProofAndERoot M projection context left right child)
        rowContext a b c t child1 child2 child3 hconstructor).
    + apply Forall_forall. intros [fields children] hentry.
      unfold RawProofChildrenClosedCase.
      intro hcode.
      pose proof (raw_proofAndERoot_recursive_children M hPA
        projection context left right child
        rowContext a b c t child1 child2 child3 fields children
        hentry hcode) as ->.
      constructor.
      * split; [exact hchildSupported |].
        exact (raw_proofAndERoot_child_lt M hPA
          projection context left right child).
      * constructor.
Qed.

Lemma raw_proofAndE_endpoint_rule_complete : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      projection context left right child,
  RawProofEndpoint M child context
    (rawFormulaAndCode M left right) ->
  RawProofEndpointRuleComplete M
    (rawProofAndERoot M projection context left right child).
Proof.
  intros M hPA projection context left right child hchildEndpoint
    endpointContext endpointConclusion hendpoint.
  destruct hendpoint as
    (rowContext & a & b & c & t & child1 & child2 & child3 &
      hcontext & hcases).
  subst rowContext.
  destruct projection.
  - unfold RawProofEndpointCases in hcases.
    repeat match type of hcases with
    | _ \/ _ => destruct hcases as [hcases | hcases]
    end; try contradiction.
    all: destruct hcases as [hhead hrest].
    all: pose proof (raw_proofAndERoot_list_view M hPA
      RawAndLeft context left right child _ _ hhead) as hview.
    all: destruct hview as [htag hpayload].
    all: cbn [rawAndProjectionTag] in htag.
    all: try discriminate htag.
    inversion hpayload; subst endpointContext a b child1.
    subst endpointConclusion.
    exists context, left, right,
      (rawFormulaAndCode M left right), (raw_zero M), child,
      (raw_zero M), (raw_zero M).
    split; [reflexivity |].
    unfold RawProofRuleValidCases, rawProofAndERoot,
      rawAndProjectionTag.
    right. right. right. right. right. right. left.
    repeat split; assumption || reflexivity.
  - unfold RawProofEndpointCases in hcases.
    repeat match type of hcases with
    | _ \/ _ => destruct hcases as [hcases | hcases]
    end; try contradiction.
    all: destruct hcases as [hhead hrest].
    all: pose proof (raw_proofAndERoot_list_view M hPA
      RawAndRight context left right child _ _ hhead) as hview.
    all: destruct hview as [htag hpayload].
    all: cbn [rawAndProjectionTag] in htag.
    all: try discriminate htag.
    inversion hpayload; subst endpointContext a b child1.
    subst endpointConclusion.
    exists context, left, right,
      (rawFormulaAndCode M left right), (raw_zero M), child,
      (raw_zero M), (raw_zero M).
    split; [reflexivity |].
    unfold RawProofRuleValidCases, rawProofAndERoot,
      rawAndProjectionTag.
    right. right. right. right. right. right. right. left.
    repeat split; assumption || reflexivity.
Qed.

Corollary raw_proofAndE_endpoint : forall
    (M : RawPAModel) projection context left right child,
  RawProofEndpoint M
    (rawProofAndERoot M projection context left right child)
    context (rawAndProjectionConclusion M projection left right).
Proof.
  intros M [|] context left right child.
  - exists context, left, right,
      (raw_zero M), (raw_zero M), child,
      (raw_zero M), (raw_zero M).
    split; [reflexivity |].
    unfold RawProofEndpointCases, rawProofAndERoot,
      rawAndProjectionTag, rawAndProjectionConclusion.
    right. right. right. right. right. right. left.
    split; reflexivity.
  - exists context, left, right,
      (raw_zero M), (raw_zero M), child,
      (raw_zero M), (raw_zero M).
    split; [reflexivity |].
    unfold RawProofEndpointCases, rawProofAndERoot,
      rawAndProjectionTag, rawAndProjectionConclusion.
    right. right. right. right. right. right. right. left.
    split; reflexivity.
Qed.

Theorem raw_proofAndE_ruleCoverage : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      projection context left right child,
  RawProofRuleCoverage M child ->
  RawProofEndpoint M child context
    (rawFormulaAndCode M left right) ->
  RawProofRuleCoverage M
    (rawProofAndERoot M projection context left right child).
Proof.
  intros M hPA projection context left right child
    (oldCode & oldStep & [[[holdDefined holdRows] hchildOldSupported]
      holdEndpointRows])
    hchildEndpoint.
  set (parent := rawProofAndERoot M projection context left right child).
  destruct (raw_proofSupportExtension_to_parent M hPA
    child oldCode oldStep parent)
    as (newCode & newStep & [hnewDefined hnewExact]).
  assert (hchildBelow : rawLt M child parent).
  {
    unfold parent.
    exact (raw_proofAndERoot_child_lt M hPA
      projection context left right child).
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
        exact (raw_proofAndE_syntax_step M hPA
          projection context left right child
          newCode newStep hchildNewSupported).
    + apply (proj2 (hnewExact parent
        (raw_assignment_lt_self_succ M hPA parent))).
      right. reflexivity.
  - intros code hbelow hsupported.
    pose proof (proj1 (hnewExact code hbelow) hsupported) as hshape.
    destruct hshape as [[hbelowChild holdSupported] | ->].
    + exact (holdEndpointRows code hbelowChild holdSupported).
    + unfold parent.
      exact (raw_proofAndE_endpoint_rule_complete M hPA
        projection context left right child hchildEndpoint).
Qed.

End PABoundedRawCodedProofAndEConstructors.
