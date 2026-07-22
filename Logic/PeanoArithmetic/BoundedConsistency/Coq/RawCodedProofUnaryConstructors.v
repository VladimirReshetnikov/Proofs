(**
  Coverage-certified unary constructors for model-coded PA proofs.

  The first constructor needed by the uniform proof compiler is bottom
  elimination.  Given an honest coverage certificate for a child proof of
  falsity, this module places one [RP_botE] node above it and rebuilds the
  support assignment through the (possibly nonstandard) parent code.

  Constructor-code injectivity matters twice.  It proves that every
  alternative recursive view of the new root names exactly the supplied
  child, and that every advertised endpoint of the root is exactly the
  bottom-elimination endpoint used by the local rule certificate.
*)

From Stdlib Require Import List Arith Lia.
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

Module PABoundedRawCodedProofUnaryConstructors.

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

Definition rawProofBotERoot
    (M : RawPAModel) (context conclusion child : M) : M :=
  rawListCode M
    [rawNumeralValue M 3; context; conclusion; child].

Arguments rawProofBotERoot M context conclusion child : clear implicits.

Lemma raw_proofBotERoot_child_lt : forall
    (M : RawPAModel), RawPASatisfies M -> forall context conclusion child,
  rawLt M child (rawProofBotERoot M context conclusion child).
Proof.
  intros M hPA context conclusion child.
  unfold rawProofBotERoot.
  apply rawProofListCode_member_lt; [exact hPA |].
  cbn. tauto.
Qed.

(** Any list-constructor view of the parent has the advertised tag and
    payload.  The statement is intentionally tag-generic so it can discharge
    all seventeen constructor and endpoint alternatives uniformly. *)
Lemma raw_proofBotERoot_list_view : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context conclusion child tag payload,
  rawProofBotERoot M context conclusion child =
    rawListCode M (rawNumeralValue M tag :: payload) ->
  tag = 3 /\ payload = [context; conclusion; child].
Proof.
  intros M hPA context conclusion child tag payload hcode.
  unfold rawProofBotERoot in hcode.
  pose proof (rawListCode_injective M hPA
    [rawNumeralValue M 3; context; conclusion; child]
    (rawNumeralValue M tag :: payload) hcode) as hfields.
  assert (hhead : rawNumeralValue M 3 = rawNumeralValue M tag).
  { now inversion hfields. }
  assert (htail : [context; conclusion; child] = payload).
  { now inversion hfields. }
  split.
  - symmetry. exact (rawNumeralValue_injective M hPA _ _ hhead).
  - symmetry. exact htail.
Qed.

(** Of the fourteen recursive constructor rows, only the [RP_botE] row can
    denote this root.  In that row list-code injectivity fixes its child. *)
Lemma raw_proofBotERoot_recursive_children : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context conclusion child
      rowContext a b c t child1 child2 child3 fields children,
  In (fields, children)
    (rawProofRecursiveCases M
      rowContext a b c t child1 child2 child3) ->
  rawProofBotERoot M context conclusion child = rawListCode M fields ->
  children = [child].
Proof.
  intros M hPA context conclusion child
    rowContext a b c t child1 child2 child3 fields children
    hentry hcode.
  unfold rawProofRecursiveCases in hentry. cbn in hentry.
  repeat match type of hentry with
  | _ \/ _ => destruct hentry as [hentry | hentry]
  end; try contradiction.
  all: inversion hentry; subst fields children; clear hentry.
  all: unfold rawProofBotERoot in hcode.
  all: pose proof (rawListCode_injective M hPA _ _ hcode) as hfields.
  all: try discriminate hfields.
  all: inversion hfields; reflexivity.
Qed.

(** Local syntax closure only needs the new table to support the supplied
    child.  Exact support-table construction is handled by the public
    coverage theorem below. *)
Lemma raw_proofBotE_syntax_step : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context conclusion child supportCode supportStep,
  rawProofCodeSupported M supportCode supportStep child ->
  RawProofSyntaxStep M
    (rawProofBotERoot M context conclusion child)
    supportCode supportStep.
Proof.
  intros M hPA context conclusion child supportCode supportStep
    hchildSupported.
  split.
  - exists context, conclusion,
      (raw_zero M), (raw_zero M), (raw_zero M), child,
      (raw_zero M), (raw_zero M).
    unfold RawProofConstructorCode, rawProofBotERoot.
    right. right. right. left. reflexivity.
  - intros rowContext a b c t child1 child2 child3 hconstructor.
    split.
    + exact (raw_proofConstructorCode_descent M hPA
        (rawProofBotERoot M context conclusion child)
        rowContext a b c t child1 child2 child3 hconstructor).
    + apply Forall_forall. intros [fields children] hentry.
      unfold RawProofChildrenClosedCase.
      intro hcode.
      pose proof (raw_proofBotERoot_recursive_children M hPA
        context conclusion child
        rowContext a b c t child1 child2 child3 fields children
        hentry hcode) as ->.
      constructor.
      * split; [exact hchildSupported |].
        exact (raw_proofBotERoot_child_lt M hPA
          context conclusion child).
      * constructor.
Qed.

(** All endpoint views of the parent collapse to its unique [RP_botE]
    payload, after which the supplied child endpoint is the complete local
    rule witness. *)
Lemma raw_proofBotE_endpoint_rule_complete : forall
    (M : RawPAModel), RawPASatisfies M -> forall context conclusion child,
  RawProofEndpoint M child context (rawFormulaBotCode M) ->
  RawProofEndpointRuleComplete M
    (rawProofBotERoot M context conclusion child).
Proof.
  intros M hPA context conclusion child hchildEndpoint
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
  all: pose proof (raw_proofBotERoot_list_view M hPA
    context conclusion child _ _ hhead) as hview.
  all: destruct hview as [htag hpayload].
  all: try discriminate htag.
  inversion hpayload; subst endpointContext a child1.
  subst endpointConclusion.
  exists context, conclusion, (rawFormulaBotCode M),
    (raw_zero M), (raw_zero M), child,
    (raw_zero M), (raw_zero M).
  split; [reflexivity |].
  unfold RawProofRuleValidCases, rawProofBotERoot.
  right. right. right. left.
  repeat split; assumption || reflexivity.
Qed.

Corollary raw_proofBotE_endpoint : forall
    (M : RawPAModel) context conclusion child,
  RawProofEndpoint M
    (rawProofBotERoot M context conclusion child)
    context conclusion.
Proof.
  intros M context conclusion child.
  exists context, conclusion,
    (raw_zero M), (raw_zero M), (raw_zero M), child,
    (raw_zero M), (raw_zero M).
  split; [reflexivity |].
  unfold RawProofEndpointCases, rawProofBotERoot.
  right. right. right. left.
  split; reflexivity.
Qed.

(** Public unary constructor.  The extension table is exact: old supported
    rows occur only below the child's bound, and the only new row is the
    parent.  This makes the syntax and rule-coverage transfers immediate and
    rules out junk nodes in the gap between child and parent codes. *)
Theorem raw_proofBotE_ruleCoverage : forall
    (M : RawPAModel), RawPASatisfies M -> forall context conclusion child,
  RawProofRuleCoverage M child ->
  RawProofEndpoint M child context (rawFormulaBotCode M) ->
  RawProofRuleCoverage M
    (rawProofBotERoot M context conclusion child).
Proof.
  intros M hPA context conclusion child
    (oldCode & oldStep & [[[holdDefined holdRows] hchildOldSupported]
      holdEndpointRows])
    hchildEndpoint.
  set (parent := rawProofBotERoot M context conclusion child).
  destruct (raw_proofSupportExtension_to_parent M hPA
    child oldCode oldStep parent)
    as (newCode & newStep & [hnewDefined hnewExact]).
  assert (hchildBelow : rawLt M child parent).
  {
    unfold parent.
    exact (raw_proofBotERoot_child_lt M hPA
      context conclusion child).
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
        exact (raw_proofBotE_syntax_step M hPA
          context conclusion child newCode newStep hchildNewSupported).
    + apply (proj2 (hnewExact parent
        (raw_assignment_lt_self_succ M hPA parent))).
      right. reflexivity.
  - intros code hbelow hsupported.
    pose proof (proj1 (hnewExact code hbelow) hsupported) as hshape.
    destruct hshape as [[hbelowChild holdSupported] | ->].
    + exact (holdEndpointRows code hbelowChild holdSupported).
    + unfold parent.
      exact (raw_proofBotE_endpoint_rule_complete M hPA
        context conclusion child hchildEndpoint).
Qed.

End PABoundedRawCodedProofUnaryConstructors.
