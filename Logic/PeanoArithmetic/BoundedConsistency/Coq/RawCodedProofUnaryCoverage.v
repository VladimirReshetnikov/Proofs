(** Rule-agnostic support-table extension for one-child raw proof nodes. *)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedAssignment RawCodedProofTraversal RawCodedProofRuleCoverage
  RawCodedProofSupportExtension.

Module PABoundedRawCodedProofUnaryCoverage.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedProofTraversal.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedProofSupportExtension.

(** Add exactly one certified parent above an already covered child. *)
Theorem raw_proofUnary_ruleCoverage : forall
    (M : RawPAModel), RawPASatisfies M -> forall child parent,
  RawProofRuleCoverage M child ->
  rawLt M child parent ->
  (forall supportCode supportStep,
    rawProofCodeSupported M supportCode supportStep child ->
    RawProofSyntaxStep M parent supportCode supportStep) ->
  RawProofEndpointRuleComplete M parent ->
  RawProofRuleCoverage M parent.
Proof.
  intros M hPA child parent
    (oldCode & oldStep & [[[holdDefined holdRows] hchildOldSupported]
      holdEndpointRows])
    hchildBelow hparentSyntax hparentEndpoints.
  destruct (raw_proofSupportExtension_to_parent M hPA
    child oldCode oldStep parent)
    as (newCode & newStep & [hnewDefined hnewExact]).
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
      * exact (hparentSyntax newCode newStep hchildNewSupported).
    + apply (proj2 (hnewExact parent
        (raw_assignment_lt_self_succ M hPA parent))).
      right. reflexivity.
  - intros code hbelow hsupported.
    pose proof (proj1 (hnewExact code hbelow) hsupported) as hshape.
    destruct hshape as [[hbelowChild holdSupported] | ->].
    + exact (holdEndpointRows code hbelowChild holdSupported).
    + exact hparentEndpoints.
Qed.

End PABoundedRawCodedProofUnaryCoverage.
