(**
  A rule-agnostic coverage compiler for binary raw-proof nodes.

  The two children may use unrelated nonstandard support tables.  The binary
  support union joins those tables below a fresh parent.  Consequently a
  concrete binary rule only has to provide four local facts: both children
  are smaller than the parent, the parent is a syntax step whenever both
  children are supported, and every advertised endpoint of the parent is a
  valid rule instance.

  Keeping this traversal argument independent of any particular logical rule
  is useful for conjunction introduction below and for future binary proof
  constructors whose formula fields are themselves nonstandard codes.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedAssignment RawCodedProofTraversal RawCodedProofRuleCoverage
  RawCodedProofSupportExtension RawCodedProofBinarySupportUnion.

Module PABoundedRawCodedProofBinaryCoverage.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedProofTraversal.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedProofSupportExtension.
Import PABoundedRawCodedProofBinarySupportUnion.

(** Extend two complete covered proof trees by one certified binary parent.

    Notice that the endpoint hypotheses for the children have already been
    consumed by the concrete parent's endpoint-completeness proof.  This
    theorem is deliberately phrased only in terms of the semantic interfaces
    needed to transport the two support tables. *)
Theorem raw_proofBinary_ruleCoverage : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      leftRoot rightRoot parent,
  RawProofRuleCoverage M leftRoot ->
  RawProofRuleCoverage M rightRoot ->
  rawLt M leftRoot parent ->
  rawLt M rightRoot parent ->
  (forall supportCode supportStep,
    rawProofCodeSupported M supportCode supportStep leftRoot ->
    rawProofCodeSupported M supportCode supportStep rightRoot ->
    RawProofSyntaxStep M parent supportCode supportStep) ->
  RawProofEndpointRuleComplete M parent ->
  RawProofRuleCoverage M parent.
Proof.
  intros M hPA leftRoot rightRoot parent
    (leftCode & leftStep & [[[hleftDefined hleftRows]
      hleftOldSupported] hleftEndpointRows])
    (rightCode & rightStep & [[[hrightDefined hrightRows]
      hrightOldSupported] hrightEndpointRows])
    hleftBelow hrightBelow hparentSyntax hparentEndpoints.
  destruct (raw_proofBinarySupport_to_parent M hPA
    leftRoot leftCode leftStep rightRoot rightCode rightStep parent)
    as (newCode & newStep & [hnewDefined hnewExact]).
  assert (hleftNewSupported :
      rawProofCodeSupported M newCode newStep leftRoot).
  {
    apply (proj2 (hnewExact leftRoot
      (raw_assignment_lt_trans M hPA
        leftRoot parent (raw_succ M parent) hleftBelow
        (raw_assignment_lt_self_succ M hPA parent)))).
    left. split.
    - exact (raw_assignment_lt_self_succ M hPA leftRoot).
    - exact hleftOldSupported.
  }
  assert (hrightNewSupported :
      rawProofCodeSupported M newCode newStep rightRoot).
  {
    apply (proj2 (hnewExact rightRoot
      (raw_assignment_lt_trans M hPA
        rightRoot parent (raw_succ M parent) hrightBelow
        (raw_assignment_lt_self_succ M hPA parent)))).
    right. left. split.
    - exact (raw_assignment_lt_self_succ M hPA rightRoot).
    - exact hrightOldSupported.
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
             nested code (raw_succ M leftRoot)
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
             nested code (raw_succ M rightRoot)
             hnestedBelow hbelowRight).
        -- exact hnestedSupported.
      * exact (hparentSyntax newCode newStep
          hleftNewSupported hrightNewSupported).
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
    + exact hparentEndpoints.
Qed.

End PABoundedRawCodedProofBinaryCoverage.
