(**
  Standard valid proofs realize proof-wide endpoint rule coverage.

  The support table used here is intentionally the restricted standard
  table.  The older unrestricted standard table marks every canonical raw
  proof code below a numerical bound, including syntactically well-formed
  but invalid natural-deduction trees.  Such rows cannot satisfy local rule
  validity.  By contrast, the restricted table marks exactly valid proofs
  (also carrying an inessential common rank bound), is closed under genuine
  recursive children, and therefore supplies the honest support predicate
  required by [RawProofRuleCoverage].

  Endpoint completeness itself uses a separate fact: every endpoint exposed
  by the arithmetic endpoint graph of a standard quotation is the canonical
  quoted endpoint.  This includes arbitrary substitution traces, whose
  standard-output functionality was established by formula coverage
  adequacy.  The existing quotation theorem for valid rules can consequently
  be transported to every advertised endpoint, not only to one selected
  endpoint witness.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import ListCode Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  BoundedConsistency CodedProof PolynomialPairInjectivity
  RawCodedSyntaxConstructors RawCodedAssignment
  RawCodedProofConstructors RawCodedProofTraversal RawCodedProofEndpoints
  RawCodedProofStandardSyntax RawCodedRestrictedProofStandardAdequacy
  RawCodedProofFormulaCoverageStandard RawCodedProofRuleCoverage.

Import ListNotations.

Module PABoundedRawCodedProofRuleCoverageStandard.

Import PA.
Import PAListCode.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedConsistency.
Import PABoundedCodedProof.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedProofTraversal.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofStandardSyntax.
Import PABoundedRawCodedRestrictedProofStandardAdequacy.
Import PABoundedRawCodedProofFormulaCoverageStandard.
Import PABoundedRawCodedProofRuleCoverage.

(** A valid standard node is rule-complete at every endpoint exposed by its
    arithmetic endpoint relation. *)
Lemma raw_quotedValidProof_endpoint_rule_complete : forall
    (M : RawPAModel), RawPASatisfies M -> forall derivation,
  RawProofValid derivation ->
  RawProofEndpointRuleComplete M (rawQuotedProofCode M derivation).
Proof.
  intros M hPA derivation hvalid context conclusion hendpoint.
  destruct (raw_quotedProof_endpoint_functional M hPA derivation
    context conclusion hendpoint) as [hcontext hconclusion].
  rewrite hcontext, hconclusion.
  exact (raw_quotedProof_rule_valid M hPA derivation hvalid).
Qed.

(** The rank coordinate only filters the finite support table.  Choosing the
    root's own occurrence rank makes the root eligible, while validity and
    rank monotonicity make every genuine child eligible as well. *)
Theorem raw_quotedValidProof_rule_coverage : forall (M : RawPAModel),
  RawPASatisfies M -> forall root,
  RawProofValid root ->
  RawProofRuleCoverage M (rawQuotedProofCode M root).
Proof.
  intros M hPA root hrootValid.
  set (level := rawProofOccurrenceRank root).
  assert (hrootBounded : rawProofOccurrenceRank root <= level).
  { unfold level. lia. }
  destruct (raw_standardRestrictedProofSupportTable_for_quotation
    M hPA level root hrootValid hrootBounded) as
    (supportCode & supportStep & htable & hrootSupported).
  destruct htable as [hdefined hexact].
  exists supportCode, supportStep. split.
  - split.
    + split.
      * rewrite rawQuotedProofCode_standard by exact hPA.
        change (RawCodedAssignmentDefinedThrough M supportCode supportStep
          (rawNumeralValue M (S (rawProofCode root)))).
        exact hdefined.
      * intros code hcode hsupported.
        assert (hcodeBound : rawLt M code
            (rawNumeralValue M (S (rawProofCode root)))).
        {
          rewrite rawQuotedProofCode_standard in hcode by exact hPA.
          change (rawLt M code
            (rawNumeralValue M (S (rawProofCode root)))) in hcode.
          exact hcode.
        }
        destruct (proj1 (hexact code hcodeBound) hsupported) as
          (derivation & -> & hderivationBound & hvalid & hbounded).
        apply raw_quotedProof_syntax_step_of_children; [exact hPA |].
        intros child hchild.
        exact (raw_standardRestrictedProofSupportTable_child M hPA
          level (S (rawProofCode root)) supportCode supportStep
          (conj hdefined hexact) derivation child
          hderivationBound hvalid hbounded hchild).
    + exact hrootSupported.
  - intros code hcode hsupported.
    assert (hcodeBound : rawLt M code
        (rawNumeralValue M (S (rawProofCode root)))).
    {
      rewrite rawQuotedProofCode_standard in hcode by exact hPA.
      change (rawLt M code
        (rawNumeralValue M (S (rawProofCode root)))) in hcode.
      exact hcode.
    }
    destruct (proj1 (hexact code hcodeBound) hsupported) as
      (derivation & -> & _ & hvalid & _).
    exact (raw_quotedValidProof_endpoint_rule_complete
      M hPA derivation hvalid).
Qed.

End PABoundedRawCodedProofRuleCoverageStandard.
