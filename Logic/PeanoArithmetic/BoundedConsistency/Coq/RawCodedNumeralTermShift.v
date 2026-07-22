(**
  De Bruijn shifting fixes every model-internal numeral-term code.

  A [RawNumeralTermCodeAt] certificate is already a beta-coded traversal:
  row zero contains [tZero], and every successor row contains [tSucc] of the
  preceding row.  The same table can therefore serve simultaneously as the
  source and target tables of a term-shift trace.  This works for a numeral
  whose length is nonstandard in the ambient PA model; no external decoding
  or recursion over a carrier element is used.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  BoundedConsistency RawModelCompleteness RawCodedSyntaxConstructors
  RawCodedAssignment RawCodedFormulaRankStep RawCodedFormulaRankTotality
  RawCodedFormulaOperations RawCodedNumeralTermCode.

Module PABoundedRawCodedNumeralTermShift.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedConsistency.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFormulaRankStep.
Import PABoundedRawCodedFormulaRankTotality.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedNumeralTermCode.

(** The identity result holds for every nonnegative cutoff and every shift
    amount, not merely for the [0,1] instance used by context shifting. *)
Theorem raw_codedTermShift_numeral_identity : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    bound numeralCode cutoff amount,
  RawNumeralTermCodeAt M bound numeralCode ->
  RawCodedTermShift M cutoff amount numeralCode numeralCode.
Proof.
  intros M hPA bound numeralCode cutoff amount
    (code & step & [hdefined [hzero hrows]] & hroot).
  exists code, step, code, step,
    (raw_succ M bound), bound.
  unfold RawCodedTermShiftTrace.
  repeat split.
  - exact hdefined.
  - exact hdefined.
  - exact (raw_assignment_lt_self_succ M hPA bound).
  - exact hroot.
  - exact hroot.
  - intros index input output hindex [hinput houtput].
    destruct (raw_assignment_zero_or_successor M hPA index)
      as [-> | [predecessor ->]].
    + assert (hinputZero : input = rawTermZeroCode M).
      {
        exact (raw_codedAssignmentLookup_functional M hPA
          code step (raw_zero M) input (rawTermZeroCode M)
          hinput hzero).
      }
      assert (houtputZero : output = rawTermZeroCode M).
      {
        exact (raw_codedAssignmentLookup_functional M hPA
          code step (raw_zero M) output (rawTermZeroCode M)
          houtput hzero).
      }
      right. left. split; assumption.
    + assert (hpredecessorBound : rawLt M predecessor bound).
      {
        destruct (raw_lt_succ_cases M hPA
          (raw_succ M predecessor) bound hindex) as [hlt | heq].
        - exact (raw_assignment_lt_trans M hPA predecessor
            (raw_succ M predecessor) bound
            (raw_assignment_lt_self_succ M hPA predecessor) hlt).
        - rewrite <- heq.
          exact (raw_assignment_lt_self_succ M hPA predecessor).
      }
      destruct (hdefined predecessor
        (raw_assignment_lt_trans M hPA predecessor bound
          (raw_succ M bound) hpredecessorBound
          (raw_assignment_lt_self_succ M hPA bound)))
        as [child hchild].
      destruct (hdefined (raw_succ M predecessor) hindex)
        as [successorCode hsuccessor].
      assert (hsuccessorShape :
          successorCode = rawTermSuccCode M child).
      {
        exact (hrows predecessor child successorCode
          hpredecessorBound hchild hsuccessor).
      }
      assert (hinputSuccessor : input = successorCode).
      {
        exact (raw_codedAssignmentLookup_functional M hPA
          code step (raw_succ M predecessor) input successorCode
          hinput hsuccessor).
      }
      assert (houtputSuccessor : output = successorCode).
      {
        exact (raw_codedAssignmentLookup_functional M hPA
          code step (raw_succ M predecessor) output successorCode
          houtput hsuccessor).
      }
      right. right. left.
      exists predecessor, child, child.
      split.
      * exact (raw_assignment_lt_self_succ M hPA predecessor).
      * split.
        -- split; exact hchild.
        -- split.
           ++ now rewrite hinputSuccessor, hsuccessorShape.
           ++ now rewrite houtputSuccessor, hsuccessorShape.
  - exact (raw_rank_zero_le M hPA cutoff).
Qed.

Corollary raw_codedTermShift_numeral_zero_one : forall
    (M : RawPAModel), RawPASatisfies M -> forall bound numeralCode,
  RawNumeralTermCodeAt M bound numeralCode ->
  RawCodedTermShift M
    (raw_zero M) (rawNumeralValue M 1) numeralCode numeralCode.
Proof.
  intros M hPA bound numeralCode hnumeral.
  exact (raw_codedTermShift_numeral_identity
    M hPA bound numeralCode (raw_zero M) (rawNumeralValue M 1)
    hnumeral).
Qed.

End PABoundedRawCodedNumeralTermShift.
