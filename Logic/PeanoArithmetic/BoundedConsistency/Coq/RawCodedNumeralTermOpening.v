(**
  Term opening fixes model-internal numeral terms.

  This is the opening analogue of [RawCodedNumeralTermShift].  Its point is
  that the numeral may have nonstandard length in the ambient PA model.  We
  therefore reuse the beta-coded numeral trace itself instead of decoding the
  numeral into a metatheoretic Coq term.

  The second construction is the complementary one-row trace saying that the
  variable exactly at the opening cutoff is replaced.  Together these two
  certificates are the atomic ingredients for substituting a nonstandard
  numeral code into a fixed formula skeleton.
*)

From PAHF Require Import PAHF.
From Coq Require Import Lia.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  BoundedConsistency RawModelCompleteness RawCodedSyntaxConstructors
  RawCodedAssignment RawCodedFormulaRankStep RawCodedFormulaRankTotality
  RawCodedFormulaOperations RawCodedNumeralTermCode
  RawCodedNumeralTermShift.

Module PABoundedRawCodedNumeralTermOpening.

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
Import PABoundedRawCodedNumeralTermShift.

(** The source and target of the opening trace are the same numeral table.
    Consequently the statement is uniform in both the cutoff and the already
    lifted replacement term. *)
Theorem raw_codedTermOpening_numeral_identity : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    bound numeralCode cutoff liftedReplacement,
  RawNumeralTermCodeAt M bound numeralCode ->
  RawCodedTermOpening M
    cutoff liftedReplacement numeralCode numeralCode.
Proof.
  intros M hPA bound numeralCode cutoff liftedReplacement
    (code & step & [hdefined [hzero hrows]] & hroot).
  exists code, step, code, step,
    (raw_succ M bound), bound.
  unfold RawCodedTermOpeningTrace.
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
Qed.

(** A one-node operation trace realizes the active variable case.  The two
    beta tables deliberately carry different arbitrary values, so this lemma
    does not assume that the replacement has standard syntax. *)
Theorem raw_codedTermOpening_variable_at_cutoff : forall
    (M : RawPAModel), RawPASatisfies M -> forall cutoff liftedReplacement,
  RawCodedTermOpening M cutoff liftedReplacement
    (rawTermVarCode M cutoff) liftedReplacement.
Proof.
  intros M hPA cutoff liftedReplacement.
  destruct (finite_vector_beta_code M hPA 1
    (fun _ => rawTermVarCode M cutoff)) as
    [sourceCode [sourceStep hsource]].
  destruct (finite_vector_beta_code M hPA 1
    (fun _ => liftedReplacement)) as
    [targetCode [targetStep htarget]].
  exists sourceCode, sourceStep, targetCode, targetStep,
    (rawNumeralValue M 1), (raw_zero M).
  unfold RawCodedTermOpeningTrace.
  repeat split.
  - intros index hindex.
    destruct (raw_lt_numeralValue_cases M hPA index 1 hindex)
      as [k [hk ->]].
    exists (rawTermVarCode M cutoff). apply hsource. lia.
  - intros index hindex.
    destruct (raw_lt_numeralValue_cases M hPA index 1 hindex)
      as [k [hk ->]].
    exists liftedReplacement. apply htarget. lia.
  - change (rawLt M (rawNumeralValue M 0) (rawNumeralValue M 1)).
    apply raw_lt_numeralValue_of_lt; [exact hPA | lia].
  - change (RawBetaEntry M (rawTermVarCode M cutoff)
      sourceCode sourceStep (rawNumeralValue M 0)).
    exact (hsource 0 ltac:(lia)).
  - change (RawBetaEntry M liftedReplacement
      targetCode targetStep (rawNumeralValue M 0)).
    exact (htarget 0 ltac:(lia)).
  - intros index input output hindex [hinput houtput].
    destruct (raw_lt_numeralValue_cases M hPA index 1 hindex)
      as [k [hk ->]].
    assert (hkZero : k = 0) by lia. subst k.
    assert (hinputCanonical : input = rawTermVarCode M cutoff).
    {
      exact (raw_codedAssignmentLookup_functional M hPA
        sourceCode sourceStep (rawNumeralValue M 0)
        input (rawTermVarCode M cutoff)
        hinput (hsource 0 ltac:(lia))).
    }
    assert (houtputCanonical : output = liftedReplacement).
    {
      exact (raw_codedAssignmentLookup_functional M hPA
        targetCode targetStep (rawNumeralValue M 0)
        output liftedReplacement
        houtput (htarget 0 ltac:(lia))).
    }
    subst input. subst output. left.
    exists cutoff. split; [reflexivity |].
    right. left. split; reflexivity.
Qed.

(** The formula-substitution atom packages capture-avoiding lifting followed
    by opening.  A numeral lifts to itself, and the cutoff variable then opens
    to that same numeral code. *)
Corollary raw_codedFormulaSubstitutionAtom_variable_numeral : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    bound numeralCode depth,
  RawNumeralTermCodeAt M bound numeralCode ->
  RawCodedFormulaSubstitutionAtom M numeralCode depth
    (rawTermVarCode M depth) numeralCode.
Proof.
  intros M hPA bound numeralCode depth hnumeral.
  exists numeralCode. split.
  - exact (raw_codedTermShift_numeral_identity M hPA
      bound numeralCode (raw_zero M) depth hnumeral).
  - exact (raw_codedTermOpening_variable_at_cutoff M hPA
      depth numeralCode).
Qed.

(** Numeral atoms not containing the active variable remain fixed. *)
Corollary raw_codedFormulaSubstitutionAtom_numeral_identity : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    replacementBound replacement inputBound input depth,
  RawNumeralTermCodeAt M replacementBound replacement ->
  RawNumeralTermCodeAt M inputBound input ->
  RawCodedFormulaSubstitutionAtom M replacement depth input input.
Proof.
  intros M hPA replacementBound replacement inputBound input depth
    hreplacement hinput.
  exists replacement. split.
  - exact (raw_codedTermShift_numeral_identity M hPA
      replacementBound replacement (raw_zero M) depth hreplacement).
  - exact (raw_codedTermOpening_numeral_identity M hPA
      inputBound input depth replacement hinput).
Qed.

End PABoundedRawCodedNumeralTermOpening.
