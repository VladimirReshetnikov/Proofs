(**
  Totality boundary for globally closed fixed-level truth certificates.

  The bounded-proof application starts with a formula whose Sigma *or* Pi
  hierarchy rank is at most an external natural [n].  Truth is safely run at
  level [S n]: the two mutually computed hierarchy ranks differ by at most
  one, even for nonstandard formula codes certified by a model-internal rank
  traversal.  The first half of this file proves that rank-gap theorem using
  a PA-definable prefix induction; no external decoder is used.

  The second half records the honest formula/assignment domain and proves a
  PA-internal, arbitrary-value append operation for the four synchronized
  state tables.  Its step-parametric capacity trace works through nonstandard
  bounds.  Full positive-level scheduling additionally needs transport and
  composition of closed rows plus simultaneous adjacent-level certificate
  coherence.  The latter is exposed as an exact PA formula with proved raw
  semantics, but is not postulated or mislabeled as a theorem.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF PAHFOrdinalCodeTotalInduction.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness PolynomialPairInjectivity
  RawCodedSyntaxConstructors RawCodedAssignment
  RawCodedTermEvaluationTraversal RawCodedTermEvaluationRealization
  RawCodedTermEvaluationCapacity
  RawCodedFormulaRankStep
  RawCodedFormulaRankTraversal RawCodedFormulaRankTotality
  RawCodedRankZeroTruthRealization RawCodedFixedLevelTruth
  RawCodedFixedLevelTruthTraversal.

Import ListNotations.

Module PABoundedRawCodedFixedLevelTruthTotality.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedTermEvaluationTraversal.
Import PABoundedRawCodedTermEvaluationRealization.
Import PABoundedRawCodedTermEvaluationCapacity.
Import PABoundedRawCodedFormulaRankStep.
Import PABoundedRawCodedFormulaRankTraversal.
Import PABoundedRawCodedFormulaRankTotality.
Import PABoundedRawCodedRankZeroTruthRealization.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTraversal.

(** ------------------------------------------------------------------
    The Sigma/Pi rank-gap invariant. *)

Definition fixedLevelRankGapTermAt (sigma pi : term) : formula :=
  pAnd
    (Formula.leTermAt sigma (tSucc pi))
    (Formula.leTermAt pi (tSucc sigma)).

Definition RawFixedLevelRankGap (M : RawPAModel) (sigma pi : M) : Prop :=
  rawLe M sigma (raw_succ M pi) /\
  rawLe M pi (raw_succ M sigma).

Arguments RawFixedLevelRankGap M sigma pi : clear implicits.

Lemma raw_sat_fixedLevelRankGapTermAt_iff : forall
    (M : RawPAModel) e sigma pi,
  raw_formula_sat M e (fixedLevelRankGapTermAt sigma pi) <->
  RawFixedLevelRankGap M
    (raw_term_eval M e sigma) (raw_term_eval M e pi).
Proof.
  intros. unfold fixedLevelRankGapTermAt, RawFixedLevelRankGap.
  cbn [raw_formula_sat raw_term_eval].
  rewrite !raw_sat_leTermAt_iff_rank. reflexivity.
Qed.

Lemma raw_fixedLevel_max_components_le : forall
    (M : RawPAModel), RawPASatisfies M -> forall out left right,
  RawMax M out left right ->
  rawLe M left out /\ rawLe M right out.
Proof.
  intros M hPA out left right
    [[hleft ->] | [hright ->]].
  - split; [exact hleft | apply raw_rank_le_refl; exact hPA].
  - split; [apply raw_rank_le_refl; exact hPA | exact hright].
Qed.

Lemma raw_fixedLevel_max_bounded : forall
    (M : RawPAModel), RawPASatisfies M -> forall out left right upper,
  RawMax M out left right ->
  rawLe M left upper -> rawLe M right upper ->
  rawLe M out upper.
Proof.
  intros M hPA out left right upper
    [[_ ->] | [_ ->]] hleft hright; assumption.
Qed.

Lemma raw_fixedLevel_gap_zero : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawFixedLevelRankGap M (raw_zero M) (raw_zero M).
Proof.
  intros M hPA. split;
    apply raw_lt_to_le;
    exact (raw_assignment_lt_self_succ M hPA (raw_zero M)).
Qed.

Lemma raw_fixedLevel_gap_sigma_successor : forall
    (M : RawPAModel), RawPASatisfies M -> forall base,
  RawFixedLevelRankGap M (raw_succ M base) base.
Proof.
  intros M hPA base. split.
  - apply raw_rank_le_refl. exact hPA.
  - apply (raw_le_trans M hPA base (raw_succ M base)
      (raw_succ M (raw_succ M base))).
    + apply raw_lt_to_le.
      exact (raw_assignment_lt_self_succ M hPA base).
    + apply raw_lt_to_le.
      exact (raw_assignment_lt_self_succ M hPA (raw_succ M base)).
Qed.

Lemma raw_fixedLevel_gap_pi_successor : forall
    (M : RawPAModel), RawPASatisfies M -> forall base,
  RawFixedLevelRankGap M base (raw_succ M base).
Proof.
  intros M hPA base. split.
  - apply (raw_le_trans M hPA base (raw_succ M base)
      (raw_succ M (raw_succ M base))).
    + apply raw_lt_to_le.
      exact (raw_assignment_lt_self_succ M hPA base).
    + apply raw_lt_to_le.
      exact (raw_assignment_lt_self_succ M hPA (raw_succ M base)).
  - apply raw_rank_le_refl. exact hPA.
Qed.

Lemma raw_fixedLevel_gap_parallel_max : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall sigma pi leftSigma leftPi rightSigma rightPi,
  RawFixedLevelRankGap M leftSigma leftPi ->
  RawFixedLevelRankGap M rightSigma rightPi ->
  RawMax M sigma leftSigma rightSigma ->
  RawMax M pi leftPi rightPi ->
  RawFixedLevelRankGap M sigma pi.
Proof.
  intros M hPA sigma pi leftSigma leftPi rightSigma rightPi
    [hleftSigma hleftPi] [hrightSigma hrightPi]
    hsigma hpi.
  destruct (raw_fixedLevel_max_components_le M hPA
    pi leftPi rightPi hpi) as [hleftPiMax hrightPiMax].
  destruct (raw_fixedLevel_max_components_le M hPA
    sigma leftSigma rightSigma hsigma) as [hleftSigmaMax hrightSigmaMax].
  split.
  - apply (raw_fixedLevel_max_bounded M hPA
      sigma leftSigma rightSigma (raw_succ M pi) hsigma).
    + exact (raw_le_trans M hPA leftSigma (raw_succ M leftPi)
        (raw_succ M pi) hleftSigma
        (raw_rank_succ_le M hPA leftPi pi hleftPiMax)).
    + exact (raw_le_trans M hPA rightSigma (raw_succ M rightPi)
        (raw_succ M pi) hrightSigma
        (raw_rank_succ_le M hPA rightPi pi hrightPiMax)).
  - apply (raw_fixedLevel_max_bounded M hPA
      pi leftPi rightPi (raw_succ M sigma) hpi).
    + exact (raw_le_trans M hPA leftPi (raw_succ M leftSigma)
        (raw_succ M sigma) hleftPi
        (raw_rank_succ_le M hPA leftSigma sigma hleftSigmaMax)).
    + exact (raw_le_trans M hPA rightPi (raw_succ M rightSigma)
        (raw_succ M sigma) hrightPi
        (raw_rank_succ_le M hPA rightSigma sigma hrightSigmaMax)).
Qed.

Lemma raw_fixedLevel_gap_cross_max : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall sigma pi leftSigma leftPi rightSigma rightPi,
  RawFixedLevelRankGap M leftSigma leftPi ->
  RawFixedLevelRankGap M rightSigma rightPi ->
  RawMax M sigma leftPi rightSigma ->
  RawMax M pi leftSigma rightPi ->
  RawFixedLevelRankGap M sigma pi.
Proof.
  intros M hPA sigma pi leftSigma leftPi rightSigma rightPi
    [hleftSigma hleftPi] [hrightSigma hrightPi]
    hsigma hpi.
  destruct (raw_fixedLevel_max_components_le M hPA
    pi leftSigma rightPi hpi) as [hleftSigmaMax hrightPiMax].
  destruct (raw_fixedLevel_max_components_le M hPA
    sigma leftPi rightSigma hsigma) as [hleftPiMax hrightSigmaMax].
  split.
  - apply (raw_fixedLevel_max_bounded M hPA
      sigma leftPi rightSigma (raw_succ M pi) hsigma).
    + exact (raw_le_trans M hPA leftPi (raw_succ M leftSigma)
        (raw_succ M pi) hleftPi
        (raw_rank_succ_le M hPA leftSigma pi hleftSigmaMax)).
    + exact (raw_le_trans M hPA rightSigma (raw_succ M rightPi)
        (raw_succ M pi) hrightSigma
        (raw_rank_succ_le M hPA rightPi pi hrightPiMax)).
  - apply (raw_fixedLevel_max_bounded M hPA
      pi leftSigma rightPi (raw_succ M sigma) hpi).
    + exact (raw_le_trans M hPA leftSigma (raw_succ M leftPi)
        (raw_succ M sigma) hleftSigma
        (raw_rank_succ_le M hPA leftPi sigma hleftPiMax)).
    + exact (raw_le_trans M hPA rightPi (raw_succ M rightSigma)
        (raw_succ M sigma) hrightPi
        (raw_rank_succ_le M hPA rightSigma sigma hrightSigmaMax)).
Qed.

(** Local preservation of the gap by every rank row.  Recursive child gap
    facts are supplied only for the strictly earlier rows named by the row. *)
Lemma raw_codedFormulaRankTraversalRow_gap : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    index code sigma pi,
  RawCodedFormulaRankTraversalRow M
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    index code sigma pi ->
  (forall childIndex child childSigma childPi,
    rawLt M childIndex index ->
    RawCodedFormulaRankTripleLookup M
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      childIndex child childSigma childPi ->
    RawFixedLevelRankGap M childSigma childPi) ->
  RawFixedLevelRankGap M sigma pi.
Proof.
  intros M hPA formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    index code sigma pi hrow hchildren.
  destruct hrow as [heq | [hbot | [himp | [hand | [hor | [hall | hex]]]]]].
  - destruct heq as [left [right [_ [-> ->]]]].
    apply raw_fixedLevel_gap_zero. exact hPA.
  - destruct hbot as [_ [-> ->]].
    apply raw_fixedLevel_gap_zero. exact hPA.
  - destruct himp as
      (li & left & ls & lp & ri & right & rs & rp &
       hli & hleft & hri & hright & _ & [hsigma hpi]).
    apply (raw_fixedLevel_gap_cross_max M hPA
      sigma pi ls lp rs rp).
    + exact (hchildren li left ls lp hli hleft).
    + exact (hchildren ri right rs rp hri hright).
    + exact hsigma.
    + exact hpi.
  - destruct hand as
      (li & left & ls & lp & ri & right & rs & rp &
       hli & hleft & hri & hright & _ & [hsigma hpi]).
    apply (raw_fixedLevel_gap_parallel_max M hPA
      sigma pi ls lp rs rp).
    + exact (hchildren li left ls lp hli hleft).
    + exact (hchildren ri right rs rp hri hright).
    + exact hsigma.
    + exact hpi.
  - destruct hor as
      (li & left & ls & lp & ri & right & rs & rp &
       hli & hleft & hri & hright & _ & [hsigma hpi]).
    apply (raw_fixedLevel_gap_parallel_max M hPA
      sigma pi ls lp rs rp).
    + exact (hchildren li left ls lp hli hleft).
    + exact (hchildren ri right rs rp hri hright).
    + exact hsigma.
    + exact hpi.
  - destruct hall as
      (ci & child & cs & cp & hci & hchild & _ &
       base & _ & hpi & hsigma).
    rewrite hpi, hsigma.
    apply raw_fixedLevel_gap_sigma_successor. exact hPA.
  - destruct hex as
      (ci & child & cs & cp & hci & hchild & _ &
       base & _ & hsigma & hpi).
    rewrite hsigma, hpi.
    apply raw_fixedLevel_gap_pi_successor. exact hPA.
Qed.

(** ------------------------------------------------------------------
    PA-definable prefix induction for the gap. *)

Definition codedFormulaRankGapRowsTermAt
    (formulaCode formulaStep sigmaCode sigmaStep piCode piStep bound : term)
    : formula :=
  pAll (pAll (pAll (pAll
    (pImp
      (Formula.ltTermAt (tVar 3) (liftTerm 4 bound))
      (pImp
        (codedFormulaRankTripleLookupTermAt
          (liftTerm 4 formulaCode) (liftTerm 4 formulaStep)
          (liftTerm 4 sigmaCode) (liftTerm 4 sigmaStep)
          (liftTerm 4 piCode) (liftTerm 4 piStep)
          (tVar 3) (tVar 2) (tVar 1) (tVar 0))
        (fixedLevelRankGapTermAt (tVar 1) (tVar 0))))))).

Definition RawCodedFormulaRankGapRows (M : RawPAModel)
    (formulaCode formulaStep sigmaCode sigmaStep piCode piStep bound : M)
    : Prop :=
  forall index code sigma pi : M,
    rawLt M index bound ->
    RawCodedFormulaRankTripleLookup M
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      index code sigma pi ->
    RawFixedLevelRankGap M sigma pi.

Arguments RawCodedFormulaRankGapRows
  M formulaCode formulaStep sigmaCode sigmaStep piCode piStep bound
  : clear implicits.

Lemma raw_sat_codedFormulaRankGapRowsTermAt_iff : forall
    (M : RawPAModel) e
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep bound,
  raw_formula_sat M e
    (codedFormulaRankGapRowsTermAt
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep bound) <->
  RawCodedFormulaRankGapRows M
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e sigmaCode) (raw_term_eval M e sigmaStep)
    (raw_term_eval M e piCode) (raw_term_eval M e piStep)
    (raw_term_eval M e bound).
Proof.
  intros. unfold codedFormulaRankGapRowsTermAt,
    RawCodedFormulaRankGapRows.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedFormulaRankTripleLookupTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelRankGapTermAt_iff.
  repeat setoid_rewrite raw_rankTraversal_eval_liftTerm_four.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_codedFormulaRankGapRows_zero : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall formulaCode formulaStep sigmaCode sigmaStep piCode piStep,
  RawCodedFormulaRankGapRows M
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep (raw_zero M).
Proof.
  intros M hPA formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    index code sigma pi hindex.
  exfalso. exact (raw_not_lt_zero M hPA index hindex).
Qed.

Lemma raw_codedFormulaRankGapRows_succ : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root rootSigma rootPi current,
  RawCodedFormulaRankTraversal M
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root rootSigma rootPi ->
  rawLt M current bound ->
  RawCodedFormulaRankGapRows M
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep current ->
  RawCodedFormulaRankGapRows M
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    (raw_succ M current).
Proof.
  intros M hPA formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root rootSigma rootPi current
    [_ [_ [_ [_ [_ hrows]]]]] hcurrent hprefix
    index code sigma pi hindex hlookup.
  destruct (raw_lt_succ_cases M hPA index current hindex)
    as [hbefore | ->].
  - exact (hprefix index code sigma pi hbefore hlookup).
  - apply (raw_codedFormulaRankTraversalRow_gap M hPA
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      current code sigma pi).
    + exact (hrows current code sigma pi hcurrent hlookup).
    + intros childIndex child childSigma childPi hchild hchildLookup.
      exact (hprefix childIndex child childSigma childPi
        hchild hchildLookup).
Qed.

Definition codedFormulaRankGapRowsWithinTermAt
    (formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      bound current : term) : formula :=
  pImp
    (Formula.leTermAt current bound)
    (codedFormulaRankGapRowsTermAt
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep current).

Definition RawCodedFormulaRankGapRowsWithin (M : RawPAModel)
    (formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      bound current : M) : Prop :=
  rawLe M current bound ->
  RawCodedFormulaRankGapRows M
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep current.

Arguments RawCodedFormulaRankGapRowsWithin
  M formulaCode formulaStep sigmaCode sigmaStep piCode piStep bound current
  : clear implicits.

Lemma raw_sat_codedFormulaRankGapRowsWithinTermAt_iff : forall
    (M : RawPAModel) e
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep bound current,
  raw_formula_sat M e
    (codedFormulaRankGapRowsWithinTermAt
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      bound current) <->
  RawCodedFormulaRankGapRowsWithin M
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e sigmaCode) (raw_term_eval M e sigmaStep)
    (raw_term_eval M e piCode) (raw_term_eval M e piStep)
    (raw_term_eval M e bound) (raw_term_eval M e current).
Proof.
  intros. unfold codedFormulaRankGapRowsWithinTermAt,
    RawCodedFormulaRankGapRowsWithin.
  cbn [raw_formula_sat].
  rewrite raw_sat_leTermAt_iff_rank,
    raw_sat_codedFormulaRankGapRowsTermAt_iff.
  reflexivity.
Qed.

Lemma raw_codedFormulaRankGapRowsWithin_succ : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root rootSigma rootPi current,
  RawCodedFormulaRankTraversal M
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root rootSigma rootPi ->
  RawCodedFormulaRankGapRowsWithin M
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep bound current ->
  RawCodedFormulaRankGapRowsWithin M
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound (raw_succ M current).
Proof.
  intros M hPA formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root rootSigma rootPi current htraversal hcurrent
    hsuccBound.
  assert (hcurrentLe : rawLe M current bound).
  {
    apply (raw_le_trans M hPA current (raw_succ M current) bound).
    - apply raw_lt_to_le.
      exact (raw_assignment_lt_self_succ M hPA current).
    - exact hsuccBound.
  }
  exact (raw_codedFormulaRankGapRows_succ M hPA
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root rootSigma rootPi current htraversal
    (raw_rank_lt_of_succ_le M hPA current bound hsuccBound)
    (hcurrent hcurrentLe)).
Qed.

Theorem raw_codedFormulaRankGapRows_all : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root rootSigma rootPi,
  RawCodedFormulaRankTraversal M
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root rootSigma rootPi ->
  forall current,
  RawCodedFormulaRankGapRowsWithin M
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep bound current.
Proof.
  intros M hPA formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root rootSigma rootPi htraversal.
  set (parameterEnv := fun n : nat =>
    match n with
    | 0 => formulaCode
    | 1 => formulaStep
    | 2 => sigmaCode
    | 3 => sigmaStep
    | 4 => piCode
    | 5 => piStep
    | _ => bound
    end).
  set (phi := codedFormulaRankGapRowsWithinTermAt
    (tVar 1) (tVar 2) (tVar 3) (tVar 4)
    (tVar 5) (tVar 6) (tVar 7) (tVar 0)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2 (raw_sat_codedFormulaRankGapRowsWithinTermAt_iff M
        (scons M (raw_zero M) parameterEnv)
        (tVar 1) (tVar 2) (tVar 3) (tVar 4)
        (tVar 5) (tVar 6) (tVar 7) (tVar 0))).
      unfold parameterEnv. cbn [raw_term_eval scons].
      intros _.
      exact (raw_codedFormulaRankGapRows_zero M hPA
        formulaCode formulaStep sigmaCode sigmaStep piCode piStep).
    - intros current hcurrentSat.
      unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_codedFormulaRankGapRowsWithinTermAt_iff M
          (scons M current parameterEnv)
          (tVar 1) (tVar 2) (tVar 3) (tVar 4)
          (tVar 5) (tVar 6) (tVar 7) (tVar 0))
        hcurrentSat) as hcurrent.
      apply (proj2
        (raw_sat_codedFormulaRankGapRowsWithinTermAt_iff M
          (scons M (raw_succ M current) parameterEnv)
          (tVar 1) (tVar 2) (tVar 3) (tVar 4)
          (tVar 5) (tVar 6) (tVar 7) (tVar 0))).
      unfold parameterEnv in hcurrent |- *.
      cbn [raw_term_eval scons] in hcurrent |- *.
      exact (raw_codedFormulaRankGapRowsWithin_succ M hPA
        formulaCode formulaStep sigmaCode sigmaStep piCode piStep
        bound rootIndex root rootSigma rootPi current
        htraversal hcurrent).
  }
  intro current.
  unfold phi in hall.
  pose proof (proj1
    (raw_sat_codedFormulaRankGapRowsWithinTermAt_iff M
      (scons M current parameterEnv)
      (tVar 1) (tVar 2) (tVar 3) (tVar 4)
      (tVar 5) (tVar 6) (tVar 7) (tVar 0))
    (hall current)) as hraw.
  unfold parameterEnv in hraw.
  cbn [raw_term_eval scons] in hraw. exact hraw.
Qed.

Theorem raw_codedFormulaRankTraversal_gap : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root sigma pi,
  RawCodedFormulaRankTraversal M
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root sigma pi ->
  RawFixedLevelRankGap M sigma pi.
Proof.
  intros M hPA formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root sigma pi htraversal.
  pose proof (raw_codedFormulaRankGapRows_all M hPA
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root sigma pi htraversal bound) as hwithin.
  destruct htraversal as
    [_ [_ [_ [hrootIndex [hrootLookup _]]]]].
  exact ((hwithin (raw_rank_le_refl M hPA bound))
    rootIndex root sigma pi hrootIndex hrootLookup).
Qed.

Corollary raw_codedFormulaRank_gap : forall
    (M : RawPAModel), RawPASatisfies M -> forall root sigma pi,
  RawCodedFormulaRank M root sigma pi ->
  RawFixedLevelRankGap M sigma pi.
Proof.
  intros M hPA root sigma pi
    (formulaCode & formulaStep & sigmaCode & sigmaStep &
     piCode & piStep & bound & rootIndex & htraversal).
  exact (raw_codedFormulaRankTraversal_gap M hPA
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root sigma pi htraversal).
Qed.

(** The rank-gap calibration requested by the bounded-proof application. *)
Theorem raw_fixedLevel_rank_bound_both_at_successor : forall
    (M : RawPAModel), RawPASatisfies M -> forall level code,
  (RawFixedLevelSigmaDomain M level code \/
   RawFixedLevelPiDomain M level code) ->
  RawFixedLevelSigmaDomain M (S level) code /\
  RawFixedLevelPiDomain M (S level) code.
Proof.
  intros M hPA level code [hsigma | hpi].
  - destruct hsigma as [sigma [pi [hrank hsigmaBound]]].
    destruct (raw_codedFormulaRank_gap M hPA code sigma pi hrank)
      as [hsigmaGap hpiGap].
    split.
    + exact (raw_fixedLevelSigmaDomain_mono M hPA level code
        (ex_intro _ sigma (ex_intro _ pi (conj hrank hsigmaBound)))).
    + exists sigma, pi. split; [exact hrank |].
      change (rawLe M pi (raw_succ M (rawNumeralValue M level))).
      exact (raw_le_trans M hPA pi (raw_succ M sigma)
        (raw_succ M (rawNumeralValue M level)) hpiGap
        (raw_rank_succ_le M hPA sigma
          (rawNumeralValue M level) hsigmaBound)).
  - destruct hpi as [sigma [pi [hrank hpiBound]]].
    destruct (raw_codedFormulaRank_gap M hPA code sigma pi hrank)
      as [hsigmaGap hpiGap].
    split.
    + exists sigma, pi. split; [exact hrank |].
      change (rawLe M sigma (raw_succ M (rawNumeralValue M level))).
      exact (raw_le_trans M hPA sigma (raw_succ M pi)
        (raw_succ M (rawNumeralValue M level)) hsigmaGap
        (raw_rank_succ_le M hPA pi
          (rawNumeralValue M level) hpiBound)).
    + exact (raw_fixedLevelPiDomain_mono M hPA level code
        (ex_intro _ sigma (ex_intro _ pi (conj hrank hpiBound)))).
Qed.

(** ------------------------------------------------------------------
    An honest arithmetized input domain.

    [RawCodedWellFormedFormula] deliberately checks only the formula tree:
    an equality row may still contain arbitrary carrier elements as its two
    purported term codes.  Truth totality therefore needs a little more than
    formula well-formedness.  The predicate below reuses one certified formula
    postorder and requires each equality payload to carry genuine term syntax
    for every assignment which is defined through the containing formula
    code.  The universal assignment clause is stable under the binder
    extensions used by the truth clauses; it does not assert truth, falsity,
    or the existence of a truth schedule.

    Six binders below are, from outermost to innermost, the formula-row index,
    formula code, left term code, right term code, assignment code, and
    assignment step.  At the body they occupy variables 5 down to 0. *)

Lemma raw_fixedTruthTotality_eval_liftTerm_six : forall
    (M : RawPAModel) a b c d f g (e : nat -> M) t,
  raw_term_eval M
    (scons M a (scons M b (scons M c (scons M d
      (scons M f (scons M g e))))))
    (liftTerm 6 t) = raw_term_eval M e t.
Proof.
  intros M a b c d f g e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro i.
  replace (i + 6) with (S (S (S (S (S (S i)))))) by lia.
  reflexivity.
Qed.

Definition fixedTruthTotalityAll6 (body : formula) : formula :=
  pAll (pAll (pAll (pAll (pAll (pAll body))))).

Definition codedFormulaAtomicTermAdequateTermAt
    (formulaCode formulaStep bound : term) : formula :=
  fixedTruthTotalityAll6
    (pImp
      (Formula.ltTermAt (tVar 5) (liftTerm 6 bound))
      (pImp
        (codedAssignmentLookupTermAt
          (liftTerm 6 formulaCode) (liftTerm 6 formulaStep)
          (tVar 5) (tVar 4))
        (pImp
          (formulaEqCodeTermAt (tVar 4) (tVar 3) (tVar 2))
          (pImp
            (codedAssignmentDefinedThroughTermAt
              (tVar 1) (tVar 0) (tVar 4))
            (pAnd
              (termSyntaxRealizableTermAt
                (tVar 3) (tVar 1) (tVar 0))
              (termSyntaxRealizableTermAt
                (tVar 2) (tVar 1) (tVar 0))))))).

Definition RawCodedFormulaAtomicTermAdequate (M : RawPAModel)
    (formulaCode formulaStep bound : M) : Prop :=
  forall index code left right assignmentCode assignmentStep : M,
    rawLt M index bound ->
    RawCodedAssignmentLookup M formulaCode formulaStep index code ->
    code = rawFormulaEqCode M left right ->
    RawCodedAssignmentDefinedThrough M
      assignmentCode assignmentStep code ->
    RawTermSyntaxRealizable M left assignmentCode assignmentStep /\
    RawTermSyntaxRealizable M right assignmentCode assignmentStep.

Arguments RawCodedFormulaAtomicTermAdequate
  M formulaCode formulaStep bound : clear implicits.

Lemma raw_sat_codedFormulaAtomicTermAdequateTermAt_iff : forall
    (M : RawPAModel) e formulaCode formulaStep bound,
  raw_formula_sat M e
    (codedFormulaAtomicTermAdequateTermAt
      formulaCode formulaStep bound) <->
  RawCodedFormulaAtomicTermAdequate M
    (raw_term_eval M e formulaCode)
    (raw_term_eval M e formulaStep)
    (raw_term_eval M e bound).
Proof.
  intros. unfold codedFormulaAtomicTermAdequateTermAt,
    fixedTruthTotalityAll6,
    RawCodedFormulaAtomicTermAdequate.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedAssignmentLookupTermAt_iff.
  setoid_rewrite raw_sat_formulaEqCodeTermAt_iff.
  setoid_rewrite raw_sat_codedAssignmentDefinedThroughTermAt_iff.
  setoid_rewrite raw_sat_termSyntaxRealizableTermAt_iff.
  repeat setoid_rewrite raw_fixedTruthTotality_eval_liftTerm_six.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition codedFormulaAtomicallyAdequateTermAt (root : term) : formula :=
  pEx (pEx (pEx (pEx
    (pAnd
      (codedFormulaSyntaxTraversalTermAt
        (tVar 3) (tVar 2) (tVar 1) (tVar 0) (liftTerm 4 root))
      (codedFormulaAtomicTermAdequateTermAt
        (tVar 3) (tVar 2) (tVar 1)))))).

Definition RawCodedFormulaAtomicallyAdequate (M : RawPAModel)
    (root : M) : Prop :=
  exists formulaCode formulaStep bound rootIndex : M,
    RawCodedFormulaSyntaxTraversal M
      formulaCode formulaStep bound rootIndex root /\
    RawCodedFormulaAtomicTermAdequate M
      formulaCode formulaStep bound.

Arguments RawCodedFormulaAtomicallyAdequate M root : clear implicits.

Lemma raw_sat_codedFormulaAtomicallyAdequateTermAt_iff : forall
    (M : RawPAModel) e root,
  raw_formula_sat M e (codedFormulaAtomicallyAdequateTermAt root) <->
  RawCodedFormulaAtomicallyAdequate M (raw_term_eval M e root).
Proof.
  intros. unfold codedFormulaAtomicallyAdequateTermAt,
    RawCodedFormulaAtomicallyAdequate.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_codedFormulaSyntaxTraversalTermAt_iff.
  setoid_rewrite raw_sat_codedFormulaAtomicTermAdequateTermAt_iff.
  repeat setoid_rewrite raw_rankTraversal_eval_liftTerm_four.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition fixedLevelTruthAdmissibleTermAt (level : nat)
    (root assignmentCode assignmentStep : term) : formula :=
  pAnd
    (codedFormulaAtomicallyAdequateTermAt root)
    (pAnd
      (codedAssignmentDefinedThroughTermAt
        assignmentCode assignmentStep root)
      (pOr
        (fixedLevelSigmaDomainTermAt level root)
        (fixedLevelPiDomainTermAt level root))).

Definition RawFixedLevelTruthAdmissible (M : RawPAModel) (level : nat)
    (root assignmentCode assignmentStep : M) : Prop :=
  RawCodedFormulaAtomicallyAdequate M root /\
  RawCodedAssignmentDefinedThrough M
    assignmentCode assignmentStep root /\
  (RawFixedLevelSigmaDomain M level root \/
   RawFixedLevelPiDomain M level root).

Arguments RawFixedLevelTruthAdmissible
  M level root assignmentCode assignmentStep : clear implicits.

Lemma raw_sat_fixedLevelTruthAdmissibleTermAt_iff : forall
    (M : RawPAModel) e level root assignmentCode assignmentStep,
  raw_formula_sat M e
    (fixedLevelTruthAdmissibleTermAt
      level root assignmentCode assignmentStep) <->
  RawFixedLevelTruthAdmissible M level
    (raw_term_eval M e root)
    (raw_term_eval M e assignmentCode)
    (raw_term_eval M e assignmentStep).
Proof.
  intros. unfold fixedLevelTruthAdmissibleTermAt,
    RawFixedLevelTruthAdmissible.
  cbn [raw_formula_sat].
  rewrite raw_sat_codedFormulaAtomicallyAdequateTermAt_iff,
    raw_sat_codedAssignmentDefinedThroughTermAt_iff,
    raw_sat_fixedLevelSigmaDomainTermAt_iff,
    raw_sat_fixedLevelPiDomainTermAt_iff.
  reflexivity.
Qed.

Lemma raw_fixedLevelTruthAdmissible_wellFormed : forall
    (M : RawPAModel) level root assignmentCode assignmentStep,
  RawFixedLevelTruthAdmissible M level
    root assignmentCode assignmentStep ->
  RawCodedWellFormedFormula M root.
Proof.
  intros M level root assignmentCode assignmentStep
    [[formulaCode [formulaStep [bound [rootIndex [htraversal _]]]]] _].
  exists formulaCode, formulaStep, bound, rootIndex. exact htraversal.
Qed.

Theorem raw_fixedLevelTruthAdmissible_successor_domains : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall level root assignmentCode assignmentStep,
  RawFixedLevelTruthAdmissible M level
    root assignmentCode assignmentStep ->
  RawFixedLevelSigmaDomain M (S level) root /\
  RawFixedLevelPiDomain M (S level) root.
Proof.
  intros M hPA level root assignmentCode assignmentStep
    [_ [_ hdomain]].
  exact (raw_fixedLevel_rank_bound_both_at_successor
    M hPA level root hdomain).
Qed.

(** ------------------------------------------------------------------
    Model-internal arbitrary-value beta append.

    A fixed beta step cannot directly append an arbitrary carrier value: the
    one-entry CRT theorem requires the value to be smaller than the target
    modulus.  We avoid that circularity with the same step-parametric capacity
    method used for term evaluation.  At every internal prefix [current] a
    capacity works uniformly for every sufficiently large common-multiple
    step.  The successor capacity adds the next source value, making that
    value small enough for [raw_betaCodeExtension_exists].

    The source here is especially simple: preserve [oldCode] below [bound]
    and place [newValue] at [bound].  Nevertheless the iteration through the
    possibly nonstandard prefix is PA's definable induction, not Rocq
    recursion on a decoded list. *)

Definition RawCodedAssignmentAppendPrefix (M : RawPAModel)
    (current oldCode oldStep bound newValue targetCode targetStep : M)
    : Prop :=
  RawCodedAssignmentDefinedThrough M targetCode targetStep current /\
  (forall index value : M,
    rawLt M index current ->
    rawLt M index bound ->
    RawCodedAssignmentLookup M oldCode oldStep index value ->
    RawCodedAssignmentLookup M targetCode targetStep index value) /\
  (rawLt M bound current ->
    RawCodedAssignmentLookup M
      targetCode targetStep bound newValue).

Arguments RawCodedAssignmentAppendPrefix
  M current oldCode oldStep bound newValue targetCode targetStep
  : clear implicits.

Definition codedAssignmentAppendPrefixTermAt
    (current oldCode oldStep bound newValue targetCode targetStep : term)
    : formula :=
  pAnd
    (codedAssignmentDefinedThroughTermAt targetCode targetStep current)
    (pAnd
      (pAll (pAll
        (pImp
          (Formula.ltTermAt (tVar 1) (liftTerm 2 current))
          (pImp
            (Formula.ltTermAt (tVar 1) (liftTerm 2 bound))
            (pImp
              (codedAssignmentLookupTermAt
                (liftTerm 2 oldCode) (liftTerm 2 oldStep)
                (tVar 1) (tVar 0))
              (codedAssignmentLookupTermAt
                (liftTerm 2 targetCode) (liftTerm 2 targetStep)
                (tVar 1) (tVar 0)))))))
      (pImp
        (Formula.ltTermAt bound current)
        (codedAssignmentLookupTermAt
          targetCode targetStep bound newValue))).

Lemma raw_sat_codedAssignmentAppendPrefixTermAt_iff : forall
    (M : RawPAModel) e current oldCode oldStep bound newValue
      targetCode targetStep,
  raw_formula_sat M e
    (codedAssignmentAppendPrefixTermAt
      current oldCode oldStep bound newValue targetCode targetStep) <->
  RawCodedAssignmentAppendPrefix M
    (raw_term_eval M e current)
    (raw_term_eval M e oldCode) (raw_term_eval M e oldStep)
    (raw_term_eval M e bound) (raw_term_eval M e newValue)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep).
Proof.
  intros. unfold codedAssignmentAppendPrefixTermAt,
    RawCodedAssignmentAppendPrefix.
  cbn [raw_formula_sat].
  rewrite raw_sat_codedAssignmentDefinedThroughTermAt_iff.
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedAssignmentLookupTermAt_iff.
  cbn [raw_term_eval scons]. split.
  - intros [hdefined [hprefix hnew]]. split; [exact hdefined |]. split.
    + intros index value hcurrent hbound hold.
      try rewrite !raw_term_eval_liftTerm_two_traversal in hcurrent.
      try rewrite !raw_term_eval_liftTerm_two_traversal in hbound.
      try rewrite !raw_term_eval_liftTerm_two_traversal in hold.
      try rewrite !raw_term_eval_liftTerm_two_traversal.
      specialize (hprefix index value).
      rewrite !raw_term_eval_liftTerm_two_traversal in hprefix.
      exact (hprefix hcurrent hbound hold).
    + exact hnew.
  - intros [hdefined [hprefix hnew]]. split; [exact hdefined |]. split.
    + intros index value hcurrent hbound hold.
      try rewrite !raw_term_eval_liftTerm_two_traversal in hcurrent.
      try rewrite !raw_term_eval_liftTerm_two_traversal in hbound.
      try rewrite !raw_term_eval_liftTerm_two_traversal in hold.
      try rewrite !raw_term_eval_liftTerm_two_traversal.
      exact (hprefix index value hcurrent hbound hold).
    + exact hnew.
Qed.

Definition RawCodedAssignmentAppendTraceCapacity (M : RawPAModel)
    (current oldCode oldStep bound newValue : M) : Prop :=
  exists capacity : M,
    forall targetStep : M,
      RawTermEvaluationCodingStep M current capacity targetStep ->
      exists targetCode : M,
        RawCodedAssignmentAppendPrefix M
          current oldCode oldStep bound newValue targetCode targetStep.

Arguments RawCodedAssignmentAppendTraceCapacity
  M current oldCode oldStep bound newValue : clear implicits.

Definition codedAssignmentAppendTraceCapacityTermAt
    (current oldCode oldStep bound newValue : term) : formula :=
  pEx (pAll
    (pImp
      (Formula.betaCodingStepTermAt
        (liftTerm 2 current) (tVar 1) (tVar 0))
      (pEx
        (codedAssignmentAppendPrefixTermAt
          (liftTerm 3 current)
          (liftTerm 3 oldCode) (liftTerm 3 oldStep)
          (liftTerm 3 bound) (liftTerm 3 newValue)
          (tVar 0) (tVar 1))))).

Lemma raw_sat_codedAssignmentAppendTraceCapacityTermAt_iff : forall
    (M : RawPAModel) e current oldCode oldStep bound newValue,
  raw_formula_sat M e
    (codedAssignmentAppendTraceCapacityTermAt
      current oldCode oldStep bound newValue) <->
  RawCodedAssignmentAppendTraceCapacity M
    (raw_term_eval M e current)
    (raw_term_eval M e oldCode) (raw_term_eval M e oldStep)
    (raw_term_eval M e bound) (raw_term_eval M e newValue).
Proof.
  intros. unfold codedAssignmentAppendTraceCapacityTermAt,
    RawCodedAssignmentAppendTraceCapacity.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_termEvaluationCodingStepTermAt_iff.
  setoid_rewrite raw_sat_codedAssignmentAppendPrefixTermAt_iff.
  repeat setoid_rewrite raw_term_eval_liftTerm_two_traversal.
  repeat setoid_rewrite raw_term_eval_liftTerm_three_traversal.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition RawCodedAssignmentAppendTraceCapacityThrough (M : RawPAModel)
    (current limit oldCode oldStep bound newValue : M) : Prop :=
  rawLe M current limit ->
  RawCodedAssignmentAppendTraceCapacity M
    current oldCode oldStep bound newValue.

Arguments RawCodedAssignmentAppendTraceCapacityThrough
  M current limit oldCode oldStep bound newValue : clear implicits.

Definition codedAssignmentAppendTraceCapacityThroughTermAt
    (current limit oldCode oldStep bound newValue : term) : formula :=
  pImp
    (Formula.leTermAt current limit)
    (codedAssignmentAppendTraceCapacityTermAt
      current oldCode oldStep bound newValue).

Lemma raw_sat_codedAssignmentAppendTraceCapacityThroughTermAt_iff : forall
    (M : RawPAModel) e current limit oldCode oldStep bound newValue,
  raw_formula_sat M e
    (codedAssignmentAppendTraceCapacityThroughTermAt
      current limit oldCode oldStep bound newValue) <->
  RawCodedAssignmentAppendTraceCapacityThrough M
    (raw_term_eval M e current) (raw_term_eval M e limit)
    (raw_term_eval M e oldCode) (raw_term_eval M e oldStep)
    (raw_term_eval M e bound) (raw_term_eval M e newValue).
Proof.
  intros. unfold codedAssignmentAppendTraceCapacityThroughTermAt,
    RawCodedAssignmentAppendTraceCapacityThrough.
  cbn [raw_formula_sat].
  rewrite raw_sat_leTermAt_iff_rank,
    raw_sat_codedAssignmentAppendTraceCapacityTermAt_iff.
  reflexivity.
Qed.

Lemma raw_codedAssignmentAppendTraceCapacity_zero : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall oldCode oldStep bound newValue,
  RawCodedAssignmentAppendTraceCapacity M (raw_zero M)
    oldCode oldStep bound newValue.
Proof.
  intros M hPA oldCode oldStep bound newValue.
  exists (raw_zero M). intros targetStep _.
  exists (raw_zero M). split.
  - intros index hindex. exfalso.
    exact (raw_not_lt_zero M hPA index hindex).
  - split.
    + intros index value hindex. exfalso.
      exact (raw_not_lt_zero M hPA index hindex).
    + intros hbound. exfalso.
      exact (raw_not_lt_zero M hPA bound hbound).
Qed.

(** The successor calculation is split at [current < bound] versus
    [current = bound].  In the first case the next source value comes from the
    old table.  In the second it is the arbitrary value being appended. *)
Lemma raw_codedAssignmentAppendTraceCapacity_succ : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall oldCode oldStep bound newValue current,
  RawCodedAssignmentDefinedThrough M oldCode oldStep bound ->
  rawLt M current (raw_succ M bound) ->
  RawCodedAssignmentAppendTraceCapacity M
    current oldCode oldStep bound newValue ->
  RawCodedAssignmentAppendTraceCapacity M
    (raw_succ M current) oldCode oldStep bound newValue.
Proof.
  intros M hPA oldCode oldStep bound newValue current
    holdDefined hcurrent [oldCapacity holdCapacity].
  destruct (raw_lt_succ_cases M hPA current bound hcurrent)
    as [hcurrentBound | hcurrentBound].
  - destruct (holdDefined current hcurrentBound)
      as [sourceValue hsourceValue].
    exists (raw_add M oldCapacity sourceValue).
    intros targetStep hnewCoding.
    pose proof (raw_termEvaluationCodingStep_old_of_sum M hPA
      current oldCapacity sourceValue targetStep hnewCoding)
      as holdCoding.
    destruct (holdCapacity targetStep holdCoding)
      as [targetCode [htargetDefined [htargetPrefix htargetNew]]].
    assert (hvalueBound : rawLt M sourceValue
        (rawBetaModulus M targetStep current)).
    {
      exact (raw_termEvaluationCodingStep_value_bound M hPA
        current oldCapacity sourceValue targetStep hnewCoding).
    }
    destruct (raw_betaCodeExtension_exists M hPA
      targetCode targetStep current sourceValue
      (proj1 holdCoding) hvalueBound)
      as [newTargetCode hext].
    exists newTargetCode. split.
    + exact (raw_rank_betaExtension_defined_succ M hPA
        targetCode targetStep current sourceValue newTargetCode
        htargetDefined hext).
    + split.
      * intros index value hindexSucc hindexBound hvalue.
        destruct (raw_lt_succ_cases M hPA index current hindexSucc)
          as [hindexCurrent | ->].
        -- unfold RawCodedAssignmentLookup in *.
           exact ((proj1 hext) index hindexCurrent value
             (htargetPrefix index value
               hindexCurrent hindexBound hvalue)).
        -- assert (hvalueEq : value = sourceValue).
           {
             exact (raw_codedAssignmentLookup_functional M hPA
               oldCode oldStep current value sourceValue
               hvalue hsourceValue).
           }
           subst value. exact (proj2 hext).
      * intro hboundSucc. exfalso.
        apply (raw_not_lt_self M hPA bound).
        exact (raw_lt_le_trans_pair M hPA
          bound (raw_succ M current) bound hboundSucc
          (raw_succ_le_of_lt_pair M hPA
            current bound hcurrentBound)).
  - subst current.
    exists (raw_add M oldCapacity newValue).
    intros targetStep hnewCoding.
    pose proof (raw_termEvaluationCodingStep_old_of_sum M hPA
      bound oldCapacity newValue targetStep hnewCoding)
      as holdCoding.
    destruct (holdCapacity targetStep holdCoding)
      as [targetCode [htargetDefined [htargetPrefix htargetNew]]].
    assert (hvalueBound : rawLt M newValue
        (rawBetaModulus M targetStep bound)).
    {
      exact (raw_termEvaluationCodingStep_value_bound M hPA
        bound oldCapacity newValue targetStep hnewCoding).
    }
    destruct (raw_betaCodeExtension_exists M hPA
      targetCode targetStep bound newValue
      (proj1 holdCoding) hvalueBound)
      as [newTargetCode hext].
    exists newTargetCode. split.
    + exact (raw_rank_betaExtension_defined_succ M hPA
        targetCode targetStep bound newValue newTargetCode
        htargetDefined hext).
    + split.
      * intros index value hindexSucc hindexBound hvalue.
        unfold RawCodedAssignmentLookup in *.
        exact ((proj1 hext) index hindexBound value
          (htargetPrefix index value hindexBound hindexBound hvalue)).
      * intros _. exact (proj2 hext).
Qed.

Theorem raw_codedAssignmentAppendTraceCapacity_through_all : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall oldCode oldStep bound newValue,
  RawCodedAssignmentDefinedThrough M oldCode oldStep bound ->
  forall current,
  RawCodedAssignmentAppendTraceCapacityThrough M
    current (raw_succ M bound) oldCode oldStep bound newValue.
Proof.
  intros M hPA oldCode oldStep bound newValue holdDefined.
  set (limit := raw_succ M bound).
  set (parameterEnv := scons M limit
    (scons M oldCode (scons M oldStep
      (scons M bound
        (scons M newValue (fun _ : nat => raw_zero M)))))).
  set (phi := codedAssignmentAppendTraceCapacityThroughTermAt
    (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2
        (raw_sat_codedAssignmentAppendTraceCapacityThroughTermAt_iff M
          (scons M (raw_zero M) parameterEnv)
          (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5))).
      unfold parameterEnv. cbn [raw_term_eval scons]. intros _.
      exact (raw_codedAssignmentAppendTraceCapacity_zero M hPA
        oldCode oldStep bound newValue).
    - intros current hcurrentSat.
      unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_codedAssignmentAppendTraceCapacityThroughTermAt_iff M
          (scons M current parameterEnv)
          (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5))
        hcurrentSat) as hcurrentRaw.
      apply (proj2
        (raw_sat_codedAssignmentAppendTraceCapacityThroughTermAt_iff M
          (scons M (raw_succ M current) parameterEnv)
          (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5))).
      unfold parameterEnv in hcurrentRaw |- *.
      cbn [raw_term_eval scons] in hcurrentRaw |- *.
      intro hsuccLimit.
      assert (hcurrentLimit : rawLt M current limit).
      {
        exact (raw_lt_of_succ_le_traversal M hPA
          current limit hsuccLimit).
      }
      apply (raw_codedAssignmentAppendTraceCapacity_succ M hPA
        oldCode oldStep bound newValue current holdDefined).
      + unfold limit in hcurrentLimit. exact hcurrentLimit.
      + apply hcurrentRaw.
        exact (raw_lt_to_le M current limit hcurrentLimit).
  }
  intro current. unfold phi in hall.
  pose proof (proj1
    (raw_sat_codedAssignmentAppendTraceCapacityThroughTermAt_iff M
      (scons M current parameterEnv)
      (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5))
    (hall current)) as hraw.
  unfold parameterEnv in hraw.
  cbn [raw_term_eval scons] in hraw.
  unfold limit in hraw. exact hraw.
Qed.

(** Public one-table append theorem.  Both the fresh step and fresh code are
    hidden; the result preserves the old prefix at the same indices and adds
    the requested arbitrary value at the old bound. *)
Theorem raw_codedAssignmentAppend_defined_exists : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall oldCode oldStep bound newValue,
  RawCodedAssignmentDefinedThrough M oldCode oldStep bound ->
  exists newCode newStep : M,
    RawCodedAssignmentDefinedThrough M
      newCode newStep (raw_succ M bound) /\
    (forall index value,
      rawLt M index bound ->
      RawCodedAssignmentLookup M oldCode oldStep index value ->
      RawCodedAssignmentLookup M newCode newStep index value) /\
    RawCodedAssignmentLookup M newCode newStep bound newValue.
Proof.
  intros M hPA oldCode oldStep bound newValue holdDefined.
  pose proof
    (raw_codedAssignmentAppendTraceCapacity_through_all M hPA
      oldCode oldStep bound newValue holdDefined
      (raw_succ M bound)) as hthrough.
  destruct (hthrough (raw_rank_le_refl M hPA (raw_succ M bound)))
    as [capacity hcapacity].
  destruct (raw_termEvaluationCodingStep_exists M hPA
    (raw_succ M bound) capacity) as [newStep hcoding].
  destruct (hcapacity newStep hcoding)
    as [newCode [hdefined [hprefix hnew]]].
  exists newCode, newStep. split; [exact hdefined |]. split.
  - intros index value hindex hlookup.
    apply (hprefix index value).
    + exact (raw_assignment_lt_trans M hPA
        index bound (raw_succ M bound) hindex
        (raw_assignment_lt_self_succ M hPA bound)).
    + exact hindex.
    + exact hlookup.
  - exact (hnew (raw_assignment_lt_self_succ M hPA bound)).
Qed.

(** Closed arithmetic law for arbitrary-value append.  This packages the
    entire capacity construction behind the public relation and lets raw-model
    completeness produce an actual PA derivation. *)
Definition RawCodedAssignmentAppendLaw (M : RawPAModel) : Prop :=
  forall oldCode oldStep bound newValue : M,
    RawCodedAssignmentDefinedThrough M oldCode oldStep bound ->
    exists newCode newStep : M,
      RawCodedAssignmentAppendPrefix M
        (raw_succ M bound) oldCode oldStep bound newValue newCode newStep.

Arguments RawCodedAssignmentAppendLaw M : clear implicits.

Definition fixedTruthTotalityAll4 (body : formula) : formula :=
  pAll (pAll (pAll (pAll body))).

Definition codedAssignmentAppendFormula : formula :=
  fixedTruthTotalityAll4
    (pImp
      (codedAssignmentDefinedThroughTermAt
        (tVar 3) (tVar 2) (tVar 1))
      (pEx (pEx
        (codedAssignmentAppendPrefixTermAt
          (tSucc (tVar 3)) (tVar 5) (tVar 4)
          (tVar 3) (tVar 2) (tVar 1) (tVar 0))))).

Lemma raw_sat_codedAssignmentAppendFormula_iff : forall
    (M : RawPAModel) e,
  raw_formula_sat M e codedAssignmentAppendFormula <->
  RawCodedAssignmentAppendLaw M.
Proof.
  intros. unfold codedAssignmentAppendFormula,
    fixedTruthTotalityAll4, RawCodedAssignmentAppendLaw.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_codedAssignmentDefinedThroughTermAt_iff.
  setoid_rewrite raw_sat_codedAssignmentAppendPrefixTermAt_iff.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Theorem codedAssignmentAppendFormula_sentence :
  Formula.Sentence codedAssignmentAppendFormula.
Proof.
  intros k hfree.
  unfold codedAssignmentAppendFormula,
    fixedTruthTotalityAll4,
    codedAssignmentAppendPrefixTermAt in hfree.
  cbn in hfree. lia.
Qed.

Theorem codedAssignmentAppendFormula_raw_valid : forall
    (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e codedAssignmentAppendFormula.
Proof.
  intros M hPA e.
  apply (proj2 (raw_sat_codedAssignmentAppendFormula_iff M e)).
  intros oldCode oldStep bound newValue holdDefined.
  destruct (raw_codedAssignmentAppend_defined_exists M hPA
    oldCode oldStep bound newValue holdDefined)
    as [newCode [newStep [hdefined [hprefix hnew]]]].
  exists newCode, newStep. split; [exact hdefined |]. split.
  - intros index value hindexSucc hindexBound hlookup.
    exact (hprefix index value hindexBound hlookup).
  - intros _. exact hnew.
Qed.

Theorem PA_proves_codedAssignmentAppendFormula :
  Formula.BProv Formula.Ax_s [] codedAssignmentAppendFormula.
Proof.
  apply PA_BProv_of_raw_valid.
  - exact codedAssignmentAppendFormula_sentence.
  - intros M hPA e.
    exact (codedAssignmentAppendFormula_raw_valid M hPA e).
Qed.

Definition RawFixedLevelStateTablesAppendProperty
    (M : RawPAModel) : Prop :=
  forall modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep bound
    mode formula assignmentCode assignmentStep : M,
  RawCodedAssignmentDefinedThrough M modeCode modeStep bound ->
  RawCodedAssignmentDefinedThrough M formulaCode formulaStep bound ->
  RawCodedAssignmentDefinedThrough M
    assignmentCodeCode assignmentCodeStep bound ->
  RawCodedAssignmentDefinedThrough M
    assignmentStepCode assignmentStepStep bound ->
  exists newModeCode newModeStep newFormulaCode newFormulaStep
    newAssignmentCodeCode newAssignmentCodeStep
    newAssignmentStepCode newAssignmentStepStep : M,
    RawCodedAssignmentDefinedThrough M
      newModeCode newModeStep (raw_succ M bound) /\
    RawCodedAssignmentDefinedThrough M
      newFormulaCode newFormulaStep (raw_succ M bound) /\
    RawCodedAssignmentDefinedThrough M
      newAssignmentCodeCode newAssignmentCodeStep (raw_succ M bound) /\
    RawCodedAssignmentDefinedThrough M
      newAssignmentStepCode newAssignmentStepStep (raw_succ M bound) /\
    (forall index value,
      rawLt M index bound ->
      RawCodedAssignmentLookup M modeCode modeStep index value ->
      RawCodedAssignmentLookup M
        newModeCode newModeStep index value) /\
    (forall index value,
      rawLt M index bound ->
      RawCodedAssignmentLookup M formulaCode formulaStep index value ->
      RawCodedAssignmentLookup M
        newFormulaCode newFormulaStep index value) /\
    (forall index value,
      rawLt M index bound ->
      RawCodedAssignmentLookup M
        assignmentCodeCode assignmentCodeStep index value ->
      RawCodedAssignmentLookup M
        newAssignmentCodeCode newAssignmentCodeStep index value) /\
    (forall index value,
      rawLt M index bound ->
      RawCodedAssignmentLookup M
        assignmentStepCode assignmentStepStep index value ->
      RawCodedAssignmentLookup M
        newAssignmentStepCode newAssignmentStepStep index value) /\
    RawFixedLevelStateLookup M
      newModeCode newModeStep newFormulaCode newFormulaStep
      newAssignmentCodeCode newAssignmentCodeStep
      newAssignmentStepCode newAssignmentStepStep
      bound mode formula assignmentCode assignmentStep.

Arguments RawFixedLevelStateTablesAppendProperty M : clear implicits.

Theorem raw_fixedLevelStateTablesAppend : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawFixedLevelStateTablesAppendProperty M.
Proof.
  intros M hPA modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep bound
    mode formula assignmentCode assignmentStep
    hmodeDefined hformulaDefined
    hassignmentCodeDefined hassignmentStepDefined.
  destruct (raw_codedAssignmentAppend_defined_exists M hPA
    modeCode modeStep bound mode hmodeDefined)
    as [newModeCode [newModeStep
      [hnewModeDefined [hmodePrefix hmodeLookup]]]].
  destruct (raw_codedAssignmentAppend_defined_exists M hPA
    formulaCode formulaStep bound formula hformulaDefined)
    as [newFormulaCode [newFormulaStep
      [hnewFormulaDefined [hformulaPrefix hformulaLookup]]]].
  destruct (raw_codedAssignmentAppend_defined_exists M hPA
    assignmentCodeCode assignmentCodeStep bound assignmentCode
    hassignmentCodeDefined)
    as [newAssignmentCodeCode [newAssignmentCodeStep
      [hnewAssignmentCodeDefined
       [hassignmentCodePrefix hassignmentCodeLookup]]]].
  destruct (raw_codedAssignmentAppend_defined_exists M hPA
    assignmentStepCode assignmentStepStep bound assignmentStep
    hassignmentStepDefined)
    as [newAssignmentStepCode [newAssignmentStepStep
      [hnewAssignmentStepDefined
       [hassignmentStepPrefix hassignmentStepLookup]]]].
  exists newModeCode, newModeStep, newFormulaCode, newFormulaStep,
    newAssignmentCodeCode, newAssignmentCodeStep,
    newAssignmentStepCode, newAssignmentStepStep.
  repeat split; try assumption.
Qed.

(** Prefix preservation for the four synchronized state components. *)
Definition RawFixedLevelStateTablePrefixExtension (M : RawPAModel)
    (bound
      oldModeCode oldModeStep oldFormulaCode oldFormulaStep
      oldAssignmentCodeCode oldAssignmentCodeStep
      oldAssignmentStepCode oldAssignmentStepStep
      newModeCode newModeStep newFormulaCode newFormulaStep
      newAssignmentCodeCode newAssignmentCodeStep
      newAssignmentStepCode newAssignmentStepStep : M) : Prop :=
  (forall index value,
    rawLt M index bound ->
    RawCodedAssignmentLookup M
      oldModeCode oldModeStep index value ->
    RawCodedAssignmentLookup M
      newModeCode newModeStep index value) /\
  (forall index value,
    rawLt M index bound ->
    RawCodedAssignmentLookup M
      oldFormulaCode oldFormulaStep index value ->
    RawCodedAssignmentLookup M
      newFormulaCode newFormulaStep index value) /\
  (forall index value,
    rawLt M index bound ->
    RawCodedAssignmentLookup M
      oldAssignmentCodeCode oldAssignmentCodeStep index value ->
    RawCodedAssignmentLookup M
      newAssignmentCodeCode newAssignmentCodeStep index value) /\
  (forall index value,
    rawLt M index bound ->
    RawCodedAssignmentLookup M
      oldAssignmentStepCode oldAssignmentStepStep index value ->
    RawCodedAssignmentLookup M
      newAssignmentStepCode newAssignmentStepStep index value).

Arguments RawFixedLevelStateTablePrefixExtension
  M bound
    oldModeCode oldModeStep oldFormulaCode oldFormulaStep
    oldAssignmentCodeCode oldAssignmentCodeStep
    oldAssignmentStepCode oldAssignmentStepStep
    newModeCode newModeStep newFormulaCode newFormulaStep
    newAssignmentCodeCode newAssignmentCodeStep
    newAssignmentStepCode newAssignmentStepStep : clear implicits.

Lemma raw_fixedLevelStateLookup_prefix_extend : forall
    (M : RawPAModel) bound
    oldModeCode oldModeStep oldFormulaCode oldFormulaStep
    oldAssignmentCodeCode oldAssignmentCodeStep
    oldAssignmentStepCode oldAssignmentStepStep
    newModeCode newModeStep newFormulaCode newFormulaStep
    newAssignmentCodeCode newAssignmentCodeStep
    newAssignmentStepCode newAssignmentStepStep
    index mode code assignmentCode assignmentStep,
  RawFixedLevelStateTablePrefixExtension M bound
    oldModeCode oldModeStep oldFormulaCode oldFormulaStep
    oldAssignmentCodeCode oldAssignmentCodeStep
    oldAssignmentStepCode oldAssignmentStepStep
    newModeCode newModeStep newFormulaCode newFormulaStep
    newAssignmentCodeCode newAssignmentCodeStep
    newAssignmentStepCode newAssignmentStepStep ->
  rawLt M index bound ->
  RawFixedLevelStateLookup M
    oldModeCode oldModeStep oldFormulaCode oldFormulaStep
    oldAssignmentCodeCode oldAssignmentCodeStep
    oldAssignmentStepCode oldAssignmentStepStep
    index mode code assignmentCode assignmentStep ->
  RawFixedLevelStateLookup M
    newModeCode newModeStep newFormulaCode newFormulaStep
    newAssignmentCodeCode newAssignmentCodeStep
    newAssignmentStepCode newAssignmentStepStep
    index mode code assignmentCode assignmentStep.
Proof.
  intros M bound
    oldModeCode oldModeStep oldFormulaCode oldFormulaStep
    oldAssignmentCodeCode oldAssignmentCodeStep
    oldAssignmentStepCode oldAssignmentStepStep
    newModeCode newModeStep newFormulaCode newFormulaStep
    newAssignmentCodeCode newAssignmentCodeStep
    newAssignmentStepCode newAssignmentStepStep
    index mode code assignmentCode assignmentStep
    [hmode [hformula [hassignmentCode hassignmentStep]]]
    hindex [hm [hf [hac has]]].
  repeat split.
  - exact (hmode index mode hindex hm).
  - exact (hformula index code hindex hf).
  - exact (hassignmentCode index assignmentCode hindex hac).
  - exact (hassignmentStep index assignmentStep hindex has).
Qed.

Lemma raw_fixedLevelStateLookup_prefix_reflect : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall bound
    oldModeCode oldModeStep oldFormulaCode oldFormulaStep
    oldAssignmentCodeCode oldAssignmentCodeStep
    oldAssignmentStepCode oldAssignmentStepStep
    newModeCode newModeStep newFormulaCode newFormulaStep
    newAssignmentCodeCode newAssignmentCodeStep
    newAssignmentStepCode newAssignmentStepStep
    index mode code assignmentCode assignmentStep,
  RawCodedAssignmentDefinedThrough M
    oldModeCode oldModeStep bound ->
  RawCodedAssignmentDefinedThrough M
    oldFormulaCode oldFormulaStep bound ->
  RawCodedAssignmentDefinedThrough M
    oldAssignmentCodeCode oldAssignmentCodeStep bound ->
  RawCodedAssignmentDefinedThrough M
    oldAssignmentStepCode oldAssignmentStepStep bound ->
  RawFixedLevelStateTablePrefixExtension M bound
    oldModeCode oldModeStep oldFormulaCode oldFormulaStep
    oldAssignmentCodeCode oldAssignmentCodeStep
    oldAssignmentStepCode oldAssignmentStepStep
    newModeCode newModeStep newFormulaCode newFormulaStep
    newAssignmentCodeCode newAssignmentCodeStep
    newAssignmentStepCode newAssignmentStepStep ->
  rawLt M index bound ->
  RawFixedLevelStateLookup M
    newModeCode newModeStep newFormulaCode newFormulaStep
    newAssignmentCodeCode newAssignmentCodeStep
    newAssignmentStepCode newAssignmentStepStep
    index mode code assignmentCode assignmentStep ->
  RawFixedLevelStateLookup M
    oldModeCode oldModeStep oldFormulaCode oldFormulaStep
    oldAssignmentCodeCode oldAssignmentCodeStep
    oldAssignmentStepCode oldAssignmentStepStep
    index mode code assignmentCode assignmentStep.
Proof.
  intros M hPA bound
    oldModeCode oldModeStep oldFormulaCode oldFormulaStep
    oldAssignmentCodeCode oldAssignmentCodeStep
    oldAssignmentStepCode oldAssignmentStepStep
    newModeCode newModeStep newFormulaCode newFormulaStep
    newAssignmentCodeCode newAssignmentCodeStep
    newAssignmentStepCode newAssignmentStepStep
    index mode code assignmentCode assignmentStep
    hmodeDefined hformulaDefined
    hassignmentCodeDefined hassignmentStepDefined
    [hmode [hformula [hassignmentCode hassignmentStep]]]
    hindex [hnewMode [hnewFormula
      [hnewAssignmentCode hnewAssignmentStep]]].
  destruct (hmodeDefined index hindex) as [oldMode holdMode].
  destruct (hformulaDefined index hindex) as [oldFormula holdFormula].
  destruct (hassignmentCodeDefined index hindex)
    as [oldAssignmentCode holdAssignmentCode].
  destruct (hassignmentStepDefined index hindex)
    as [oldAssignmentStep holdAssignmentStep].
  assert (hmodeEq : mode = oldMode).
  {
    exact (raw_codedAssignmentLookup_functional M hPA
      newModeCode newModeStep index mode oldMode
      hnewMode (hmode index oldMode hindex holdMode)).
  }
  assert (hformulaEq : code = oldFormula).
  {
    exact (raw_codedAssignmentLookup_functional M hPA
      newFormulaCode newFormulaStep index code oldFormula
      hnewFormula (hformula index oldFormula hindex holdFormula)).
  }
  assert (hassignmentCodeEq : assignmentCode = oldAssignmentCode).
  {
    exact (raw_codedAssignmentLookup_functional M hPA
      newAssignmentCodeCode newAssignmentCodeStep index
      assignmentCode oldAssignmentCode hnewAssignmentCode
      (hassignmentCode index oldAssignmentCode
        hindex holdAssignmentCode)).
  }
  assert (hassignmentStepEq : assignmentStep = oldAssignmentStep).
  {
    exact (raw_codedAssignmentLookup_functional M hPA
      newAssignmentStepCode newAssignmentStepStep index
      assignmentStep oldAssignmentStep hnewAssignmentStep
      (hassignmentStep index oldAssignmentStep
        hindex holdAssignmentStep)).
  }
  subst oldMode. subst oldFormula.
  subst oldAssignmentCode. subst oldAssignmentStep.
  repeat split; assumption.
Qed.

(** Every table-dependent premise of a closed successor row is an earlier
    state lookup.  Hence a prefix extension transports the row whenever its
    current index is still at most the old bound.  Lower-level recursive
    certificates and binder-prepend witnesses are table-independent. *)
Lemma raw_fixedLevelClosedSuccessorRow_prefix_extend : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall lower lowerSigmaEvidence lowerPiEvidence
    bound current
    oldModeCode oldModeStep oldFormulaCode oldFormulaStep
    oldAssignmentCodeCode oldAssignmentCodeStep
    oldAssignmentStepCode oldAssignmentStepStep
    newModeCode newModeStep newFormulaCode newFormulaStep
    newAssignmentCodeCode newAssignmentCodeStep
    newAssignmentStepCode newAssignmentStepStep
    mode code assignmentCode assignmentStep,
  RawFixedLevelStateTablePrefixExtension M bound
    oldModeCode oldModeStep oldFormulaCode oldFormulaStep
    oldAssignmentCodeCode oldAssignmentCodeStep
    oldAssignmentStepCode oldAssignmentStepStep
    newModeCode newModeStep newFormulaCode newFormulaStep
    newAssignmentCodeCode newAssignmentCodeStep
    newAssignmentStepCode newAssignmentStepStep ->
  rawLe M current bound ->
  RawFixedLevelClosedSuccessorRow M lower
    lowerSigmaEvidence lowerPiEvidence
    oldModeCode oldModeStep oldFormulaCode oldFormulaStep
    oldAssignmentCodeCode oldAssignmentCodeStep
    oldAssignmentStepCode oldAssignmentStepStep
    current mode code assignmentCode assignmentStep ->
  RawFixedLevelClosedSuccessorRow M lower
    lowerSigmaEvidence lowerPiEvidence
    newModeCode newModeStep newFormulaCode newFormulaStep
    newAssignmentCodeCode newAssignmentCodeStep
    newAssignmentStepCode newAssignmentStepStep
    current mode code assignmentCode assignmentStep.
Proof.
  intros M hPA lower lowerSigmaEvidence lowerPiEvidence
    bound current
    oldModeCode oldModeStep oldFormulaCode oldFormulaStep
    oldAssignmentCodeCode oldAssignmentCodeStep
    oldAssignmentStepCode oldAssignmentStepStep
    newModeCode newModeStep newFormulaCode newFormulaStep
    newAssignmentCodeCode newAssignmentCodeStep
    newAssignmentStepCode newAssignmentStepStep
    mode code assignmentCode assignmentStep
    hext hcurrent hclosed.
  assert (hearlier : forall childIndex expectedMode childCode
      childAssignmentCode childAssignmentStep,
    RawFixedLevelEarlierState M
      oldModeCode oldModeStep oldFormulaCode oldFormulaStep
      oldAssignmentCodeCode oldAssignmentCodeStep
      oldAssignmentStepCode oldAssignmentStepStep
      current childIndex expectedMode childCode
      childAssignmentCode childAssignmentStep ->
    RawFixedLevelEarlierState M
      newModeCode newModeStep newFormulaCode newFormulaStep
      newAssignmentCodeCode newAssignmentCodeStep
      newAssignmentStepCode newAssignmentStepStep
      current childIndex expectedMode childCode
      childAssignmentCode childAssignmentStep).
  {
    intros childIndex expectedMode childCode
      childAssignmentCode childAssignmentStep [hchild hlookup].
    split; [exact hchild |].
    apply (raw_fixedLevelStateLookup_prefix_extend M bound
      oldModeCode oldModeStep oldFormulaCode oldFormulaStep
      oldAssignmentCodeCode oldAssignmentCodeStep
      oldAssignmentStepCode oldAssignmentStepStep
      newModeCode newModeStep newFormulaCode newFormulaStep
      newAssignmentCodeCode newAssignmentCodeStep
      newAssignmentStepCode newAssignmentStepStep
      childIndex expectedMode childCode
      childAssignmentCode childAssignmentStep hext).
    - exact (raw_lt_le_trans_pair M hPA
        childIndex current bound hchild hcurrent).
    - exact hlookup.
  }
  destruct hclosed as [[hmode hsigma] | [hmode hpi]].
  - left. split; [exact hmode |].
    destruct hsigma as
      (leftIndex & leftCode & rightIndex & rightCode & witness &
       newAssignmentCode & newAssignmentStep & spare & hsigma).
    exists leftIndex, leftCode, rightIndex, rightCode, witness,
      newAssignmentCode, newAssignmentStep, spare.
    unfold RawFixedLevelSigmaSuccessorWitnessRow in hsigma |- *.
    destruct hsigma as [hdomain hcases]. split; [exact hdomain |].
    destruct hcases as
      [hzero | [himpLeft | [himpRight | [hand | [hor | [hex | hall]]]]]].
    + left. exact hzero.
    + right. left.
      destruct himpLeft as [hcode [hleft hspare]].
      split; [exact hcode |]. split; [exact (hearlier _ _ _ _ _ hleft) |].
      exact hspare.
    + right. right. left.
      destruct himpRight as [hcode [hright hspare]].
      split; [exact hcode |]. split; [exact (hearlier _ _ _ _ _ hright) |].
      exact hspare.
    + right. right. right. left.
      destruct hand as [hcode [hleft hright]].
      split; [exact hcode |]. split.
      * exact (hearlier _ _ _ _ _ hleft).
      * exact (hearlier _ _ _ _ _ hright).
    + right. right. right. right. left.
      destruct hor as [hcode [hleft | hright]].
      * split; [exact hcode |]. left.
        exact (hearlier _ _ _ _ _ hleft).
      * split; [exact hcode |]. right.
        exact (hearlier _ _ _ _ _ hright).
    + right. right. right. right. right. left.
      destruct hex as [hcode [hprepend hleft]].
      split; [exact hcode |]. split; [exact hprepend |].
      exact (hearlier _ _ _ _ _ hleft).
    + right. right. right. right. right. right. exact hall.
  - right. split; [exact hmode |].
    destruct hpi as
      (leftIndex & leftCode & rightIndex & rightCode & witness &
       newAssignmentCode & newAssignmentStep & spare & hpi).
    exists leftIndex, leftCode, rightIndex, rightCode, witness,
      newAssignmentCode, newAssignmentStep, spare.
    unfold RawFixedLevelPiSuccessorWitnessRow in hpi |- *.
    destruct hpi as [hdomain hcases]. split; [exact hdomain |].
    destruct hcases as
      [hzero | [himp | [hand | [hor | [hall | hex]]]]].
    + left. exact hzero.
    + right. left.
      destruct himp as [hcode [hleft [hright hspare]]].
      split; [exact hcode |]. split.
      * exact (hearlier _ _ _ _ _ hleft).
      * split; [exact (hearlier _ _ _ _ _ hright) | exact hspare].
    + right. right. left.
      destruct hand as [hcode [hleft | hright]].
      * split; [exact hcode |]. left.
        exact (hearlier _ _ _ _ _ hleft).
      * split; [exact hcode |]. right.
        exact (hearlier _ _ _ _ _ hright).
    + right. right. right. left.
      destruct hor as [hcode [hleft hright]].
      split; [exact hcode |]. split.
      * exact (hearlier _ _ _ _ _ hleft).
      * exact (hearlier _ _ _ _ _ hright).
    + right. right. right. right. left.
      destruct hall as [hcode [hprepend hleft]].
      split; [exact hcode |]. split; [exact hprepend |].
      exact (hearlier _ _ _ _ _ hleft).
    + right. right. right. right. right. exact hex.
Qed.

(** One accumulator step for a positive-level schedule.  The premise is a
    globally closed old prefix plus a new closed row whose child references
    point into that prefix.  The conclusion is a complete traversal rooted at
    the appended row.  Thus arbitrary-value CRT capacity is no longer a seam
    in the schedule construction. *)
Theorem raw_fixedLevelClosedSuccessorRow_append_traversal : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall lower lowerSigmaEvidence lowerPiEvidence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode code assignmentCode assignmentStep,
  RawCodedAssignmentDefinedThrough M modeCode modeStep bound ->
  RawCodedAssignmentDefinedThrough M formulaCode formulaStep bound ->
  RawCodedAssignmentDefinedThrough M
    assignmentCodeCode assignmentCodeStep bound ->
  RawCodedAssignmentDefinedThrough M
    assignmentStepCode assignmentStepStep bound ->
  RawFixedLevelSuccessorTruthTraversalRows M lower
    lowerSigmaEvidence lowerPiEvidence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep bound ->
  RawFixedLevelClosedSuccessorRow M lower
    lowerSigmaEvidence lowerPiEvidence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode code assignmentCode assignmentStep ->
  exists newModeCode newModeStep newFormulaCode newFormulaStep
    newAssignmentCodeCode newAssignmentCodeStep
    newAssignmentStepCode newAssignmentStepStep : M,
  RawFixedLevelSuccessorTruthTraversal M lower
    lowerSigmaEvidence lowerPiEvidence
    newModeCode newModeStep newFormulaCode newFormulaStep
    newAssignmentCodeCode newAssignmentCodeStep
    newAssignmentStepCode newAssignmentStepStep
    (raw_succ M bound) bound mode code assignmentCode assignmentStep.
Proof.
  intros M hPA lower lowerSigmaEvidence lowerPiEvidence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode code assignmentCode assignmentStep
    hmodeDefined hformulaDefined
    hassignmentCodeDefined hassignmentStepDefined
    hrows hclosed.
  destruct (raw_fixedLevelStateTablesAppend M hPA
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep bound
    mode code assignmentCode assignmentStep
    hmodeDefined hformulaDefined
    hassignmentCodeDefined hassignmentStepDefined)
    as (newModeCode & newModeStep & newFormulaCode & newFormulaStep &
        newAssignmentCodeCode & newAssignmentCodeStep &
        newAssignmentStepCode & newAssignmentStepStep &
        hnewModeDefined & hnewFormulaDefined &
        hnewAssignmentCodeDefined & hnewAssignmentStepDefined &
        hmodePrefix & hformulaPrefix &
        hassignmentCodePrefix & hassignmentStepPrefix & hrootLookup).
  assert (hext : RawFixedLevelStateTablePrefixExtension M bound
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      newModeCode newModeStep newFormulaCode newFormulaStep
      newAssignmentCodeCode newAssignmentCodeStep
      newAssignmentStepCode newAssignmentStepStep).
  {
    repeat split; assumption.
  }
  exists newModeCode, newModeStep, newFormulaCode, newFormulaStep,
    newAssignmentCodeCode, newAssignmentCodeStep,
    newAssignmentStepCode, newAssignmentStepStep.
  split; [exact hnewModeDefined |].
  split; [exact hnewFormulaDefined |].
  split; [exact hnewAssignmentCodeDefined |].
  split; [exact hnewAssignmentStepDefined |].
  split; [exact (raw_assignment_lt_self_succ M hPA bound) |].
  split; [exact hrootLookup |].
  intros index rowMode rowCode rowAssignmentCode rowAssignmentStep
    hindex hrowLookup.
  destruct (raw_lt_succ_cases M hPA index bound hindex)
    as [hindexBound | ->].
  - pose proof (raw_fixedLevelStateLookup_prefix_reflect M hPA bound
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      newModeCode newModeStep newFormulaCode newFormulaStep
      newAssignmentCodeCode newAssignmentCodeStep
      newAssignmentStepCode newAssignmentStepStep
      index rowMode rowCode rowAssignmentCode rowAssignmentStep
      hmodeDefined hformulaDefined
      hassignmentCodeDefined hassignmentStepDefined
      hext hindexBound hrowLookup) as holdLookup.
    pose proof (hrows index rowMode rowCode
      rowAssignmentCode rowAssignmentStep hindexBound holdLookup)
      as holdClosed.
    exact (raw_fixedLevelClosedSuccessorRow_prefix_extend M hPA
      lower lowerSigmaEvidence lowerPiEvidence bound index
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      newModeCode newModeStep newFormulaCode newFormulaStep
      newAssignmentCodeCode newAssignmentCodeStep
      newAssignmentStepCode newAssignmentStepStep
      rowMode rowCode rowAssignmentCode rowAssignmentStep
      hext (raw_lt_to_le M index bound hindexBound) holdClosed).
  - destruct (raw_fixedLevelStateLookup_functional M hPA
      newModeCode newModeStep newFormulaCode newFormulaStep
      newAssignmentCodeCode newAssignmentCodeStep
      newAssignmentStepCode newAssignmentStepStep
      bound mode code assignmentCode assignmentStep
      rowMode rowCode rowAssignmentCode rowAssignmentStep
      hrootLookup hrowLookup)
      as [hmode [hcode [hassignmentCode hassignmentStep]]].
    subst rowMode. subst rowCode.
    subst rowAssignmentCode. subst rowAssignmentStep.
    exact (raw_fixedLevelClosedSuccessorRow_prefix_extend M hPA
      lower lowerSigmaEvidence lowerPiEvidence bound bound
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      newModeCode newModeStep newFormulaCode newFormulaStep
      newAssignmentCodeCode newAssignmentCodeStep
      newAssignmentStepCode newAssignmentStepStep
      mode code assignmentCode assignmentStep
      hext (raw_rank_le_refl M hPA bound) hclosed).
Qed.

(** ------------------------------------------------------------------
    The independent adjacent-level coherence boundary.

    Arbitrary-value append is now proved above, but it is not the only issue
    in a positive-level truth induction.  A Sigma-All row says that there is
    no lower-level Pi-falsity certificate, while a Pi-Ex row dually excludes a
    lower-level Sigma-truth certificate.  When a Boolean or preferred-binder
    child is decided at the current level, those negative clauses require the
    certificate predicates to agree on the lower domain at adjacent levels.

    The following formula states exactly that simultaneous coherence
    at one external level.  We prove its raw semantics, but deliberately do
    not postulate or claim its PA proof in this checkpoint. *)

Definition RawFixedLevelTruthCertificateCoherenceAt
    (M : RawPAModel) (lower : nat) : Prop :=
  (forall root assignmentCode assignmentStep : M,
    RawFixedLevelSigmaDomain M lower root ->
    (RawFixedLevelSigmaTruthCertificate M lower
        root assignmentCode assignmentStep <->
     RawFixedLevelSigmaTruthCertificate M (S lower)
        root assignmentCode assignmentStep)) /\
  (forall root assignmentCode assignmentStep : M,
    RawFixedLevelPiDomain M lower root ->
    (RawFixedLevelPiFalsityCertificate M lower
        root assignmentCode assignmentStep <->
     RawFixedLevelPiFalsityCertificate M (S lower)
        root assignmentCode assignmentStep)).

Arguments RawFixedLevelTruthCertificateCoherenceAt M lower
  : clear implicits.

Definition fixedLevelTruthCertificateCoherenceFormula
    (lower : nat) : formula :=
  pAll (pAll (pAll
    (pAnd
      (pImp
        (fixedLevelSigmaDomainTermAt lower (tVar 2))
        (pAnd
          (pImp
            (fixedLevelSigmaTruthCertificateTermAt lower
              (tVar 2) (tVar 1) (tVar 0))
            (fixedLevelSigmaTruthCertificateTermAt (S lower)
              (tVar 2) (tVar 1) (tVar 0)))
          (pImp
            (fixedLevelSigmaTruthCertificateTermAt (S lower)
              (tVar 2) (tVar 1) (tVar 0))
            (fixedLevelSigmaTruthCertificateTermAt lower
              (tVar 2) (tVar 1) (tVar 0)))))
      (pImp
        (fixedLevelPiDomainTermAt lower (tVar 2))
        (pAnd
          (pImp
            (fixedLevelPiFalsityCertificateTermAt lower
              (tVar 2) (tVar 1) (tVar 0))
            (fixedLevelPiFalsityCertificateTermAt (S lower)
              (tVar 2) (tVar 1) (tVar 0)))
          (pImp
            (fixedLevelPiFalsityCertificateTermAt (S lower)
              (tVar 2) (tVar 1) (tVar 0))
            (fixedLevelPiFalsityCertificateTermAt lower
              (tVar 2) (tVar 1) (tVar 0)))))))).

Lemma raw_sat_fixedLevelTruthCertificateCoherenceFormula_iff : forall
    (M : RawPAModel) e lower,
  raw_formula_sat M e
    (fixedLevelTruthCertificateCoherenceFormula lower) <->
  RawFixedLevelTruthCertificateCoherenceAt M lower.
Proof.
  intros. unfold fixedLevelTruthCertificateCoherenceFormula,
    RawFixedLevelTruthCertificateCoherenceAt.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_fixedLevelSigmaDomainTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelPiDomainTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelSigmaTruthCertificateTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelPiFalsityCertificateTermAt_iff.
  cbn [raw_term_eval scons]. split.
  - intros hall. split.
    + intros root assignmentCode assignmentStep hdomain.
      specialize (hall root assignmentCode assignmentStep).
      destruct hall as [hsigma _].
      specialize (hsigma hdomain).
      tauto.
    + intros root assignmentCode assignmentStep hdomain.
      specialize (hall root assignmentCode assignmentStep).
      destruct hall as [_ hpi].
      specialize (hpi hdomain).
      tauto.
  - intros [hsigma hpi] root assignmentCode assignmentStep. split.
    + intros hdomain.
      specialize (hsigma root assignmentCode assignmentStep hdomain).
      tauto.
    + intros hdomain.
      specialize (hpi root assignmentCode assignmentStep hdomain).
      tauto.
Qed.

Definition RawFixedLevelTruthCertificateCoherence
    (M : RawPAModel) : Prop :=
  forall lower, RawFixedLevelTruthCertificateCoherenceAt M lower.

Arguments RawFixedLevelTruthCertificateCoherence M : clear implicits.

(** The bounded-proof application starts with the union domain at [n] and
    runs truth at [S n].  Making that shift explicit avoids the false claim
    that an arbitrary union-domain formula is decidable at level zero. *)
Definition RawFixedLevelShiftedTruthAdmissible (M : RawPAModel)
    (level : nat) (root assignmentCode assignmentStep : M) : Prop :=
  match level with
  | 0 => False
  | S inputLevel =>
      RawFixedLevelTruthAdmissible M inputLevel
        root assignmentCode assignmentStep
  end.

Definition RawFixedLevelInputTruthCertificateTotalityFor
    (M : RawPAModel) : Prop :=
  forall inputLevel root assignmentCode assignmentStep,
    RawFixedLevelTruthAdmissible M inputLevel
      root assignmentCode assignmentStep ->
    RawFixedLevelSigmaTruthCertificate M (S inputLevel)
        root assignmentCode assignmentStep \/
    RawFixedLevelPiFalsityCertificate M (S inputLevel)
        root assignmentCode assignmentStep.

Arguments RawFixedLevelShiftedTruthAdmissible
  M level root assignmentCode assignmentStep : clear implicits.
Arguments RawFixedLevelInputTruthCertificateTotalityFor M
  : clear implicits.

(** The endpoint reduction is exact and contains no hidden zero-level
    premise.  Its remaining argument is the positive schedule construction;
    closing it requires row transport/concatenation, hereditary atomic
    adequacy under child restriction and binder prepend, and the simultaneous
    coherence formula above. *)
Theorem raw_fixedLevelInputTruthCertificate_totality_from_schedule :
  forall (M : RawPAModel),
  RawFixedLevelPositiveTruthScheduleRealizationFor M
    (RawFixedLevelShiftedTruthAdmissible M) ->
  RawFixedLevelInputTruthCertificateTotalityFor M.
Proof.
  intros M hschedule inputLevel root assignmentCode assignmentStep
    hadmissible.
  exact (hschedule inputLevel root assignmentCode assignmentStep
    hadmissible).
Qed.

End PABoundedRawCodedFixedLevelTruthTotality.
