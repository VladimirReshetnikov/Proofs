(**
  The Sigma/Pi rank gap for arbitrary model-internal formula traversals.

  The public rank graph is witnessed by synchronized Goedel-beta tables.
  Those tables, their bound, and their rows may all be nonstandard.  Thus the
  familiar meta-theoretic induction on a decoded formula is not available
  here.  Instead we express the assertion that every row below a carrier
  element has ranks differing by at most one, and apply PA's own definable
  induction axiom to that formula.

  Besides the semantic theorem, this file exposes genuine PA formulae for
  the rank-gap law and for the resulting fixed-level lift.  Raw-model
  completeness then turns their validity into actual PA derivations.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness RawCodedAssignment RawCodedFormulaRankStep
  RawCodedFormulaRankTraversal RawCodedFormulaRankRealization
  RawCodedFormulaRankTotality
  RawCodedFixedLevelTruth RawCodedContextBounds.

Import ListNotations.

Module PABoundedRawCodedFormulaRankGap.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFormulaRankStep.
Import PABoundedRawCodedFormulaRankTraversal.
Import PABoundedRawCodedFormulaRankRealization.
Import PABoundedRawCodedFormulaRankTotality.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedContextBounds.

(** ------------------------------------------------------------------
    The arithmetic rank-gap predicate. *)

Definition formulaRankGapTermAt (sigma pi : term) : formula :=
  pAnd
    (Formula.leTermAt sigma (tSucc pi))
    (Formula.leTermAt pi (tSucc sigma)).

Definition RawFormulaRankGap (M : RawPAModel) (sigma pi : M) : Prop :=
  rawLe M sigma (raw_succ M pi) /\
  rawLe M pi (raw_succ M sigma).

Arguments RawFormulaRankGap M sigma pi : clear implicits.

Lemma raw_sat_formulaRankGapTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M) sigma pi,
  raw_formula_sat M e (formulaRankGapTermAt sigma pi) <->
  RawFormulaRankGap M
    (raw_term_eval M e sigma) (raw_term_eval M e pi).
Proof.
  intros M e sigma pi.
  unfold formulaRankGapTermAt, RawFormulaRankGap.
  cbn [raw_formula_sat raw_term_eval].
  rewrite !raw_sat_leTermAt_iff_rank. reflexivity.
Qed.

(** Elementary order facts used by the local constructor calculation. *)
Lemma raw_rankGap_le_succ : forall (M : RawPAModel),
  RawPASatisfies M -> forall x : M,
  rawLe M x (raw_succ M x).
Proof.
  intros M hPA x.
  apply raw_lt_to_le.
  exact (raw_assignment_lt_self_succ M hPA x).
Qed.

Lemma raw_rankGap_max_upper : forall (M : RawPAModel),
  RawPASatisfies M -> forall out left right : M,
  RawMax M out left right ->
  rawLe M left out /\ rawLe M right out.
Proof.
  intros M hPA out left right hmax.
  destruct hmax as [[hle hout] | [hle hout]]; subst out.
  - split; [exact hle | exact (raw_rank_le_refl M hPA right)].
  - split; [exact (raw_rank_le_refl M hPA left) | exact hle].
Qed.

Lemma raw_rankGap_max_least : forall (M : RawPAModel),
  forall out left right upper : M,
  RawMax M out left right ->
  rawLe M left upper -> rawLe M right upper ->
  rawLe M out upper.
Proof.
  intros M out left right upper hmax hleft hright.
  destruct hmax as [[_ hout] | [_ hout]]; subst out;
    assumption.
Qed.

Lemma raw_formulaRankZero_gap : forall (M : RawPAModel),
  RawPASatisfies M -> forall sigma pi,
  RawFormulaRankZero M sigma pi ->
  RawFormulaRankGap M sigma pi.
Proof.
  intros M hPA sigma pi [-> ->]. split;
    apply raw_rank_zero_le; exact hPA.
Qed.

Lemma raw_formulaRankImp_gap : forall (M : RawPAModel),
  RawPASatisfies M -> forall sigma pi leftSigma leftPi rightSigma rightPi,
  RawFormulaRankGap M leftSigma leftPi ->
  RawFormulaRankGap M rightSigma rightPi ->
  RawFormulaRankImp M sigma pi
    leftSigma leftPi rightSigma rightPi ->
  RawFormulaRankGap M sigma pi.
Proof.
  intros M hPA sigma pi leftSigma leftPi rightSigma rightPi
    [hlslp hlpls] [hrsrp hrprs] [hsigma hpi].
  destruct (raw_rankGap_max_upper M hPA
    pi leftSigma rightPi hpi) as [hlsPi hrpPi].
  destruct (raw_rankGap_max_upper M hPA
    sigma leftPi rightSigma hsigma) as [hlpSigma hrsSigma].
  split.
  - apply (raw_rankGap_max_least M sigma leftPi rightSigma
      (raw_succ M pi) hsigma).
    + exact (raw_le_trans M hPA leftPi (raw_succ M leftSigma)
        (raw_succ M pi) hlpls
        (raw_rank_succ_le M hPA leftSigma pi hlsPi)).
    + exact (raw_le_trans M hPA rightSigma (raw_succ M rightPi)
        (raw_succ M pi) hrsrp
        (raw_rank_succ_le M hPA rightPi pi hrpPi)).
  - apply (raw_rankGap_max_least M pi leftSigma rightPi
      (raw_succ M sigma) hpi).
    + exact (raw_le_trans M hPA leftSigma (raw_succ M leftPi)
        (raw_succ M sigma) hlslp
        (raw_rank_succ_le M hPA leftPi sigma hlpSigma)).
    + exact (raw_le_trans M hPA rightPi (raw_succ M rightSigma)
        (raw_succ M sigma) hrprs
        (raw_rank_succ_le M hPA rightSigma sigma hrsSigma)).
Qed.

Lemma raw_formulaRankAndOr_gap : forall (M : RawPAModel),
  RawPASatisfies M -> forall sigma pi leftSigma leftPi rightSigma rightPi,
  RawFormulaRankGap M leftSigma leftPi ->
  RawFormulaRankGap M rightSigma rightPi ->
  RawFormulaRankAndOr M sigma pi
    leftSigma leftPi rightSigma rightPi ->
  RawFormulaRankGap M sigma pi.
Proof.
  intros M hPA sigma pi leftSigma leftPi rightSigma rightPi
    [hlslp hlpls] [hrsrp hrprs] [hsigma hpi].
  destruct (raw_rankGap_max_upper M hPA
    pi leftPi rightPi hpi) as [hlpPi hrpPi].
  destruct (raw_rankGap_max_upper M hPA
    sigma leftSigma rightSigma hsigma) as [hlsSigma hrsSigma].
  split.
  - apply (raw_rankGap_max_least M sigma leftSigma rightSigma
      (raw_succ M pi) hsigma).
    + exact (raw_le_trans M hPA leftSigma (raw_succ M leftPi)
        (raw_succ M pi) hlslp
        (raw_rank_succ_le M hPA leftPi pi hlpPi)).
    + exact (raw_le_trans M hPA rightSigma (raw_succ M rightPi)
        (raw_succ M pi) hrsrp
        (raw_rank_succ_le M hPA rightPi pi hrpPi)).
  - apply (raw_rankGap_max_least M pi leftPi rightPi
      (raw_succ M sigma) hpi).
    + exact (raw_le_trans M hPA leftPi (raw_succ M leftSigma)
        (raw_succ M sigma) hlpls
        (raw_rank_succ_le M hPA leftSigma sigma hlsSigma)).
    + exact (raw_le_trans M hPA rightPi (raw_succ M rightSigma)
        (raw_succ M sigma) hrprs
        (raw_rank_succ_le M hPA rightSigma sigma hrsSigma)).
Qed.

Lemma raw_formulaRankAll_gap : forall (M : RawPAModel),
  RawPASatisfies M -> forall sigma pi childSigma childPi,
  RawFormulaRankAll M sigma pi childSigma childPi ->
  RawFormulaRankGap M sigma pi.
Proof.
  intros M hPA sigma pi childSigma childPi
    (base & _ & hpi & hsigma).
  subst pi. subst sigma. split.
  - exact (raw_rank_le_refl M hPA (raw_succ M base)).
  - exact (raw_le_trans M hPA base (raw_succ M base)
      (raw_succ M (raw_succ M base))
      (raw_rankGap_le_succ M hPA base)
      (raw_rankGap_le_succ M hPA (raw_succ M base))).
Qed.

Lemma raw_formulaRankEx_gap : forall (M : RawPAModel),
  RawPASatisfies M -> forall sigma pi childSigma childPi,
  RawFormulaRankEx M sigma pi childSigma childPi ->
  RawFormulaRankGap M sigma pi.
Proof.
  intros M hPA sigma pi childSigma childPi
    (base & _ & hsigma & hpi).
  subst sigma. subst pi. split.
  - exact (raw_le_trans M hPA base (raw_succ M base)
      (raw_succ M (raw_succ M base))
      (raw_rankGap_le_succ M hPA base)
      (raw_rankGap_le_succ M hPA (raw_succ M base))).
  - exact (raw_rank_le_refl M hPA (raw_succ M base)).
Qed.

(** One row inherits the gap from its strictly earlier children.  Notice
    that quantified rows need no child hypothesis: their two output ranks
    are definitionally a predecessor/successor pair around the same base. *)
Theorem raw_codedFormulaRankTraversalRow_gap : forall
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
    RawFormulaRankGap M childSigma childPi) ->
  RawFormulaRankGap M sigma pi.
Proof.
  intros M hPA formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    index code sigma pi hrow hchildren.
  destruct hrow as
    [heq | [hbot | [himp | [hand | [hor | [hall | hex]]]]]].
  - destruct heq as (left & right & _ & hzero).
    exact (raw_formulaRankZero_gap M hPA sigma pi hzero).
  - destruct hbot as [_ hzero].
    exact (raw_formulaRankZero_gap M hPA sigma pi hzero).
  - destruct himp as
      (li & left & ls & lp & ri & right & rs & rp &
       hli & hleft & hri & hright & _ & hrank).
    apply (raw_formulaRankImp_gap M hPA sigma pi ls lp rs rp).
    + exact (hchildren li left ls lp hli hleft).
    + exact (hchildren ri right rs rp hri hright).
    + exact hrank.
  - destruct hand as
      (li & left & ls & lp & ri & right & rs & rp &
       hli & hleft & hri & hright & _ & hrank).
    apply (raw_formulaRankAndOr_gap M hPA sigma pi ls lp rs rp).
    + exact (hchildren li left ls lp hli hleft).
    + exact (hchildren ri right rs rp hri hright).
    + exact hrank.
  - destruct hor as
      (li & left & ls & lp & ri & right & rs & rp &
       hli & hleft & hri & hright & _ & hrank).
    apply (raw_formulaRankAndOr_gap M hPA sigma pi ls lp rs rp).
    + exact (hchildren li left ls lp hli hleft).
    + exact (hchildren ri right rs rp hri hright).
    + exact hrank.
  - destruct hall as
      (ci & child & cs & cp & _ & _ & _ & hrank).
    exact (raw_formulaRankAll_gap M hPA sigma pi cs cp hrank).
  - destruct hex as
      (ci & child & cs & cp & _ & _ & _ & hrank).
    exact (raw_formulaRankEx_gap M hPA sigma pi cs cp hrank).
Qed.

(** ------------------------------------------------------------------
    A definable invariant over a possibly nonstandard row prefix. *)

Definition codedFormulaRankGapBelowTermAt
    (formulaCode formulaStep sigmaCode sigmaStep piCode piStep current : term)
    : formula :=
  pAll (pAll (pAll (pAll
    (pImp
      (Formula.ltTermAt (tVar 3) (liftTerm 4 current))
      (pImp
        (codedFormulaRankTripleLookupTermAt
          (liftTerm 4 formulaCode) (liftTerm 4 formulaStep)
          (liftTerm 4 sigmaCode) (liftTerm 4 sigmaStep)
          (liftTerm 4 piCode) (liftTerm 4 piStep)
          (tVar 3) (tVar 2) (tVar 1) (tVar 0))
        (formulaRankGapTermAt (tVar 1) (tVar 0))))))).

Definition RawCodedFormulaRankGapBelow (M : RawPAModel)
    (formulaCode formulaStep sigmaCode sigmaStep piCode piStep current : M)
    : Prop :=
  forall index code sigma pi : M,
    rawLt M index current ->
    RawCodedFormulaRankTripleLookup M
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      index code sigma pi ->
    RawFormulaRankGap M sigma pi.

Arguments RawCodedFormulaRankGapBelow
  M formulaCode formulaStep sigmaCode sigmaStep piCode piStep current
  : clear implicits.

Lemma raw_sat_codedFormulaRankGapBelowTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M)
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep current,
  raw_formula_sat M e
    (codedFormulaRankGapBelowTermAt
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep current) <->
  RawCodedFormulaRankGapBelow M
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e sigmaCode) (raw_term_eval M e sigmaStep)
    (raw_term_eval M e piCode) (raw_term_eval M e piStep)
    (raw_term_eval M e current).
Proof.
  intros M e formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    current.
  unfold codedFormulaRankGapBelowTermAt,
    RawCodedFormulaRankGapBelow.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedFormulaRankTripleLookupTermAt_iff.
  setoid_rewrite raw_sat_formulaRankGapTermAt_iff.
  repeat setoid_rewrite raw_rankTraversal_eval_liftTerm_four.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition codedFormulaRankGapThroughTermAt
    (formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      bound current : term) : formula :=
  pImp (Formula.leTermAt current bound)
    (codedFormulaRankGapBelowTermAt
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep current).

Definition RawCodedFormulaRankGapThrough (M : RawPAModel)
    (formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      bound current : M) : Prop :=
  rawLe M current bound ->
  RawCodedFormulaRankGapBelow M
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep current.

Arguments RawCodedFormulaRankGapThrough
  M formulaCode formulaStep sigmaCode sigmaStep piCode piStep bound current
  : clear implicits.

Lemma raw_sat_codedFormulaRankGapThroughTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M)
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep bound current,
  raw_formula_sat M e
    (codedFormulaRankGapThroughTermAt
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      bound current) <->
  RawCodedFormulaRankGapThrough M
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e sigmaCode) (raw_term_eval M e sigmaStep)
    (raw_term_eval M e piCode) (raw_term_eval M e piStep)
    (raw_term_eval M e bound) (raw_term_eval M e current).
Proof.
  intros. unfold codedFormulaRankGapThroughTermAt,
    RawCodedFormulaRankGapThrough.
  cbn [raw_formula_sat].
  rewrite raw_sat_leTermAt_iff_rank.
  rewrite raw_sat_codedFormulaRankGapBelowTermAt_iff.
  reflexivity.
Qed.

Lemma raw_codedFormulaRankGapBelow_zero : forall (M : RawPAModel),
  RawPASatisfies M ->
  forall formulaCode formulaStep sigmaCode sigmaStep piCode piStep,
  RawCodedFormulaRankGapBelow M
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep (raw_zero M).
Proof.
  intros M hPA formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    index code sigma pi hindex _.
  exfalso. exact (raw_not_lt_zero M hPA index hindex).
Qed.

Lemma raw_codedFormulaRankGapBelow_succ : forall (M : RawPAModel),
  RawPASatisfies M ->
  forall formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root rootSigma rootPi current,
  RawCodedFormulaRankTraversal M
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root rootSigma rootPi ->
  rawLt M current bound ->
  RawCodedFormulaRankGapBelow M
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep current ->
  RawCodedFormulaRankGapBelow M
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    (raw_succ M current).
Proof.
  intros M hPA formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root rootSigma rootPi current htraversal
    hcurrentBound hbelow index code sigma pi hindex hlookup.
  destruct htraversal as
    [_ [_ [_ [_ [_ hrows]]]]].
  destruct (raw_lt_succ_cases M hPA index current hindex)
    as [hprior | ->].
  - exact (hbelow index code sigma pi hprior hlookup).
  - apply (raw_codedFormulaRankTraversalRow_gap M hPA
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      current code sigma pi
      (hrows current code sigma pi hcurrentBound hlookup)).
    intros childIndex child childSigma childPi hchild hchildLookup.
    exact (hbelow childIndex child childSigma childPi
      hchild hchildLookup).
Qed.

Lemma raw_codedFormulaRankGapThrough_zero : forall (M : RawPAModel),
  RawPASatisfies M ->
  forall formulaCode formulaStep sigmaCode sigmaStep piCode piStep bound,
  RawCodedFormulaRankGapThrough M
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound (raw_zero M).
Proof.
  intros M hPA formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound _.
  exact (raw_codedFormulaRankGapBelow_zero M hPA
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep).
Qed.

Lemma raw_codedFormulaRankGapThrough_succ : forall (M : RawPAModel),
  RawPASatisfies M ->
  forall formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root rootSigma rootPi current,
  RawCodedFormulaRankTraversal M
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root rootSigma rootPi ->
  RawCodedFormulaRankGapThrough M
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound current ->
  RawCodedFormulaRankGapThrough M
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound (raw_succ M current).
Proof.
  intros M hPA formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root rootSigma rootPi current htraversal
    hcurrent hsuccBound.
  assert (hcurrentBound : rawLe M current bound).
  {
    exact (raw_le_trans M hPA current (raw_succ M current) bound
      (raw_rankGap_le_succ M hPA current) hsuccBound).
  }
  apply (raw_codedFormulaRankGapBelow_succ M hPA
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root rootSigma rootPi current htraversal).
  - exact (raw_rank_lt_of_succ_le M hPA current bound hsuccBound).
  - exact (hcurrent hcurrentBound).
Qed.

(** PA induction is applied to the displayed arithmetic formula.  This is
    the crucial point that keeps the proof valid when [bound] is a
    nonstandard element of [M]. *)
Theorem raw_codedFormulaRankGapThrough_all : forall (M : RawPAModel),
  RawPASatisfies M ->
  forall formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root rootSigma rootPi,
  RawCodedFormulaRankTraversal M
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root rootSigma rootPi ->
  forall current,
  RawCodedFormulaRankGapThrough M
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound current.
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
  set (phi := codedFormulaRankGapThroughTermAt
    (tVar 1) (tVar 2) (tVar 3) (tVar 4)
    (tVar 5) (tVar 6) (tVar 7) (tVar 0)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2 (raw_sat_codedFormulaRankGapThroughTermAt_iff M
        (scons M (raw_zero M) parameterEnv)
        (tVar 1) (tVar 2) (tVar 3) (tVar 4)
        (tVar 5) (tVar 6) (tVar 7) (tVar 0))).
      unfold parameterEnv. cbn [raw_term_eval scons].
      exact (raw_codedFormulaRankGapThrough_zero M hPA
        formulaCode formulaStep sigmaCode sigmaStep piCode piStep bound).
    - intros current hcurrentSat.
      unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_codedFormulaRankGapThroughTermAt_iff M
          (scons M current parameterEnv)
          (tVar 1) (tVar 2) (tVar 3) (tVar 4)
          (tVar 5) (tVar 6) (tVar 7) (tVar 0))
        hcurrentSat) as hcurrent.
      apply (proj2
        (raw_sat_codedFormulaRankGapThroughTermAt_iff M
          (scons M (raw_succ M current) parameterEnv)
          (tVar 1) (tVar 2) (tVar 3) (tVar 4)
          (tVar 5) (tVar 6) (tVar 7) (tVar 0))).
      unfold parameterEnv in hcurrent |- *.
      cbn [raw_term_eval scons] in hcurrent |- *.
      exact (raw_codedFormulaRankGapThrough_succ M hPA
        formulaCode formulaStep sigmaCode sigmaStep piCode piStep
        bound rootIndex root rootSigma rootPi current
        htraversal hcurrent).
  }
  intro current.
  unfold phi in hall.
  pose proof (proj1
    (raw_sat_codedFormulaRankGapThroughTermAt_iff M
      (scons M current parameterEnv)
      (tVar 1) (tVar 2) (tVar 3) (tVar 4)
      (tVar 5) (tVar 6) (tVar 7) (tVar 0))
    (hall current)) as hraw.
  unfold parameterEnv in hraw.
  cbn [raw_term_eval scons] in hraw. exact hraw.
Qed.

Theorem raw_codedFormulaRankTraversal_gap : forall (M : RawPAModel),
  RawPASatisfies M ->
  forall formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root sigma pi,
  RawCodedFormulaRankTraversal M
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root sigma pi ->
  RawFormulaRankGap M sigma pi.
Proof.
  intros M hPA formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root sigma pi htraversal.
  pose proof (raw_codedFormulaRankGapThrough_all M hPA
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root sigma pi htraversal bound) as hthrough.
  destruct htraversal as
    [_ [_ [_ [hrootIndex [hrootLookup _]]]]].
  exact ((hthrough (raw_rank_le_refl M hPA bound))
    rootIndex root sigma pi hrootIndex hrootLookup).
Qed.

(** Public theorem: no decoder and no standardness assumption occurs in the
    statement.  Every honest public rank certificate has the gap. *)
Theorem raw_codedFormulaRank_gap : forall (M : RawPAModel),
  RawPASatisfies M -> forall root sigma pi,
  RawCodedFormulaRank M root sigma pi ->
  rawLe M sigma (raw_succ M pi) /\
  rawLe M pi (raw_succ M sigma).
Proof.
  intros M hPA root sigma pi
    (formulaCode & formulaStep & sigmaCode & sigmaStep &
     piCode & piStep & bound & rootIndex & htraversal).
  exact (raw_codedFormulaRankTraversal_gap M hPA
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root sigma pi htraversal).
Qed.

(** ------------------------------------------------------------------
    Both polarity domains at the next fixed level. *)

Theorem raw_formulaQuantifierBounded_fixedLevel_both : forall
    (M : RawPAModel), RawPASatisfies M -> forall level code,
  RawFormulaQuantifierBounded M level code ->
  RawFixedLevelSigmaDomain M (S level) code /\
  RawFixedLevelPiDomain M (S level) code.
Proof.
  intros M hPA level code [hsigmaDomain | hpiDomain].
  - destruct hsigmaDomain as (sigma & pi & hrank & hsigmaBound).
    destruct (raw_codedFormulaRank_gap M hPA code sigma pi hrank)
      as [hsigmaPi hpiSigma].
    assert (hsuccSigmaBound :
        rawLe M (raw_succ M sigma) (rawNumeralValue M (S level))).
    {
      change (rawLe M (raw_succ M sigma)
        (raw_succ M (rawNumeralValue M level))).
      exact (raw_rank_succ_le M hPA sigma
        (rawNumeralValue M level) hsigmaBound).
    }
    split.
    + exists sigma, pi. split; [exact hrank |].
      exact (raw_le_trans M hPA sigma (raw_succ M sigma)
        (rawNumeralValue M (S level))
        (raw_rankGap_le_succ M hPA sigma) hsuccSigmaBound).
    + exists sigma, pi. split; [exact hrank |].
      exact (raw_le_trans M hPA pi (raw_succ M sigma)
        (rawNumeralValue M (S level)) hpiSigma hsuccSigmaBound).
  - destruct hpiDomain as (sigma & pi & hrank & hpiBound).
    destruct (raw_codedFormulaRank_gap M hPA code sigma pi hrank)
      as [hsigmaPi hpiSigma].
    assert (hsuccPiBound :
        rawLe M (raw_succ M pi) (rawNumeralValue M (S level))).
    {
      change (rawLe M (raw_succ M pi)
        (raw_succ M (rawNumeralValue M level))).
      exact (raw_rank_succ_le M hPA pi
        (rawNumeralValue M level) hpiBound).
    }
    split.
    + exists sigma, pi. split; [exact hrank |].
      exact (raw_le_trans M hPA sigma (raw_succ M pi)
        (rawNumeralValue M (S level)) hsigmaPi hsuccPiBound).
    + exists sigma, pi. split; [exact hrank |].
      exact (raw_le_trans M hPA pi (raw_succ M pi)
        (rawNumeralValue M (S level))
        (raw_rankGap_le_succ M hPA pi) hsuccPiBound).
Qed.

Corollary raw_formulaQuantifierBounded_fixedLevel_sigma : forall
    (M : RawPAModel), RawPASatisfies M -> forall level code,
  RawFormulaQuantifierBounded M level code ->
  RawFixedLevelSigmaDomain M (S level) code.
Proof.
  intros M hPA level code hbounded.
  exact (proj1 (raw_formulaQuantifierBounded_fixedLevel_both
    M hPA level code hbounded)).
Qed.

Corollary raw_formulaQuantifierBounded_fixedLevel_pi : forall
    (M : RawPAModel), RawPASatisfies M -> forall level code,
  RawFormulaQuantifierBounded M level code ->
  RawFixedLevelPiDomain M (S level) code.
Proof.
  intros M hPA level code hbounded.
  exact (proj2 (raw_formulaQuantifierBounded_fixedLevel_both
    M hPA level code hbounded)).
Qed.

(** ------------------------------------------------------------------
    Closed arithmetic statements and their PA derivations. *)

Definition RawCodedFormulaRankGapLaw (M : RawPAModel) : Prop :=
  forall root sigma pi : M,
    RawCodedFormulaRank M root sigma pi ->
    RawFormulaRankGap M sigma pi.

Definition codedFormulaRankGapFormula : formula :=
  pAll
    (pAll
      (pAll
        (pImp
          (codedFormulaRankTermAt (tVar 2) (tVar 1) (tVar 0))
          (formulaRankGapTermAt (tVar 1) (tVar 0))))).

Lemma raw_sat_codedFormulaRankGapFormula_iff : forall
    (M : RawPAModel) (e : nat -> M),
  raw_formula_sat M e codedFormulaRankGapFormula <->
  RawCodedFormulaRankGapLaw M.
Proof.
  intros M e.
  unfold codedFormulaRankGapFormula, RawCodedFormulaRankGapLaw.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_codedFormulaRankTermAt_iff.
  setoid_rewrite raw_sat_formulaRankGapTermAt_iff.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Theorem codedFormulaRankGapFormula_sentence :
  Formula.Sentence codedFormulaRankGapFormula.
Proof.
  intros k hfree.
  unfold codedFormulaRankGapFormula, formulaRankGapTermAt in hfree.
  cbn in hfree. lia.
Qed.

Theorem codedFormulaRankGapFormula_raw_valid : forall
    (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e codedFormulaRankGapFormula.
Proof.
  intros M hPA e.
  apply (proj2 (raw_sat_codedFormulaRankGapFormula_iff M e)).
  intros root sigma pi hrank.
  exact (raw_codedFormulaRank_gap M hPA root sigma pi hrank).
Qed.

Theorem PA_proves_codedFormulaRankGapFormula :
  Formula.BProv Formula.Ax_s [] codedFormulaRankGapFormula.
Proof.
  apply PA_BProv_of_raw_valid.
  - exact codedFormulaRankGapFormula_sentence.
  - exact codedFormulaRankGapFormula_raw_valid.
Qed.

Definition fixedLevelRankLiftFormula (level : nat) : formula :=
  pAll
    (pImp
      (formulaQuantifierBoundedTermAt level (tVar 0))
      (pAnd
        (fixedLevelSigmaDomainTermAt (S level) (tVar 0))
        (fixedLevelPiDomainTermAt (S level) (tVar 0)))).

Lemma raw_sat_fixedLevelRankLiftFormula_iff : forall
    (M : RawPAModel) (e : nat -> M) level,
  raw_formula_sat M e (fixedLevelRankLiftFormula level) <->
  forall code : M,
    RawFormulaQuantifierBounded M level code ->
    RawFixedLevelSigmaDomain M (S level) code /\
    RawFixedLevelPiDomain M (S level) code.
Proof.
  intros M e level.
  unfold fixedLevelRankLiftFormula.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_formulaQuantifierBoundedTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelSigmaDomainTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelPiDomainTermAt_iff.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Theorem fixedLevelRankLiftFormula_sentence : forall level,
  Formula.Sentence (fixedLevelRankLiftFormula level).
Proof.
  induction level as [|level IH]; intros k hfree.
  - unfold fixedLevelRankLiftFormula in hfree.
    cbn in hfree. lia.
  - apply (IH k).
    unfold fixedLevelRankLiftFormula in hfree |- *.
    cbn in hfree |- *. exact hfree.
Qed.

Theorem fixedLevelRankLiftFormula_raw_valid : forall level
    (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e (fixedLevelRankLiftFormula level).
Proof.
  intros level M hPA e.
  apply (proj2 (raw_sat_fixedLevelRankLiftFormula_iff M e level)).
  exact (raw_formulaQuantifierBounded_fixedLevel_both M hPA level).
Qed.

Theorem PA_proves_fixedLevelRankLiftFormula : forall level,
  Formula.BProv Formula.Ax_s [] (fixedLevelRankLiftFormula level).
Proof.
  intro level. apply PA_BProv_of_raw_valid.
  - exact (fixedLevelRankLiftFormula_sentence level).
  - exact (fixedLevelRankLiftFormula_raw_valid level).
Qed.

End PABoundedRawCodedFormulaRankGap.
