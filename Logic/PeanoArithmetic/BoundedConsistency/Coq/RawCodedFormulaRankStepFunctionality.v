(**
  Arithmetic functionality of the local Sigma/Pi rank equations.

  Constructor recovery and beta-table lookup belong to the global traversal.
  This file proves the reusable local fact beneath that layer: maximum is
  functional in every raw PA model, hence each of the seven constructor rank
  equations has a unique Sigma/Pi output once its child ranks are fixed.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import RawCodedFormulaRankStep.

Module PABoundedRawCodedFormulaRankStepFunctionality.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedFormulaRankStep.

Lemma raw_max_relation_functional : forall (M : RawPAModel),
  RawPASatisfies M -> forall first second left right : M,
  RawMax M first left right ->
  RawMax M second left right ->
  first = second.
Proof.
  intros M hPA first second left right
    [[hle1 hout1] | [hle1 hout1]]
    [[hle2 hout2] | [hle2 hout2]].
  - now rewrite hout1, hout2.
  - pose proof (raw_le_antisymm M hPA left right hle1 hle2) as heq.
    now rewrite hout1, hout2, heq.
  - pose proof (raw_le_antisymm M hPA right left hle1 hle2) as heq.
    now rewrite hout1, hout2, heq.
  - now rewrite hout1, hout2.
Qed.

Lemma raw_formulaRankZero_functional : forall (M : RawPAModel),
  forall sigma1 pi1 sigma2 pi2 : M,
  RawFormulaRankZero M sigma1 pi1 ->
  RawFormulaRankZero M sigma2 pi2 ->
  sigma1 = sigma2 /\ pi1 = pi2.
Proof.
  intros M sigma1 pi1 sigma2 pi2 [hs1 hp1] [hs2 hp2].
  now rewrite hs1, hp1, hs2, hp2.
Qed.

Lemma raw_formulaRankImp_functional : forall (M : RawPAModel),
  RawPASatisfies M ->
  forall sigma1 pi1 sigma2 pi2 leftSigma leftPi rightSigma rightPi : M,
  RawFormulaRankImp M sigma1 pi1
    leftSigma leftPi rightSigma rightPi ->
  RawFormulaRankImp M sigma2 pi2
    leftSigma leftPi rightSigma rightPi ->
  sigma1 = sigma2 /\ pi1 = pi2.
Proof.
  intros M hPA sigma1 pi1 sigma2 pi2
    leftSigma leftPi rightSigma rightPi
    [hsigma1 hpi1] [hsigma2 hpi2].
  split.
  - exact (raw_max_relation_functional M hPA
      sigma1 sigma2 leftPi rightSigma hsigma1 hsigma2).
  - exact (raw_max_relation_functional M hPA
      pi1 pi2 leftSigma rightPi hpi1 hpi2).
Qed.

Lemma raw_formulaRankAndOr_functional : forall (M : RawPAModel),
  RawPASatisfies M ->
  forall sigma1 pi1 sigma2 pi2 leftSigma leftPi rightSigma rightPi : M,
  RawFormulaRankAndOr M sigma1 pi1
    leftSigma leftPi rightSigma rightPi ->
  RawFormulaRankAndOr M sigma2 pi2
    leftSigma leftPi rightSigma rightPi ->
  sigma1 = sigma2 /\ pi1 = pi2.
Proof.
  intros M hPA sigma1 pi1 sigma2 pi2
    leftSigma leftPi rightSigma rightPi
    [hsigma1 hpi1] [hsigma2 hpi2].
  split.
  - exact (raw_max_relation_functional M hPA
      sigma1 sigma2 leftSigma rightSigma hsigma1 hsigma2).
  - exact (raw_max_relation_functional M hPA
      pi1 pi2 leftPi rightPi hpi1 hpi2).
Qed.

Lemma raw_formulaRankAll_functional : forall (M : RawPAModel),
  RawPASatisfies M ->
  forall sigma1 pi1 sigma2 pi2 childSigma childPi : M,
  RawFormulaRankAll M sigma1 pi1 childSigma childPi ->
  RawFormulaRankAll M sigma2 pi2 childSigma childPi ->
  sigma1 = sigma2 /\ pi1 = pi2.
Proof.
  intros M hPA sigma1 pi1 sigma2 pi2 childSigma childPi
    [base1 [hmax1 [hpi1 hsigma1]]]
    [base2 [hmax2 [hpi2 hsigma2]]].
  assert (hbase : base1 = base2).
  {
    exact (raw_max_relation_functional M hPA base1 base2
      (rawNumeralValue M 1) childPi hmax1 hmax2).
  }
  split.
  - now rewrite hsigma1, hsigma2, hbase.
  - now rewrite hpi1, hpi2, hbase.
Qed.

Lemma raw_formulaRankEx_functional : forall (M : RawPAModel),
  RawPASatisfies M ->
  forall sigma1 pi1 sigma2 pi2 childSigma childPi : M,
  RawFormulaRankEx M sigma1 pi1 childSigma childPi ->
  RawFormulaRankEx M sigma2 pi2 childSigma childPi ->
  sigma1 = sigma2 /\ pi1 = pi2.
Proof.
  intros M hPA sigma1 pi1 sigma2 pi2 childSigma childPi
    [base1 [hmax1 [hsigma1 hpi1]]]
    [base2 [hmax2 [hsigma2 hpi2]]].
  assert (hbase : base1 = base2).
  {
    exact (raw_max_relation_functional M hPA base1 base2
      (rawNumeralValue M 1) childSigma hmax1 hmax2).
  }
  split.
  - now rewrite hsigma1, hsigma2, hbase.
  - now rewrite hpi1, hpi2, hbase.
Qed.

(** The constructor wrappers expose the same result at the exact relation
    names consumed by a traversal.  The code equality itself is irrelevant
    here because all child fields are already fixed. *)

Lemma raw_formulaEqRankStep_output_functional : forall (M : RawPAModel),
  forall code left right sigma1 pi1 sigma2 pi2 : M,
  RawFormulaEqRankStep M code sigma1 pi1 left right ->
  RawFormulaEqRankStep M code sigma2 pi2 left right ->
  sigma1 = sigma2 /\ pi1 = pi2.
Proof.
  intros M code left right sigma1 pi1 sigma2 pi2
    [_ hrank1] [_ hrank2].
  exact (raw_formulaRankZero_functional M
    sigma1 pi1 sigma2 pi2 hrank1 hrank2).
Qed.

Lemma raw_formulaBotRankStep_output_functional : forall (M : RawPAModel),
  forall code sigma1 pi1 sigma2 pi2 : M,
  RawFormulaBotRankStep M code sigma1 pi1 ->
  RawFormulaBotRankStep M code sigma2 pi2 ->
  sigma1 = sigma2 /\ pi1 = pi2.
Proof.
  intros M code sigma1 pi1 sigma2 pi2 [_ hrank1] [_ hrank2].
  exact (raw_formulaRankZero_functional M
    sigma1 pi1 sigma2 pi2 hrank1 hrank2).
Qed.

Lemma raw_formulaImpRankStep_output_functional :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall code left leftSigma leftPi right rightSigma rightPi
    sigma1 pi1 sigma2 pi2 : M,
  RawFormulaImpRankStep M code sigma1 pi1
    left leftSigma leftPi right rightSigma rightPi ->
  RawFormulaImpRankStep M code sigma2 pi2
    left leftSigma leftPi right rightSigma rightPi ->
  sigma1 = sigma2 /\ pi1 = pi2.
Proof.
  intros M hPA code left leftSigma leftPi right rightSigma rightPi
    sigma1 pi1 sigma2 pi2 [_ hrank1] [_ hrank2].
  exact (raw_formulaRankImp_functional M hPA
    sigma1 pi1 sigma2 pi2 leftSigma leftPi rightSigma rightPi
    hrank1 hrank2).
Qed.

Lemma raw_formulaAndRankStep_output_functional :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall code left leftSigma leftPi right rightSigma rightPi
    sigma1 pi1 sigma2 pi2 : M,
  RawFormulaAndRankStep M code sigma1 pi1
    left leftSigma leftPi right rightSigma rightPi ->
  RawFormulaAndRankStep M code sigma2 pi2
    left leftSigma leftPi right rightSigma rightPi ->
  sigma1 = sigma2 /\ pi1 = pi2.
Proof.
  intros M hPA code left leftSigma leftPi right rightSigma rightPi
    sigma1 pi1 sigma2 pi2 [_ hrank1] [_ hrank2].
  exact (raw_formulaRankAndOr_functional M hPA
    sigma1 pi1 sigma2 pi2 leftSigma leftPi rightSigma rightPi
    hrank1 hrank2).
Qed.

Lemma raw_formulaOrRankStep_output_functional :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall code left leftSigma leftPi right rightSigma rightPi
    sigma1 pi1 sigma2 pi2 : M,
  RawFormulaOrRankStep M code sigma1 pi1
    left leftSigma leftPi right rightSigma rightPi ->
  RawFormulaOrRankStep M code sigma2 pi2
    left leftSigma leftPi right rightSigma rightPi ->
  sigma1 = sigma2 /\ pi1 = pi2.
Proof.
  intros M hPA code left leftSigma leftPi right rightSigma rightPi
    sigma1 pi1 sigma2 pi2 [_ hrank1] [_ hrank2].
  exact (raw_formulaRankAndOr_functional M hPA
    sigma1 pi1 sigma2 pi2 leftSigma leftPi rightSigma rightPi
    hrank1 hrank2).
Qed.

Lemma raw_formulaAllRankStep_output_functional :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall code child childSigma childPi sigma1 pi1 sigma2 pi2 : M,
  RawFormulaAllRankStep M code sigma1 pi1 child childSigma childPi ->
  RawFormulaAllRankStep M code sigma2 pi2 child childSigma childPi ->
  sigma1 = sigma2 /\ pi1 = pi2.
Proof.
  intros M hPA code child childSigma childPi sigma1 pi1 sigma2 pi2
    [_ hrank1] [_ hrank2].
  exact (raw_formulaRankAll_functional M hPA
    sigma1 pi1 sigma2 pi2 childSigma childPi hrank1 hrank2).
Qed.

Lemma raw_formulaExRankStep_output_functional :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall code child childSigma childPi sigma1 pi1 sigma2 pi2 : M,
  RawFormulaExRankStep M code sigma1 pi1 child childSigma childPi ->
  RawFormulaExRankStep M code sigma2 pi2 child childSigma childPi ->
  sigma1 = sigma2 /\ pi1 = pi2.
Proof.
  intros M hPA code child childSigma childPi sigma1 pi1 sigma2 pi2
    [_ hrank1] [_ hrank2].
  exact (raw_formulaRankEx_functional M hPA
    sigma1 pi1 sigma2 pi2 childSigma childPi hrank1 hrank2).
Qed.

End PABoundedRawCodedFormulaRankStepFunctionality.
