(**
  PA proves injectivity of the canonical polynomial pairing function.

  The pairing polynomial is [P(a,b) = (a+b)^2+a].  Its value lies in the
  half-open interval [[(a+b)^2,(a+b+1)^2)].  These intervals are disjoint in
  every model of PA; equality of pair values therefore first identifies the
  diagonal sum and then both coordinates by additive cancellation.

  We establish this directly for arbitrary raw PA models and invoke the
  project's raw-model completeness theorem to obtain the requested checked
  PA derivation of [polynomialPairInjectiveFormula].
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness RawCodedSyntaxConstructors
  RawCodedSyntaxConstructorSeparation.

Import ListNotations.

Module PABoundedPolynomialPairInjectivity.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedSyntaxConstructorSeparation.

(** Small raw semiring consequences used in the interval argument. *)

Lemma raw_succ_add_pair : forall (M : RawPAModel),
  RawPASatisfies M -> forall x y : M,
  raw_add M (raw_succ M x) y = raw_succ M (raw_add M x y).
Proof.
  intros M hPA x y.
  set (e := scons M x (scons M y (fun _ : nat => raw_zero M))).
  pose proof (raw_eq_of_closed_bprov M hPA
    (tAdd (tSucc (tVar 0)) (tVar 1))
    (tSucc (tAdd (tVar 0) (tVar 1))) e
    (Formula.BProv_Ax_s_succ_add_terms [] (tVar 0) (tVar 1))) as h.
  cbn [raw_term_eval scons] in h. exact h.
Qed.

Lemma raw_add_mul_pair : forall (M : RawPAModel),
  RawPASatisfies M -> forall x y z : M,
  raw_mul M (raw_add M x y) z =
  raw_add M (raw_mul M x z) (raw_mul M y z).
Proof.
  intros M hPA x y z.
  set (e := scons M x (scons M y
    (scons M z (fun _ : nat => raw_zero M)))).
  pose proof (raw_eq_of_closed_bprov M hPA
    (tMul (tAdd (tVar 0) (tVar 1)) (tVar 2))
    (tAdd (tMul (tVar 0) (tVar 2))
      (tMul (tVar 1) (tVar 2))) e
    (Formula.BProv_Ax_s_add_mul_terms []
      (tVar 0) (tVar 1) (tVar 2))) as h.
  cbn [raw_term_eval scons] in h. exact h.
Qed.

Lemma raw_add_cancel_left_pair : forall (M : RawPAModel),
  RawPASatisfies M -> forall x y z : M,
  raw_add M x y = raw_add M x z -> y = z.
Proof.
  intros M hPA x y z heq.
  set (f := pEq (tAdd (tVar 0) (tVar 1))
    (tAdd (tVar 0) (tVar 2))).
  set (G := [f] : list formula).
  assert (hass : Formula.BProv Formula.Ax_s G f).
  {
    apply Formula.BProv_ass. unfold G. simpl. now left.
  }
  pose proof (Formula.BProv_Ax_s_add_cancel_left_terms G
    (tVar 0) (tVar 1) (tVar 2) hass) as hcancel.
  set (e := scons M x (scons M y
    (scons M z (fun _ : nat => raw_zero M)))).
  apply (raw_sat_of_BProv_axs_context M G _ hPA hcancel e).
  intros g hg. unfold G in hg. simpl in hg.
  destruct hg as [<- | []].
  cbn [raw_formula_sat raw_term_eval scons]. exact heq.
Qed.

Lemma raw_mul_le_right_pair : forall (M : RawPAModel),
  RawPASatisfies M -> forall x y z : M,
  rawLe M x y -> rawLe M (raw_mul M x z) (raw_mul M y z).
Proof.
  intros M hPA x y z [gap hgap].
  exists (raw_mul M gap z).
  rewrite <- raw_add_mul_pair by exact hPA.
  now rewrite hgap.
Qed.

Lemma raw_square_monotone_pair : forall (M : RawPAModel),
  RawPASatisfies M -> forall x y : M,
  rawLe M x y -> rawLe M (raw_mul M x x) (raw_mul M y y).
Proof.
  intros M hPA x y hxy.
  pose proof (raw_mul_le_right_pair M hPA x y x hxy) as hfirst.
  pose proof (raw_mul_le_right_pair M hPA x y y hxy) as hsecond.
  rewrite (raw_mul_comm M hPA y x) in hfirst.
  exact (raw_le_trans M hPA _ _ _ hfirst hsecond).
Qed.

Lemma raw_succ_le_of_lt_pair : forall (M : RawPAModel),
  RawPASatisfies M -> forall x y : M,
  rawLt M x y -> rawLe M (raw_succ M x) y.
Proof.
  intros M hPA x y [gap hgap].
  exists gap.
  rewrite raw_succ_add_pair by exact hPA.
  rewrite <- raw_add_succ by exact hPA.
  exact hgap.
Qed.

Lemma raw_lt_le_trans_pair : forall (M : RawPAModel),
  RawPASatisfies M -> forall x y z : M,
  rawLt M x y -> rawLe M y z -> rawLt M x z.
Proof.
  intros M hPA x y z [strictGap hxy] [weakGap hyz].
  exists (raw_add M strictGap weakGap).
  rewrite raw_add_succ by exact hPA.
  rewrite <- raw_add_assoc by exact hPA.
  rewrite <- raw_succ_add_pair by exact hPA.
  rewrite <- raw_add_succ by exact hPA.
  rewrite hxy. exact hyz.
Qed.

(** The lower square bound is immediate from the final [+a]. *)
Lemma rawPolynomialPair_lower_square : forall (M : RawPAModel),
  forall a b : M,
  rawLe M
    (raw_mul M (raw_add M a b) (raw_add M a b))
    (rawPolynomialPair M a b).
Proof.
  intros M a b. exists a. reflexivity.
Qed.

(** The strict upper square bound.  The explicit gap is [a+2b], since

      (a+b+1)^2 - ((a+b)^2+a) = (a+2b)+1.

    The proof below is only associativity/commutativity plus the two PA
    successor recurrences. *)
Lemma rawPolynomialPair_upper_square : forall (M : RawPAModel),
  RawPASatisfies M -> forall a b : M,
  rawLt M (rawPolynomialPair M a b)
    (raw_mul M (raw_succ M (raw_add M a b))
      (raw_succ M (raw_add M a b))).
Proof.
  intros M hPA a b.
  unfold rawLt.
  exists (raw_add M a (raw_add M b b)).
  unfold rawPolynomialPair.
  set (s := raw_add M a b).
  fold s.
  rewrite raw_add_succ by exact hPA.
  rewrite raw_succ_mul by exact hPA.
  rewrite (raw_mul_comm M hPA s (raw_succ M s)).
  rewrite raw_succ_mul by exact hPA.
  rewrite raw_add_succ by exact hPA.
  f_equal.
  rewrite !raw_add_assoc by exact hPA.
  f_equal.
  unfold s.
  symmetry.
  rewrite raw_add_assoc by exact hPA.
  f_equal.
  rewrite <- (raw_add_assoc M hPA b a b).
  rewrite (raw_add_comm M hPA b a).
  rewrite (raw_add_assoc M hPA a b b).
  reflexivity.
Qed.

Lemma rawPolynomialPair_strict_of_sum_lt : forall (M : RawPAModel),
  RawPASatisfies M -> forall a b c d : M,
  rawLt M (raw_add M a b) (raw_add M c d) ->
  rawLt M (rawPolynomialPair M a b) (rawPolynomialPair M c d).
Proof.
  intros M hPA a b c d hsum.
  set (leftSum := raw_add M a b).
  set (rightSum := raw_add M c d).
  assert (hsuccLe : rawLe M (raw_succ M leftSum) rightSum).
  {
    apply raw_succ_le_of_lt_pair. exact hPA. exact hsum.
  }
  assert (hsquareLe : rawLe M
      (raw_mul M (raw_succ M leftSum) (raw_succ M leftSum))
      (raw_mul M rightSum rightSum)).
  {
    apply raw_square_monotone_pair; assumption.
  }
  pose proof (rawPolynomialPair_upper_square M hPA a b) as hupper.
  fold leftSum in hupper.
  pose proof (rawPolynomialPair_lower_square M c d) as hlower.
  fold rightSum in hlower.
  exact (raw_lt_le_trans_pair M hPA _ _ _
    (raw_lt_le_trans_pair M hPA _ _ _ hupper hsquareLe) hlower).
Qed.

(** Main raw-model theorem. *)
Theorem rawPolynomialPair_injective : forall (M : RawPAModel),
  RawPASatisfies M -> RawPolynomialPairInjective M.
Proof.
  intros M hPA a b c d heq.
  set (leftSum := raw_add M a b).
  set (rightSum := raw_add M c d).
  destruct (raw_order_trichotomy M hPA leftSum rightSum)
    as [hsums | [hlt | hgt]].
  - assert (ha : a = c).
    {
      unfold rawPolynomialPair in heq.
      fold leftSum in heq. fold rightSum in heq.
      rewrite hsums in heq.
      exact (raw_add_cancel_left_pair M hPA
        (raw_mul M rightSum rightSum) a c heq).
    }
    split; [exact ha |].
    unfold leftSum, rightSum in hsums.
    rewrite ha in hsums.
    exact (raw_add_cancel_left_pair M hPA c b d hsums).
  - exfalso.
    pose proof (rawPolynomialPair_strict_of_sum_lt M hPA
      a b c d hlt) as hpLt.
    rewrite heq in hpLt.
    exact (raw_not_lt_self M hPA _ hpLt).
  - exfalso.
    pose proof (rawPolynomialPair_strict_of_sum_lt M hPA
      c d a b hgt) as hpLt.
    rewrite heq in hpLt.
    exact (raw_not_lt_self M hPA _ hpLt).
Qed.

(** ------------------------------------------------------------------
    Closing the explicit PA sentence by raw-model completeness. *)

Theorem polynomialPairInjectiveFormula_sentence :
  Formula.Sentence polynomialPairInjectiveFormula.
Proof.
  intros k hfree.
  unfold polynomialPairInjectiveFormula,
    polynomialPairInjectiveTermAt in hfree.
  cbn in hfree. lia.
Qed.

Theorem polynomialPairInjectiveFormula_raw_valid : forall
    (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e polynomialPairInjectiveFormula.
Proof.
  intros M hPA e.
  apply (proj2 (raw_sat_polynomialPairInjectiveFormula_iff M e)).
  exact (rawPolynomialPair_injective M hPA).
Qed.

Theorem PA_proves_polynomialPairInjectiveFormula :
  Formula.BProv Formula.Ax_s [] polynomialPairInjectiveFormula.
Proof.
  apply PA_BProv_of_raw_valid.
  - exact polynomialPairInjectiveFormula_sentence.
  - exact polynomialPairInjectiveFormula_raw_valid.
Qed.

Corollary polynomialPairInjectivityProof :
  PolynomialPairInjectivityProof.
Proof.
  exact PA_proves_polynomialPairInjectiveFormula.
Qed.

Corollary rawListNode_injective : forall (M : RawPAModel),
  RawPASatisfies M -> RawListNodeInjective M.
Proof.
  intros M hPA.
  apply raw_listNode_injective_of_pair_injective; [exact hPA |].
  exact (rawPolynomialPair_injective M hPA).
Qed.

End PABoundedPolynomialPairInjectivity.
