(* ===================================================================== *)
(*  PAHFTermGraphFunctional.v                                             *)
(*                                                                       *)
(*  Functionality of recursive arithmetic traces and translated PA term  *)
(*  graphs in arbitrary finite first-order HF models.                     *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Lia List.
From SetTheory Require Import Fol PAHF PAHFInterpretations
  PAHFTermGraphModel PAHFTermGraphTotal.

Import ListNotations.

(* Two successor-recursion traces with the same base agree at every
   ordinal-like key covered by both traces. *)
Lemma fofam_succ_rec_approx_value_unique :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V)
    (s f g m z w : V),
  OrdinalLike (foam_mem V M) m ->
  foam_succ_rec_approx V M s f m ->
  foam_mem V M (foam_kpair_obj V M m z) f ->
  foam_succ_rec_approx V M s g m ->
  foam_mem V M (foam_kpair_obj V M m w) g ->
  z = w.
Proof.
  intros V M s f g m z w hm hf hz hg hw.
  pose (phi :=
    fAll
      (fImp (fOr (fMem 1 0) (fEq 1 0))
        (fImp (HF_ordinalLikeAt 0)
          (fImp (HF_succRecApproxAt 3 2 0)
            (fImp (HF_succRecApproxAt 4 2 0)
              (fAll
                (fImp (HF_pairMemAt 2 0 4)
                  (fAll (fImp (HF_pairMemAt 3 0 6) (fEq 1 0)))))))))).
  pose (tail := fun _ : nat => foam_empty V M).
  pose proof (foam_induction_schema V M phi
    (scons V s (scons V f (scons V g tail)))) as hind.
  assert (hall : forall k,
    Sat V (foam_mem V M)
      (scons V k (scons V s (scons V f (scons V g tail)))) phi).
  {
    apply hind.
    intros k ih.
    unfold phi.
    simpl.
    intros r hkr hrSat hfSat hgSat y hySat u huSat.
    pose (Er := scons V r
      (scons V k (scons V s (scons V f (scons V g tail))))).
    pose (Ey := scons V y Er).
    pose (Eu := scons V u Ey).
    assert (hrOrd : OrdinalLike (foam_mem V M) r).
    {
      exact (proj1 (HF_ordinalLikeAt_spec V (foam_mem V M) Er 0)
        hrSat).
    }
    assert (hfApprox : foam_succ_rec_approx V M s f r).
    {
      pose proof (proj1 (foam_HF_succRecApproxAt_spec V M Er 3 2 0)
        hfSat) as h.
      change (foam_succ_rec_approx V M s f r) in h.
      exact h.
    }
    assert (hgApprox : foam_succ_rec_approx V M s g r).
    {
      pose proof (proj1 (foam_HF_succRecApproxAt_spec V M Er 4 2 0)
        hgSat) as h.
      change (foam_succ_rec_approx V M s g r) in h.
      exact h.
    }
    assert (hpairF : foam_mem V M (foam_kpair_obj V M k y) f).
    {
      pose proof (proj1 (foam_HF_pairMemAt_spec V M Ey 2 0 4)
        hySat) as h.
      change (foam_mem V M (foam_kpair_obj V M k y) f) in h.
      exact h.
    }
    assert (hpairG : foam_mem V M (foam_kpair_obj V M k u) g).
    {
      pose proof (proj1 (foam_HF_pairMemAt_spec V M Eu 3 0 6)
        huSat) as h.
      change (foam_mem V M (foam_kpair_obj V M k u) g) in h.
      exact h.
    }
    assert (hkOrd : OrdinalLike (foam_mem V M) k).
    {
      destruct hkr as [hkr | hkr].
      - exact (OrdinalLike_of_mem V (foam_mem V M) r k hrOrd hkr).
      - subst k. exact hrOrd.
    }
    destruct (fofam_OrdinalLike_empty_or_succ V M k hkOrd) as
      [hkEmpty | [p [hpk hkSucc]]].
    - destruct hfApprox as [hfunF [_hkeysF [hbaseF [_htotalF _hstepF]]]].
      destruct hgApprox as [hfunG [_hkeysG [hbaseG [_htotalG _hstepG]]]].
      assert (hpairEmptyF : foam_mem V M
        (foam_kpair_obj V M (foam_empty V M) y) f).
      { rewrite <- hkEmpty. exact hpairF. }
      assert (hpairEmptyG : foam_mem V M
        (foam_kpair_obj V M (foam_empty V M) u) g).
      { rewrite <- hkEmpty. exact hpairG. }
      pose proof (hfunF (foam_empty V M) y s hpairEmptyF hbaseF)
        as hy.
      pose proof (hfunG (foam_empty V M) u s hpairEmptyG hbaseG)
        as hu.
      exact (eq_trans hy (eq_sym hu)).
    - destruct hfApprox as
        [_hfunF [_hkeysF [_hbaseF [htotalF hstepF]]]].
      destruct hgApprox as
        [_hfunG [_hkeysG [_hbaseG [htotalG hstepG]]]].
      assert (hpr : foam_mem V M p r).
      {
        destruct hkr as [hkr | hkr].
        - exact (proj1 hrOrd k hkr p hpk).
        - subst k. exact hpk.
      }
      destruct (htotalF p (or_introl hpr)) as [t hpt].
      destruct (htotalG p (or_introl hpr)) as [v hpv].
      assert (hpSat : Sat V (foam_mem V M)
        (scons V p (scons V s (scons V f (scons V g tail)))) phi).
      {
        exact (proj1 (Sat_rename_rSkipParam V (foam_mem V M)
          phi (scons V s (scons V f (scons V g tail))) k p)
          (ih p hpk)).
      }
      pose (Erp := scons V r
        (scons V p (scons V s (scons V f (scons V g tail))))).
      pose (Etp := scons V t Erp).
      pose (Ev := scons V v Etp).
      assert (hrSatP : Sat V (foam_mem V M) Erp
        (HF_ordinalLikeAt 0)).
      {
        apply (proj2 (HF_ordinalLikeAt_spec V (foam_mem V M) Erp 0)).
        exact hrOrd.
      }
      assert (hfSatP : Sat V (foam_mem V M) Erp
        (HF_succRecApproxAt 3 2 0)).
      {
        apply (proj2 (foam_HF_succRecApproxAt_spec V M Erp 3 2 0)).
        change (foam_succ_rec_approx V M s f r).
        repeat split; assumption.
      }
      assert (hgSatP : Sat V (foam_mem V M) Erp
        (HF_succRecApproxAt 4 2 0)).
      {
        apply (proj2 (foam_HF_succRecApproxAt_spec V M Erp 4 2 0)).
        change (foam_succ_rec_approx V M s g r).
        repeat split; assumption.
      }
      assert (hptSat : Sat V (foam_mem V M) Etp
        (HF_pairMemAt 2 0 4)).
      {
        apply (proj2 (foam_HF_pairMemAt_spec V M Etp 2 0 4)).
        change (foam_mem V M (foam_kpair_obj V M p t) f).
        exact hpt.
      }
      assert (hpvSat : Sat V (foam_mem V M) Ev
        (HF_pairMemAt 3 0 6)).
      {
        apply (proj2 (foam_HF_pairMemAt_spec V M Ev 3 0 6)).
        change (foam_mem V M (foam_kpair_obj V M p v) g).
        exact hpv.
      }
      pose proof (hpSat r (or_introl hpr) hrSatP hfSatP hgSatP
        t hptSat v hpvSat) as htv.
      change (t = v) in htv.
      assert (hpairSuccF : foam_mem V M
        (foam_kpair_obj V M (foam_adjoin V M p p) y) f).
      { rewrite <- hkSucc. exact hpairF. }
      assert (hpairSuccG : foam_mem V M
        (foam_kpair_obj V M (foam_adjoin V M p p) u) g).
      { rewrite <- hkSucc. exact hpairG. }
      pose proof (hstepF p t y hpr hpt hpairSuccF) as hy.
      pose proof (hstepG p v u hpr hpv hpairSuccG) as hu.
      rewrite hy, hu, htv.
      reflexivity.
  }
  pose (Em := scons V m
    (scons V m (scons V s (scons V f (scons V g tail))))).
  pose (Ez := scons V z Em).
  pose (Ew := scons V w Ez).
  pose proof (hall m) as hmain.
  unfold phi in hmain.
  simpl in hmain.
  assert (hmSat : Sat V (foam_mem V M) Em (HF_ordinalLikeAt 0)).
  {
    apply (proj2 (HF_ordinalLikeAt_spec V (foam_mem V M) Em 0)).
    exact hm.
  }
  assert (hfSat : Sat V (foam_mem V M) Em
    (HF_succRecApproxAt 3 2 0)).
  {
    apply (proj2 (foam_HF_succRecApproxAt_spec V M Em 3 2 0)).
    change (foam_succ_rec_approx V M s f m).
    exact hf.
  }
  assert (hgSat : Sat V (foam_mem V M) Em
    (HF_succRecApproxAt 4 2 0)).
  {
    apply (proj2 (foam_HF_succRecApproxAt_spec V M Em 4 2 0)).
    change (foam_succ_rec_approx V M s g m).
    exact hg.
  }
  assert (hzSat : Sat V (foam_mem V M) Ez (HF_pairMemAt 2 0 4)).
  {
    apply (proj2 (foam_HF_pairMemAt_spec V M Ez 2 0 4)).
    change (foam_mem V M (foam_kpair_obj V M m z) f).
    exact hz.
  }
  assert (hwSat : Sat V (foam_mem V M) Ew (HF_pairMemAt 3 0 6)).
  {
    apply (proj2 (foam_HF_pairMemAt_spec V M Ew 3 0 6)).
    change (foam_mem V M (foam_kpair_obj V M m w) g).
    exact hw.
  }
  exact (hmain m (or_intror eq_refl) hmSat hfSat hgSat
    z hzSat w hwSat).
Qed.

(* Multiplication traces reduce their successor step to the preceding
   successor-recursion uniqueness theorem. *)
Lemma fofam_mul_rec_approx_value_unique :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V)
    (a f g m z w : V),
  OrdinalLike (foam_mem V M) a ->
  OrdinalLike (foam_mem V M) m ->
  foam_mul_rec_approx V M a f m ->
  foam_mem V M (foam_kpair_obj V M m z) f ->
  foam_mul_rec_approx V M a g m ->
  foam_mem V M (foam_kpair_obj V M m w) g ->
  z = w.
Proof.
  intros V M a f g m z w ha hm hf hz hg hw.
  pose (phi :=
    fAll
      (fImp (fOr (fMem 1 0) (fEq 1 0))
        (fImp (HF_ordinalLikeAt 0)
          (fImp (mulRecApproxAt 3 2 0)
            (fImp (mulRecApproxAt 4 2 0)
              (fAll
                (fImp (HF_pairMemAt 2 0 4)
                  (fAll (fImp (HF_pairMemAt 3 0 6) (fEq 1 0)))))))))).
  pose (tail := fun _ : nat => foam_empty V M).
  pose proof (foam_induction_schema V M phi
    (scons V a (scons V f (scons V g tail)))) as hind.
  assert (hall : forall k,
    Sat V (foam_mem V M)
      (scons V k (scons V a (scons V f (scons V g tail)))) phi).
  {
    apply hind.
    intros k ih.
    unfold phi.
    simpl.
    intros r hkr hrSat hfSat hgSat y hySat u huSat.
    pose (Er := scons V r
      (scons V k (scons V a (scons V f (scons V g tail))))).
    pose (Ey := scons V y Er).
    pose (Eu := scons V u Ey).
    assert (hrOrd : OrdinalLike (foam_mem V M) r).
    {
      exact (proj1 (HF_ordinalLikeAt_spec V (foam_mem V M) Er 0)
        hrSat).
    }
    assert (hfApprox : foam_mul_rec_approx V M a f r).
    {
      pose proof (proj1 (foam_mulRecApproxAt_spec V M Er 3 2 0)
        hfSat) as h.
      change (foam_mul_rec_approx V M a f r) in h.
      exact h.
    }
    assert (hgApprox : foam_mul_rec_approx V M a g r).
    {
      pose proof (proj1 (foam_mulRecApproxAt_spec V M Er 4 2 0)
        hgSat) as h.
      change (foam_mul_rec_approx V M a g r) in h.
      exact h.
    }
    assert (hpairF : foam_mem V M (foam_kpair_obj V M k y) f).
    {
      pose proof (proj1 (foam_HF_pairMemAt_spec V M Ey 2 0 4)
        hySat) as h.
      change (foam_mem V M (foam_kpair_obj V M k y) f) in h.
      exact h.
    }
    assert (hpairG : foam_mem V M (foam_kpair_obj V M k u) g).
    {
      pose proof (proj1 (foam_HF_pairMemAt_spec V M Eu 3 0 6)
        huSat) as h.
      change (foam_mem V M (foam_kpair_obj V M k u) g) in h.
      exact h.
    }
    assert (hkOrd : OrdinalLike (foam_mem V M) k).
    {
      destruct hkr as [hkr | hkr].
      - exact (OrdinalLike_of_mem V (foam_mem V M) r k hrOrd hkr).
      - subst k. exact hrOrd.
    }
    destruct (fofam_OrdinalLike_empty_or_succ V M k hkOrd) as
      [hkEmpty | [p [hpk hkSucc]]].
    - destruct hfApprox as [hfunF [_hkeysF [hbaseF [_htotalF _hstepF]]]].
      destruct hgApprox as [hfunG [_hkeysG [hbaseG [_htotalG _hstepG]]]].
      assert (hpairEmptyF : foam_mem V M
        (foam_kpair_obj V M (foam_empty V M) y) f).
      { rewrite <- hkEmpty. exact hpairF. }
      assert (hpairEmptyG : foam_mem V M
        (foam_kpair_obj V M (foam_empty V M) u) g).
      { rewrite <- hkEmpty. exact hpairG. }
      pose proof (hfunF (foam_empty V M) y (foam_empty V M)
        hpairEmptyF hbaseF) as hy.
      pose proof (hfunG (foam_empty V M) u (foam_empty V M)
        hpairEmptyG hbaseG) as hu.
      exact (eq_trans hy (eq_sym hu)).
    - destruct hfApprox as
        [_hfunF [_hkeysF [_hbaseF [htotalF hstepF]]]].
      destruct hgApprox as
        [_hfunG [_hkeysG [_hbaseG [htotalG hstepG]]]].
      assert (hpr : foam_mem V M p r).
      {
        destruct hkr as [hkr | hkr].
        - exact (proj1 hrOrd k hkr p hpk).
        - subst k. exact hpk.
      }
      destruct (htotalF p (or_introl hpr)) as [t hpt].
      destruct (htotalG p (or_introl hpr)) as [v hpv].
      assert (hpSat : Sat V (foam_mem V M)
        (scons V p (scons V a (scons V f (scons V g tail)))) phi).
      {
        exact (proj1 (Sat_rename_rSkipParam V (foam_mem V M)
          phi (scons V a (scons V f (scons V g tail))) k p)
          (ih p hpk)).
      }
      pose (Erp := scons V r
        (scons V p (scons V a (scons V f (scons V g tail))))).
      pose (Etp := scons V t Erp).
      pose (Ev := scons V v Etp).
      assert (hrSatP : Sat V (foam_mem V M) Erp
        (HF_ordinalLikeAt 0)).
      {
        apply (proj2 (HF_ordinalLikeAt_spec V (foam_mem V M) Erp 0)).
        exact hrOrd.
      }
      assert (hfSatP : Sat V (foam_mem V M) Erp
        (mulRecApproxAt 3 2 0)).
      {
        apply (proj2 (foam_mulRecApproxAt_spec V M Erp 3 2 0)).
        change (foam_mul_rec_approx V M a f r).
        repeat split; assumption.
      }
      assert (hgSatP : Sat V (foam_mem V M) Erp
        (mulRecApproxAt 4 2 0)).
      {
        apply (proj2 (foam_mulRecApproxAt_spec V M Erp 4 2 0)).
        change (foam_mul_rec_approx V M a g r).
        repeat split; assumption.
      }
      assert (hptSat : Sat V (foam_mem V M) Etp
        (HF_pairMemAt 2 0 4)).
      {
        apply (proj2 (foam_HF_pairMemAt_spec V M Etp 2 0 4)).
        change (foam_mem V M (foam_kpair_obj V M p t) f).
        exact hpt.
      }
      assert (hpvSat : Sat V (foam_mem V M) Ev
        (HF_pairMemAt 3 0 6)).
      {
        apply (proj2 (foam_HF_pairMemAt_spec V M Ev 3 0 6)).
        change (foam_mem V M (foam_kpair_obj V M p v) g).
        exact hpv.
      }
      pose proof (hpSat r (or_introl hpr) hrSatP hfSatP hgSatP
        t hptSat v hpvSat) as htv.
      change (t = v) in htv.
      assert (hpairSuccF : foam_mem V M
        (foam_kpair_obj V M (foam_adjoin V M p p) y) f).
      { rewrite <- hkSucc. exact hpairF. }
      assert (hpairSuccG : foam_mem V M
        (foam_kpair_obj V M (foam_adjoin V M p p) u) g).
      { rewrite <- hkSucc. exact hpairG. }
      destruct (hstepF p t y hpr hpt hpairSuccF)
        as [fAdd [hfAdd hyAdd]].
      destruct (hstepG p v u hpr hpv hpairSuccG)
        as [gAdd [hgAdd huAdd]].
      rewrite <- htv in hgAdd.
      exact (fofam_succ_rec_approx_value_unique
        V M t fAdd gAdd a y u ha hfAdd hyAdd hgAdd huAdd).
  }
  pose (Em := scons V m
    (scons V m (scons V a (scons V f (scons V g tail))))).
  pose (Ez := scons V z Em).
  pose (Ew := scons V w Ez).
  pose proof (hall m) as hmain.
  unfold phi in hmain.
  simpl in hmain.
  assert (hmSat : Sat V (foam_mem V M) Em (HF_ordinalLikeAt 0)).
  {
    apply (proj2 (HF_ordinalLikeAt_spec V (foam_mem V M) Em 0)).
    exact hm.
  }
  assert (hfSat : Sat V (foam_mem V M) Em (mulRecApproxAt 3 2 0)).
  {
    apply (proj2 (foam_mulRecApproxAt_spec V M Em 3 2 0)).
    change (foam_mul_rec_approx V M a f m).
    exact hf.
  }
  assert (hgSat : Sat V (foam_mem V M) Em (mulRecApproxAt 4 2 0)).
  {
    apply (proj2 (foam_mulRecApproxAt_spec V M Em 4 2 0)).
    change (foam_mul_rec_approx V M a g m).
    exact hg.
  }
  assert (hzSat : Sat V (foam_mem V M) Ez (HF_pairMemAt 2 0 4)).
  {
    apply (proj2 (foam_HF_pairMemAt_spec V M Ez 2 0 4)).
    change (foam_mem V M (foam_kpair_obj V M m z) f).
    exact hz.
  }
  assert (hwSat : Sat V (foam_mem V M) Ew (HF_pairMemAt 3 0 6)).
  {
    apply (proj2 (foam_HF_pairMemAt_spec V M Ew 3 0 6)).
    change (foam_mem V M (foam_kpair_obj V M m w) g).
    exact hw.
  }
  exact (hmain m (or_intror eq_refl) hmSat hfSat hgSat
    z hzSat w hwSat).
Qed.

Lemma addGraphAt_outputs_eq_finite_model :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V)
    (e1 e2 : nat -> V)
    out1 out2 left1 left2 right1 right2,
  e1 left1 = e2 left2 ->
  e1 right1 = e2 right2 ->
  OrdinalLike (foam_mem V M) (e1 right1) ->
  Sat V (foam_mem V M) e1 (addGraphAt out1 left1 right1) ->
  Sat V (foam_mem V M) e2 (addGraphAt out2 left2 right2) ->
  e1 out1 = e2 out2.
Proof.
  intros V M e1 e2 out1 out2 left1 left2 right1 right2
    hleft hright hrightOrd h1 h2.
  unfold addGraphAt in h1, h2.
  simpl in h1, h2.
  destruct h1 as [f [hfSat hout1Sat]].
  destruct h2 as [g [hgSat hout2Sat]].
  assert (hf : foam_succ_rec_approx V M
    (e1 left1) f (e1 right1)).
  {
    pose proof (proj1 (foam_HF_succRecApproxAt_spec V M
      (scons V f e1) 0 (S left1) (S right1)) hfSat) as h.
    change (foam_succ_rec_approx V M (e1 left1) f (e1 right1)) in h.
    exact h.
  }
  assert (hpair1 : foam_mem V M
    (foam_kpair_obj V M (e1 right1) (e1 out1)) f).
  {
    pose proof (proj1 (foam_HF_pairMemAt_spec V M
      (scons V f e1) (S right1) (S out1) 0) hout1Sat) as h.
    change (foam_mem V M
      (foam_kpair_obj V M (e1 right1) (e1 out1)) f) in h.
    exact h.
  }
  assert (hgRaw : foam_succ_rec_approx V M
    (e2 left2) g (e2 right2)).
  {
    pose proof (proj1 (foam_HF_succRecApproxAt_spec V M
      (scons V g e2) 0 (S left2) (S right2)) hgSat) as h.
    change (foam_succ_rec_approx V M (e2 left2) g (e2 right2)) in h.
    exact h.
  }
  assert (hg : foam_succ_rec_approx V M
    (e1 left1) g (e1 right1)).
  {
    rewrite hleft, hright.
    exact hgRaw.
  }
  assert (hpair2Raw : foam_mem V M
    (foam_kpair_obj V M (e2 right2) (e2 out2)) g).
  {
    pose proof (proj1 (foam_HF_pairMemAt_spec V M
      (scons V g e2) (S right2) (S out2) 0) hout2Sat) as h.
    change (foam_mem V M
      (foam_kpair_obj V M (e2 right2) (e2 out2)) g) in h.
    exact h.
  }
  assert (hpair2 : foam_mem V M
    (foam_kpair_obj V M (e1 right1) (e2 out2)) g).
  {
    rewrite hright.
    exact hpair2Raw.
  }
  exact (fofam_succ_rec_approx_value_unique
    V M (e1 left1) f g (e1 right1) (e1 out1) (e2 out2)
    hrightOrd hf hpair1 hg hpair2).
Qed.

Lemma mulGraphAt_outputs_eq_finite_model :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V)
    (e1 e2 : nat -> V)
    out1 out2 left1 left2 right1 right2,
  e1 left1 = e2 left2 ->
  e1 right1 = e2 right2 ->
  OrdinalLike (foam_mem V M) (e1 left1) ->
  OrdinalLike (foam_mem V M) (e1 right1) ->
  Sat V (foam_mem V M) e1 (mulGraphAt out1 left1 right1) ->
  Sat V (foam_mem V M) e2 (mulGraphAt out2 left2 right2) ->
  e1 out1 = e2 out2.
Proof.
  intros V M e1 e2 out1 out2 left1 left2 right1 right2
    hleft hright hleftOrd hrightOrd h1 h2.
  unfold mulGraphAt in h1, h2.
  simpl in h1, h2.
  destruct h1 as [f [hfSat hout1Sat]].
  destruct h2 as [g [hgSat hout2Sat]].
  assert (hf : foam_mul_rec_approx V M
    (e1 left1) f (e1 right1)).
  {
    pose proof (proj1 (foam_mulRecApproxAt_spec V M
      (scons V f e1) 0 (S left1) (S right1)) hfSat) as h.
    change (foam_mul_rec_approx V M (e1 left1) f (e1 right1)) in h.
    exact h.
  }
  assert (hpair1 : foam_mem V M
    (foam_kpair_obj V M (e1 right1) (e1 out1)) f).
  {
    pose proof (proj1 (foam_HF_pairMemAt_spec V M
      (scons V f e1) (S right1) (S out1) 0) hout1Sat) as h.
    change (foam_mem V M
      (foam_kpair_obj V M (e1 right1) (e1 out1)) f) in h.
    exact h.
  }
  assert (hgRaw : foam_mul_rec_approx V M
    (e2 left2) g (e2 right2)).
  {
    pose proof (proj1 (foam_mulRecApproxAt_spec V M
      (scons V g e2) 0 (S left2) (S right2)) hgSat) as h.
    change (foam_mul_rec_approx V M (e2 left2) g (e2 right2)) in h.
    exact h.
  }
  assert (hg : foam_mul_rec_approx V M
    (e1 left1) g (e1 right1)).
  {
    rewrite hleft, hright.
    exact hgRaw.
  }
  assert (hpair2Raw : foam_mem V M
    (foam_kpair_obj V M (e2 right2) (e2 out2)) g).
  {
    pose proof (proj1 (foam_HF_pairMemAt_spec V M
      (scons V g e2) (S right2) (S out2) 0) hout2Sat) as h.
    change (foam_mem V M
      (foam_kpair_obj V M (e2 right2) (e2 out2)) g) in h.
    exact h.
  }
  assert (hpair2 : foam_mem V M
    (foam_kpair_obj V M (e1 right1) (e2 out2)) g).
  {
    rewrite hright.
    exact hpair2Raw.
  }
  exact (fofam_mul_rec_approx_value_unique
    V M (e1 left1) f g (e1 right1) (e1 out1) (e2 out2)
    hleftOrd hrightOrd hf hpair1 hg hpair2).
Qed.

Lemma addGraphAt_value_OrdinalLike_finite_model :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V)
    (e : nat -> V) out left right,
  OrdinalLike (foam_mem V M) (e left) ->
  OrdinalLike (foam_mem V M) (e right) ->
  Sat V (foam_mem V M) e (addGraphAt out left right) ->
  OrdinalLike (foam_mem V M) (e out).
Proof.
  intros V M e out left right hleft hright hgraph.
  unfold addGraphAt in hgraph.
  simpl in hgraph.
  destruct hgraph as [f [hfSat houtSat]].
  assert (hf : foam_succ_rec_approx V M (e left) f (e right)).
  {
    pose proof (proj1 (foam_HF_succRecApproxAt_spec V M
      (scons V f e) 0 (S left) (S right)) hfSat) as h.
    change (foam_succ_rec_approx V M (e left) f (e right)) in h.
    exact h.
  }
  assert (hout : foam_mem V M
    (foam_kpair_obj V M (e right) (e out)) f).
  {
    pose proof (proj1 (foam_HF_pairMemAt_spec V M
      (scons V f e) (S right) (S out) 0) houtSat) as h.
    change (foam_mem V M
      (foam_kpair_obj V M (e right) (e out)) f) in h.
    exact h.
  }
  exact (fofam_succ_rec_approx_value_OrdinalLike
    V M (e left) f (e right) (e out) hleft hright hf hout).
Qed.

Lemma mulGraphAt_value_OrdinalLike_finite_model :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V)
    (e : nat -> V) out left right,
  OrdinalLike (foam_mem V M) (e left) ->
  OrdinalLike (foam_mem V M) (e right) ->
  Sat V (foam_mem V M) e (mulGraphAt out left right) ->
  OrdinalLike (foam_mem V M) (e out).
Proof.
  intros V M e out left right hleft hright hgraph.
  unfold mulGraphAt in hgraph.
  simpl in hgraph.
  destruct hgraph as [f [hfSat houtSat]].
  assert (hf : foam_mul_rec_approx V M (e left) f (e right)).
  {
    pose proof (proj1 (foam_mulRecApproxAt_spec V M
      (scons V f e) 0 (S left) (S right)) hfSat) as h.
    change (foam_mul_rec_approx V M (e left) f (e right)) in h.
    exact h.
  }
  assert (hout : foam_mem V M
    (foam_kpair_obj V M (e right) (e out)) f).
  {
    pose proof (proj1 (foam_HF_pairMemAt_spec V M
      (scons V f e) (S right) (S out) 0) houtSat) as h.
    change (foam_mem V M
      (foam_kpair_obj V M (e right) (e out)) f) in h.
    exact h.
  }
  exact (fofam_mul_rec_approx_value_OrdinalLike
    V M (e left) f (e right) (e out) hleft hright hf hout).
Qed.

(* A single structural pass proves both functionality and closure of the
   first output; the public theorem below projects the requested equality. *)
Theorem termGraphAt_outputs_eq_and_OrdinalLike :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V)
    (t : PA.term) (rho1 rho2 : nat -> nat) out1 out2
    (e1 e2 : nat -> V),
  (forall n, PA.Term.Free n t -> e1 (rho1 n) = e2 (rho2 n)) ->
  (forall n, PA.Term.Free n t ->
    OrdinalLike (foam_mem V M) (e1 (rho1 n))) ->
  Sat V (foam_mem V M) e1 (termGraphAt rho1 out1 t) ->
  Sat V (foam_mem V M) e2 (termGraphAt rho2 out2 t) ->
  e1 out1 = e2 out2 /\ OrdinalLike (foam_mem V M) (e1 out1).
Proof.
  intros V M t.
  induction t as [n | | t IH | a IHa b IHb | a IHa b IHb];
    intros rho1 rho2 out1 out2 e1 e2 hvars hord h1 h2.
  - simpl in h1, h2.
    split.
    + exact (eq_trans h1 (eq_trans (hvars n eq_refl) (eq_sym h2))).
    + rewrite h1.
      exact (hord n eq_refl).
  - simpl in h1, h2.
    pose proof (proj1 (foam_HF_emptyAt_empty V M e1 out1) h1)
      as hout1.
    pose proof (proj1 (foam_HF_emptyAt_empty V M e2 out2) h2)
      as hout2.
    split.
    + exact (eq_trans hout1 (eq_sym hout2)).
    + rewrite hout1.
      apply foam_OrdinalLike_empty.
  - simpl in h1, h2.
    destruct h1 as [x1 [hx1Graph hs1Graph]].
    destruct h2 as [x2 [hx2Graph hs2Graph]].
    assert (hvars' : forall k, PA.Term.Free k t ->
      scons V x1 e1 (rho1 k + 1) =
      scons V x2 e2 (rho2 k + 1)).
    {
      intros k hk.
      replace (rho1 k + 1) with (S (rho1 k)) by lia.
      replace (rho2 k + 1) with (S (rho2 k)) by lia.
      simpl.
      exact (hvars k hk).
    }
    assert (hord' : forall k, PA.Term.Free k t ->
      OrdinalLike (foam_mem V M) (scons V x1 e1 (rho1 k + 1))).
    {
      intros k hk.
      replace (rho1 k + 1) with (S (rho1 k)) by lia.
      simpl.
      exact (hord k hk).
    }
    pose proof (IH (fun k => rho1 k + 1) (fun k => rho2 k + 1)
      0 0 (scons V x1 e1) (scons V x2 e2)
      hvars' hord' hx1Graph hx2Graph) as [hx hxOrd].
    change (x1 = x2) in hx.
    change (OrdinalLike (foam_mem V M) x1) in hxOrd.
    pose proof (proj1 (foam_HF_succAt_spec V M
      (scons V x1 e1) (out1 + 1) 0) hs1Graph) as hout1.
    pose proof (proj1 (foam_HF_succAt_spec V M
      (scons V x2 e2) (out2 + 1) 0) hs2Graph) as hout2.
    replace (out1 + 1) with (S out1) in hout1 by lia.
    replace (out2 + 1) with (S out2) in hout2 by lia.
    simpl in hout1, hout2.
    change (e1 out1 = foam_adjoin V M x1 x1) in hout1.
    change (e2 out2 = foam_adjoin V M x2 x2) in hout2.
    split.
    + rewrite hout1, hout2, hx. reflexivity.
    + rewrite hout1.
      exact (foam_OrdinalLike_adjoin_self V M x1
        (foam_adjoin V M x1 x1) hxOrd eq_refl).
  - simpl in h1, h2.
    destruct h1 as [x1 [y1 [ha1 [hb1 hadd1]]]].
    destruct h2 as [x2 [y2 [ha2 [hb2 hadd2]]]].
    set (E1 := scons V y1 (scons V x1 e1)).
    set (E2 := scons V y2 (scons V x2 e2)).
    assert (hvarsA : forall k, PA.Term.Free k a ->
      E1 (rho1 k + 2) = E2 (rho2 k + 2)).
    {
      intros k hk.
      unfold E1, E2.
      replace (rho1 k + 2) with (S (S (rho1 k))) by lia.
      replace (rho2 k + 2) with (S (S (rho2 k))) by lia.
      simpl.
      exact (hvars k (or_introl hk)).
    }
    assert (hordA : forall k, PA.Term.Free k a ->
      OrdinalLike (foam_mem V M) (E1 (rho1 k + 2))).
    {
      intros k hk.
      unfold E1.
      replace (rho1 k + 2) with (S (S (rho1 k))) by lia.
      simpl.
      exact (hord k (or_introl hk)).
    }
    pose proof (IHa (fun k => rho1 k + 2) (fun k => rho2 k + 2)
      1 1 E1 E2 hvarsA hordA ha1 ha2) as [hx hxOrd].
    assert (hvarsB : forall k, PA.Term.Free k b ->
      E1 (rho1 k + 2) = E2 (rho2 k + 2)).
    {
      intros k hk.
      unfold E1, E2.
      replace (rho1 k + 2) with (S (S (rho1 k))) by lia.
      replace (rho2 k + 2) with (S (S (rho2 k))) by lia.
      simpl.
      exact (hvars k (or_intror hk)).
    }
    assert (hordB : forall k, PA.Term.Free k b ->
      OrdinalLike (foam_mem V M) (E1 (rho1 k + 2))).
    {
      intros k hk.
      unfold E1.
      replace (rho1 k + 2) with (S (S (rho1 k))) by lia.
      simpl.
      exact (hord k (or_intror hk)).
    }
    pose proof (IHb (fun k => rho1 k + 2) (fun k => rho2 k + 2)
      0 0 E1 E2 hvarsB hordB hb1 hb2) as [hy hyOrd].
    pose proof (addGraphAt_outputs_eq_finite_model V M E1 E2
      (out1 + 2) (out2 + 2) 1 1 0 0 hx hy hyOrd hadd1 hadd2)
      as hout.
    pose proof (addGraphAt_value_OrdinalLike_finite_model V M E1
      (out1 + 2) 1 0 hxOrd hyOrd hadd1) as houtOrd.
    unfold E1, E2 in hout, houtOrd.
    replace (out1 + 2) with (S (S out1)) in hout by lia.
    replace (out2 + 2) with (S (S out2)) in hout by lia.
    replace (out1 + 2) with (S (S out1)) in houtOrd by lia.
    simpl in hout, houtOrd.
    split; assumption.
  - simpl in h1, h2.
    destruct h1 as [y1 [x1 [z1 [ha1 [hb1 [hcopy1 hmul1]]]]]].
    destruct h2 as [y2 [x2 [z2 [ha2 [hb2 [hcopy2 hmul2]]]]]].
    set (E1 := scons V z1 (scons V x1 (scons V y1 e1))).
    set (E2 := scons V z2 (scons V x2 (scons V y2 e2))).
    assert (hvarsA : forall k, PA.Term.Free k a ->
      E1 (rho1 k + 3) = E2 (rho2 k + 3)).
    {
      intros k hk.
      unfold E1, E2.
      replace (rho1 k + 3) with (S (S (S (rho1 k)))) by lia.
      replace (rho2 k + 3) with (S (S (S (rho2 k)))) by lia.
      simpl.
      exact (hvars k (or_introl hk)).
    }
    assert (hordA : forall k, PA.Term.Free k a ->
      OrdinalLike (foam_mem V M) (E1 (rho1 k + 3))).
    {
      intros k hk.
      unfold E1.
      replace (rho1 k + 3) with (S (S (S (rho1 k)))) by lia.
      simpl.
      exact (hord k (or_introl hk)).
    }
    pose proof (IHa (fun k => rho1 k + 3) (fun k => rho2 k + 3)
      1 1 E1 E2 hvarsA hordA ha1 ha2) as [hx hxOrd].
    assert (hvarsB : forall k, PA.Term.Free k b ->
      E1 (rho1 k + 3) = E2 (rho2 k + 3)).
    {
      intros k hk.
      unfold E1, E2.
      replace (rho1 k + 3) with (S (S (S (rho1 k)))) by lia.
      replace (rho2 k + 3) with (S (S (S (rho2 k)))) by lia.
      simpl.
      exact (hvars k (or_intror hk)).
    }
    assert (hordB : forall k, PA.Term.Free k b ->
      OrdinalLike (foam_mem V M) (E1 (rho1 k + 3))).
    {
      intros k hk.
      unfold E1.
      replace (rho1 k + 3) with (S (S (S (rho1 k)))) by lia.
      simpl.
      exact (hord k (or_intror hk)).
    }
    pose proof (IHb (fun k => rho1 k + 3) (fun k => rho2 k + 3)
      2 2 E1 E2 hvarsB hordB hb1 hb2) as [hy hyOrd].
    pose proof (mulGraphAt_outputs_eq_finite_model V M E1 E2
      0 0 1 1 2 2 hx hy hxOrd hyOrd hmul1 hmul2) as hz.
    pose proof (mulGraphAt_value_OrdinalLike_finite_model V M E1
      0 1 2 hxOrd hyOrd hmul1) as hzOrd.
    unfold E1, E2 in hz, hzOrd.
    simpl in hz, hzOrd.
    replace (out1 + 3) with (S (S (S out1))) in hcopy1 by lia.
    replace (out2 + 3) with (S (S (S out2))) in hcopy2 by lia.
    simpl in hcopy1, hcopy2.
    split.
    + exact (eq_trans (eq_sym hcopy1) (eq_trans hz hcopy2)).
    + rewrite <- hcopy1.
      exact hzOrd.
Qed.

Theorem termGraphAt_outputs_eq :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V)
    (t : PA.term) (rho1 rho2 : nat -> nat) out1 out2
    (e1 e2 : nat -> V),
  (forall n, PA.Term.Free n t -> e1 (rho1 n) = e2 (rho2 n)) ->
  (forall n, PA.Term.Free n t ->
    OrdinalLike (foam_mem V M) (e1 (rho1 n))) ->
  Sat V (foam_mem V M) e1 (termGraphAt rho1 out1 t) ->
  Sat V (foam_mem V M) e2 (termGraphAt rho2 out2 t) ->
  e1 out1 = e2 out2.
Proof.
  intros V M t rho1 rho2 out1 out2 e1 e2
    hvars hord h1 h2.
  exact (proj1 (termGraphAt_outputs_eq_and_OrdinalLike
    V M t rho1 rho2 out1 out2 e1 e2 hvars hord h1 h2)).
Qed.

(* Lean-facing compatibility name used by the semantic translation layer. *)
Theorem termGraphAt_outputs_eq_finite_model :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V)
    (t : PA.term) (rho1 rho2 : nat -> nat) out1 out2
    (e1 e2 : nat -> V),
  (forall n, PA.Term.Free n t -> e1 (rho1 n) = e2 (rho2 n)) ->
  (forall n, PA.Term.Free n t ->
    OrdinalLike (foam_mem V M) (e1 (rho1 n))) ->
  Sat V (foam_mem V M) e1 (termGraphAt rho1 out1 t) ->
  Sat V (foam_mem V M) e2 (termGraphAt rho2 out2 t) ->
  e1 out1 = e2 out2.
Proof.
  exact termGraphAt_outputs_eq.
Qed.
