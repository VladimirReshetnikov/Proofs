(* ===================================================================== *)
(*  PAHFTermGraphTotal.v                                                *)
(*                                                                       *)
(*  Semantic totality of translated PA term graphs in arbitrary finite  *)
(*  HF models.  The only non-structural point is that the recursion       *)
(*  traces used for addition and multiplication stay inside the          *)
(*  ordinal-like part of the model.                                      *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Lia List.
From FirstOrder Require Import Fol Calculus Completeness.
From PAHF Require Import PAHF PAHFInterpretations
  PAHFTermGraphModel.

Import ListNotations.

(* Every value read from a successor-recursion trace over an ordinal key is
   ordinal-like when the trace's base value is ordinal-like. *)
Lemma fofam_succ_rec_approx_value_OrdinalLike :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V)
    (s f m z : V),
  OrdinalLike (foam_mem V M) s ->
  OrdinalLike (foam_mem V M) m ->
  foam_succ_rec_approx V M s f m ->
  foam_mem V M (foam_kpair_obj V M m z) f ->
  OrdinalLike (foam_mem V M) z.
Proof.
  intros V M s f m z hs hm hf hz.
  pose (phi :=
    fAll
      (fImp (fOr (fMem 1 0) (fEq 1 0))
        (fImp (HF_ordinalLikeAt 0)
          (fImp (HF_succRecApproxAt 3 2 0)
            (fAll
              (fImp (HF_pairMemAt 2 0 4)
                (HF_ordinalLikeAt 0))))))).
  pose (tail := fun _ : nat => foam_empty V M).
  pose proof (foam_induction_schema V M phi
    (scons V s (scons V f tail))) as hind.
  assert (hall : forall k,
      Sat V (foam_mem V M)
        (scons V k (scons V s (scons V f tail))) phi).
  {
    apply hind.
    intros k ih.
    unfold phi.
    simpl.
    intros r hkr hrSat hfSat y hpairSat.
    pose (Er := scons V r (scons V k (scons V s (scons V f tail)))).
    pose (Ey := scons V y Er).
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
    assert (hpair : foam_mem V M (foam_kpair_obj V M k y) f).
    {
      pose proof (proj1 (foam_HF_pairMemAt_spec V M Ey 2 0 4)
        hpairSat) as h.
      change (foam_mem V M (foam_kpair_obj V M k y) f) in h.
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
    - destruct hfApprox as [hfun [_hkeys [hbase [_htotal _hstep]]]].
      assert (hpairEmpty :
          foam_mem V M
            (foam_kpair_obj V M (foam_empty V M) y) f).
      {
        rewrite <- hkEmpty.
        exact hpair.
      }
      assert (hy : y = s).
      {
        exact (hfun (foam_empty V M) y s hpairEmpty hbase).
      }
      rewrite hy.
      exact hs.
    - destruct hfApprox as
        [hfun [hkeys [hbase [htotal hstep]]]].
      assert (hpr : foam_mem V M p r).
      {
        destruct hkr as [hkr | hkr].
        - exact (proj1 hrOrd k hkr p hpk).
        - subst k. exact hpk.
      }
      destruct (htotal p (or_introl hpr)) as [t hpt].
      assert (hpSat :
          Sat V (foam_mem V M)
            (scons V p (scons V s (scons V f tail))) phi).
      {
        exact (proj1 (Sat_rename_rSkipParam V (foam_mem V M)
          phi (scons V s (scons V f tail)) k p) (ih p hpk)).
      }
      pose (Erp :=
        scons V r (scons V p (scons V s (scons V f tail)))).
      pose (Etp := scons V t Erp).
      assert (hrSatP :
          Sat V (foam_mem V M) Erp (HF_ordinalLikeAt 0)).
      {
        apply (proj2 (HF_ordinalLikeAt_spec V (foam_mem V M) Erp 0)).
        exact hrOrd.
      }
      assert (hfSatP :
          Sat V (foam_mem V M) Erp (HF_succRecApproxAt 3 2 0)).
      {
        apply (proj2 (foam_HF_succRecApproxAt_spec V M Erp 3 2 0)).
        change (foam_succ_rec_approx V M s f r).
        repeat split; assumption.
      }
      assert (hptSat :
          Sat V (foam_mem V M) Etp (HF_pairMemAt 2 0 4)).
      {
        apply (proj2 (foam_HF_pairMemAt_spec V M Etp 2 0 4)).
        change (foam_mem V M (foam_kpair_obj V M p t) f).
        exact hpt.
      }
      assert (htDomain :
          Sat V (foam_mem V M) Etp (HF_ordinalLikeAt 0)).
      {
        unfold phi in hpSat.
        simpl in hpSat.
        exact (hpSat r (or_introl hpr) hrSatP hfSatP t hptSat).
      }
      assert (htOrd : OrdinalLike (foam_mem V M) t).
      {
        exact (proj1 (HF_ordinalLikeAt_spec V (foam_mem V M) Etp 0)
          htDomain).
      }
      assert (hpairSucc :
          foam_mem V M
            (foam_kpair_obj V M (foam_adjoin V M p p) y) f).
      {
        rewrite <- hkSucc.
        exact hpair.
      }
      assert (hy : y = foam_adjoin V M t t).
      {
        exact (hstep p t y hpr hpt hpairSucc).
      }
      exact (foam_OrdinalLike_adjoin_self V M t y htOrd hy).
  }
  pose (Em := scons V m (scons V m (scons V s (scons V f tail)))).
  pose (Ez := scons V z Em).
  pose proof (hall m) as hmain.
  unfold phi in hmain.
  simpl in hmain.
  assert (hmSat : Sat V (foam_mem V M) Em (HF_ordinalLikeAt 0)).
  {
    apply (proj2 (HF_ordinalLikeAt_spec V (foam_mem V M) Em 0)).
    exact hm.
  }
  assert (hfSat :
      Sat V (foam_mem V M) Em (HF_succRecApproxAt 3 2 0)).
  {
    apply (proj2 (foam_HF_succRecApproxAt_spec V M Em 3 2 0)).
    change (foam_succ_rec_approx V M s f m).
    exact hf.
  }
  assert (hzSat : Sat V (foam_mem V M) Ez (HF_pairMemAt 2 0 4)).
  {
    apply (proj2 (foam_HF_pairMemAt_spec V M Ez 2 0 4)).
    change (foam_mem V M (foam_kpair_obj V M m z) f).
    exact hz.
  }
  pose proof (hmain m (or_intror eq_refl) hmSat hfSat z hzSat) as hzOrd.
  exact (proj1 (HF_ordinalLikeAt_spec V (foam_mem V M) Ez 0) hzOrd).
Qed.

(* Multiplication traces are ordinal-closed as well.  At a successor key the
   multiplication step exposes an addition trace, so the preceding theorem
   supplies the only closure argument needed here. *)
Lemma fofam_mul_rec_approx_value_OrdinalLike :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V)
    (a f m z : V),
  OrdinalLike (foam_mem V M) a ->
  OrdinalLike (foam_mem V M) m ->
  foam_mul_rec_approx V M a f m ->
  foam_mem V M (foam_kpair_obj V M m z) f ->
  OrdinalLike (foam_mem V M) z.
Proof.
  intros V M a f m z ha hm hf hz.
  pose (phi :=
    fAll
      (fImp (fOr (fMem 1 0) (fEq 1 0))
        (fImp (HF_ordinalLikeAt 0)
          (fImp (mulRecApproxAt 3 2 0)
            (fAll
              (fImp (HF_pairMemAt 2 0 4)
                (HF_ordinalLikeAt 0))))))).
  pose (tail := fun _ : nat => foam_empty V M).
  pose proof (foam_induction_schema V M phi
    (scons V a (scons V f tail))) as hind.
  assert (hall : forall k,
      Sat V (foam_mem V M)
        (scons V k (scons V a (scons V f tail))) phi).
  {
    apply hind.
    intros k ih.
    unfold phi.
    simpl.
    intros r hkr hrSat hfSat y hpairSat.
    pose (Er := scons V r (scons V k (scons V a (scons V f tail)))).
    pose (Ey := scons V y Er).
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
    assert (hpair : foam_mem V M (foam_kpair_obj V M k y) f).
    {
      pose proof (proj1 (foam_HF_pairMemAt_spec V M Ey 2 0 4)
        hpairSat) as h.
      change (foam_mem V M (foam_kpair_obj V M k y) f) in h.
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
    - destruct hfApprox as [hfun [_hkeys [hbase [_htotal _hstep]]]].
      assert (hpairEmpty :
          foam_mem V M
            (foam_kpair_obj V M (foam_empty V M) y) f).
      {
        rewrite <- hkEmpty.
        exact hpair.
      }
      assert (hy : y = foam_empty V M).
      {
        exact (hfun (foam_empty V M) y (foam_empty V M)
          hpairEmpty hbase).
      }
      rewrite hy.
      exact (foam_OrdinalLike_empty V M).
    - destruct hfApprox as
        [hfun [hkeys [hbase [htotal hstep]]]].
      assert (hpr : foam_mem V M p r).
      {
        destruct hkr as [hkr | hkr].
        - exact (proj1 hrOrd k hkr p hpk).
        - subst k. exact hpk.
      }
      destruct (htotal p (or_introl hpr)) as [t hpt].
      assert (hpSat :
          Sat V (foam_mem V M)
            (scons V p (scons V a (scons V f tail))) phi).
      {
        exact (proj1 (Sat_rename_rSkipParam V (foam_mem V M)
          phi (scons V a (scons V f tail)) k p) (ih p hpk)).
      }
      pose (Erp :=
        scons V r (scons V p (scons V a (scons V f tail)))).
      pose (Etp := scons V t Erp).
      assert (hrSatP :
          Sat V (foam_mem V M) Erp (HF_ordinalLikeAt 0)).
      {
        apply (proj2 (HF_ordinalLikeAt_spec V (foam_mem V M) Erp 0)).
        exact hrOrd.
      }
      assert (hfSatP :
          Sat V (foam_mem V M) Erp (mulRecApproxAt 3 2 0)).
      {
        apply (proj2 (foam_mulRecApproxAt_spec V M Erp 3 2 0)).
        change (foam_mul_rec_approx V M a f r).
        repeat split; assumption.
      }
      assert (hptSat :
          Sat V (foam_mem V M) Etp (HF_pairMemAt 2 0 4)).
      {
        apply (proj2 (foam_HF_pairMemAt_spec V M Etp 2 0 4)).
        change (foam_mem V M (foam_kpair_obj V M p t) f).
        exact hpt.
      }
      assert (htDomain :
          Sat V (foam_mem V M) Etp (HF_ordinalLikeAt 0)).
      {
        unfold phi in hpSat.
        simpl in hpSat.
        exact (hpSat r (or_introl hpr) hrSatP hfSatP t hptSat).
      }
      assert (htOrd : OrdinalLike (foam_mem V M) t).
      {
        exact (proj1 (HF_ordinalLikeAt_spec V (foam_mem V M) Etp 0)
          htDomain).
      }
      assert (hpairSucc :
          foam_mem V M
            (foam_kpair_obj V M (foam_adjoin V M p p) y) f).
      {
        rewrite <- hkSucc.
        exact hpair.
      }
      destruct (hstep p t y hpr hpt hpairSucc) as
        [g [hgApprox hgy]].
      exact (fofam_succ_rec_approx_value_OrdinalLike
        V M t g a y htOrd ha hgApprox hgy).
  }
  pose (Em := scons V m (scons V m (scons V a (scons V f tail)))).
  pose (Ez := scons V z Em).
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
  assert (hzSat : Sat V (foam_mem V M) Ez (HF_pairMemAt 2 0 4)).
  {
    apply (proj2 (foam_HF_pairMemAt_spec V M Ez 2 0 4)).
    change (foam_mem V M (foam_kpair_obj V M m z) f).
    exact hz.
  }
  pose proof (hmain m (or_intror eq_refl) hmSat hfSat z hzSat) as hzOrd.
  exact (proj1 (HF_ordinalLikeAt_spec V (foam_mem V M) Ez 0) hzOrd).
Qed.

(* A PA term is evaluated relationally: its value is placed in a fresh head
   slot, is ordinal-like, and satisfies the corresponding graph formula. *)
Theorem termGraphAt_total_of_OrdinalLike :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V)
    (t : PA.term) (rho : nat -> nat) (e : nat -> V),
  (forall n, PA.Term.Free n t ->
    OrdinalLike (foam_mem V M) (e (rho n))) ->
  exists x,
    OrdinalLike (foam_mem V M) x /\
    Sat V (foam_mem V M) (scons V x e)
      (termGraphAt (fun n => S (rho n)) 0 t).
Proof.
  intros V M t.
  induction t as [n | | t IH | a IHa b IHb | a IHa b IHb];
    intros rho e hfree.
  - exists (e (rho n)).
    split.
    + apply hfree. reflexivity.
    + simpl.
      reflexivity.
  - exists (foam_empty V M).
    split.
    + apply foam_OrdinalLike_empty.
    + simpl.
      apply (proj2 (foam_HF_emptyAt_empty V M
        (scons V (foam_empty V M) e) 0)).
      reflexivity.
  - destruct (IH rho e hfree) as [x [hxOrd hxGraph]].
    pose (sx := foam_adjoin V M x x).
    exists sx.
    split.
    + apply (foam_OrdinalLike_adjoin_self V M x sx hxOrd).
      reflexivity.
    + simpl.
      exists x.
      split.
      * assert (hinsert :
          Sat V (foam_mem V M) (scons V x (scons V sx e))
            (termGraphAt (fun n => S (S (rho n))) 0 t)).
        {
          exact (Sat_termGraphAt_insert_after_output
            V (foam_mem V M) t rho e x sx hxGraph).
        }
        replace (termGraphAt (fun n => S (rho n + 1)) 0 t)
          with (termGraphAt (fun n => S (S (rho n))) 0 t).
        -- exact hinsert.
        -- apply termGraphAt_map_ext.
           intro k. lia.
      * apply (proj2 (foam_HF_succAt_spec V M
          (scons V x (scons V sx e)) 1 0)).
        change (sx = foam_adjoin V M x x).
        reflexivity.
  - destruct (IHa rho e (fun n hn => hfree n (or_introl hn))) as
      [x [hxOrd hxGraph]].
    destruct (IHb rho e (fun n hn => hfree n (or_intror hn))) as
      [y [hyOrd hyGraph]].
    destruct (fofam_succ_rec_total_of_ordinalLike V M x y hyOrd) as
      [f [z [hf hz]]].
    assert (hzOrd : OrdinalLike (foam_mem V M) z).
    {
      exact (fofam_succ_rec_approx_value_OrdinalLike
        V M x f y z hxOrd hyOrd hf hz).
    }
    pose (E := scons V y (scons V x (scons V z e))).
    assert (hxGraphE :
        Sat V (foam_mem V M) E
          (termGraphAt (fun n => S (rho n) + 2) 1 a)).
    {
      assert (h1 :
          Sat V (foam_mem V M) (scons V x (scons V z e))
            (termGraphAt (fun n => S (S (rho n))) 0 a)).
      {
        exact (Sat_termGraphAt_insert_after_output
          V (foam_mem V M) a rho e x z hxGraph).
      }
      pose proof (Sat_termGraphAt_shift_front
        V (foam_mem V M) a (fun n => S (S (rho n))) 0
        (scons V x (scons V z e)) y h1) as h2.
      unfold E.
      rewrite (termGraphAt_map_ext a
        (fun n => S (rho n) + 2)
        (fun n => S (S (S (rho n)))) 1).
      - exact h2.
      - intro k. lia.
    }
    assert (hyGraphE :
        Sat V (foam_mem V M) E
          (termGraphAt (fun n => S (rho n) + 2) 0 b)).
    {
      assert (h1 :
          Sat V (foam_mem V M) (scons V y (scons V z e))
            (termGraphAt (fun n => S (S (rho n))) 0 b)).
      {
        exact (Sat_termGraphAt_insert_after_output
          V (foam_mem V M) b rho e y z hyGraph).
      }
      pose proof (Sat_termGraphAt_insert_after_output
        V (foam_mem V M) b (fun n => S (rho n))
        (scons V z e) y x h1) as h2.
      unfold E.
      rewrite (termGraphAt_map_ext b
        (fun n => S (rho n) + 2)
        (fun n => S (S (S (rho n)))) 0).
      - exact h2.
      - intro k. lia.
    }
    exists z.
    split; [exact hzOrd |].
    simpl.
    exists x, y.
    repeat split.
    + exact hxGraphE.
    + exact hyGraphE.
    + apply (addGraphAt_of_succRecApprox_model V M E 2 1 0 f).
      * change (foam_succ_rec_approx V M x f y).
        exact hf.
      * change (foam_mem V M (foam_kpair_obj V M y z) f).
        exact hz.
  - destruct (IHa rho e (fun n hn => hfree n (or_introl hn))) as
      [x [hxOrd hxGraph]].
    destruct (IHb rho e (fun n hn => hfree n (or_intror hn))) as
      [y [hyOrd hyGraph]].
    destruct (fofam_mul_rec_total_of_ordinalLike V M x y hxOrd hyOrd) as
      [f [z [hf hz]]].
    assert (hzOrd : OrdinalLike (foam_mem V M) z).
    {
      exact (fofam_mul_rec_approx_value_OrdinalLike
        V M x f y z hxOrd hyOrd hf hz).
    }
    pose (E := scons V z (scons V x (scons V y (scons V z e)))).
    assert (hxGraphE :
        Sat V (foam_mem V M) E
          (termGraphAt (fun n => S (rho n) + 3) 1 a)).
    {
      assert (h1 :
          Sat V (foam_mem V M) (scons V x (scons V z e))
            (termGraphAt (fun n => S (S (rho n))) 0 a)).
      {
        exact (Sat_termGraphAt_insert_after_output
          V (foam_mem V M) a rho e x z hxGraph).
      }
      pose proof (Sat_termGraphAt_insert_after_output
        V (foam_mem V M) a (fun n => S (rho n))
        (scons V z e) x y h1) as h2.
      pose proof (Sat_termGraphAt_shift_front
        V (foam_mem V M) a (fun n => S (S (S (rho n)))) 0
        (scons V x (scons V y (scons V z e))) z h2) as h3.
      unfold E.
      rewrite (termGraphAt_map_ext a
        (fun n => S (rho n) + 3)
        (fun n => S (S (S (S (rho n))))) 1).
      - exact h3.
      - intro k. lia.
    }
    assert (hyGraphE :
        Sat V (foam_mem V M) E
          (termGraphAt (fun n => S (rho n) + 3) 2 b)).
    {
      assert (h1 :
          Sat V (foam_mem V M) (scons V y (scons V z e))
            (termGraphAt (fun n => S (S (rho n))) 0 b)).
      {
        exact (Sat_termGraphAt_insert_after_output
          V (foam_mem V M) b rho e y z hyGraph).
      }
      pose proof (Sat_termGraphAt_shift_front
        V (foam_mem V M) b (fun n => S (S (rho n))) 0
        (scons V y (scons V z e)) x h1) as h2.
      pose proof (Sat_termGraphAt_shift_front
        V (foam_mem V M) b (fun n => S (S (S (rho n)))) 1
        (scons V x (scons V y (scons V z e))) z h2) as h3.
      unfold E.
      rewrite (termGraphAt_map_ext b
        (fun n => S (rho n) + 3)
        (fun n => S (S (S (S (rho n))))) 2).
      - exact h3.
      - intro k. lia.
    }
    exists z.
    split; [exact hzOrd |].
    simpl.
    exists y, x, z.
    repeat split.
    + exact hxGraphE.
    + exact hyGraphE.
    + apply (mulGraphAt_of_mulRecApprox_model V M E 0 1 2 f).
      * change (foam_mul_rec_approx V M x f y).
        exact hf.
      * change (foam_mem V M (foam_kpair_obj V M y z) f).
        exact hz.
Qed.

Lemma formulaAt_eqRefl_valid_of_HFFinAx_s_domainContext :
  forall (V : Type) (mem : V -> V -> Prop) (v : nat -> V),
  (forall g, HFFinAx_s g -> Sat V mem v g) ->
  forall rho t (e : nat -> V),
  (forall g, In g (domainContextAt rho (PA.Term.bound t)) ->
    Sat V mem e g) ->
  Sat V mem e (formulaAt rho (PA.pEq t t)).
Proof.
  intros V mem v hHF rho t e hctx.
  pose (M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s V mem v hHF).
  change (Sat V (foam_mem V M) e (formulaAt rho (PA.pEq t t))).
  assert (hfree : forall n, PA.Term.Free n t ->
      OrdinalLike (foam_mem V M) (e (rho n))).
  {
    intros n hn.
    apply (Sat_domainContextAt_ordinalLike V (foam_mem V M)
      rho (PA.Term.bound t) e hctx n).
    exact (PA.Term.free_lt_bound t n hn).
  }
  destruct (termGraphAt_total_of_OrdinalLike V M t rho e hfree) as
    [x [_hxOrd hxGraph]].
  pose (E := scons V x (scons V x e)).
  assert (hxLeft : Sat V (foam_mem V M) E
      (termGraphAt (fun n => rho n + 2) 1 t)).
  {
    pose proof (Sat_termGraphAt_shift_front V (foam_mem V M)
      t (fun n => S (rho n)) 0 (scons V x e) x hxGraph) as h.
    unfold E.
    rewrite (termGraphAt_map_ext t
      (fun n => rho n + 2) (fun n => S (S (rho n))) 1).
    - exact h.
    - intro n. lia.
  }
  assert (hxRight : Sat V (foam_mem V M) E
      (termGraphAt (fun n => rho n + 2) 0 t)).
  {
    pose proof (Sat_termGraphAt_insert_after_output V (foam_mem V M)
      t rho e x x hxGraph) as h.
    unfold E.
    rewrite (termGraphAt_map_ext t
      (fun n => rho n + 2) (fun n => S (S (rho n))) 0).
    - exact h.
    - intro n. lia.
  }
  simpl.
  exists x, x.
  repeat split; assumption.
Qed.

Lemma termGraphAt_exists_valid_of_HFFinAx_s_domainContext :
  forall (V : Type) (mem : V -> V -> Prop) (v : nat -> V),
  (forall g, HFFinAx_s g -> Sat V mem v g) ->
  forall rho t (e : nat -> V),
  (forall g, In g (domainContextAt rho (PA.Term.bound t)) ->
    Sat V mem e g) ->
  Sat V mem e
    (fEx (fAnd domainForm
      (termGraphAt (fun n => rho n + 1) 0 t))).
Proof.
  intros V mem v hHF rho t e hctx.
  pose (M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s V mem v hHF).
  change (Sat V (foam_mem V M) e
    (fEx (fAnd domainForm
      (termGraphAt (fun n => rho n + 1) 0 t)))).
  assert (hfree : forall n, PA.Term.Free n t ->
      OrdinalLike (foam_mem V M) (e (rho n))).
  {
    intros n hn.
    apply (Sat_domainContextAt_ordinalLike V (foam_mem V M)
      rho (PA.Term.bound t) e hctx n).
    exact (PA.Term.free_lt_bound t n hn).
  }
  destruct (termGraphAt_total_of_OrdinalLike V M t rho e hfree) as
    [x [hxOrd hxGraph]].
  exists x.
  split.
  - apply (proj2 (HF_ordinalLikeAt_spec V (foam_mem V M)
      (scons V x e) 0)).
    exact hxOrd.
  - replace (termGraphAt (fun n => rho n + 1) 0 t)
      with (termGraphAt (fun n => S (rho n)) 0 t).
    + exact hxGraph.
    + apply termGraphAt_map_ext.
      intro n. lia.
Qed.

Theorem BProv_HFFin_formulaAt_eqRefl_domainContext :
  forall G rho t,
  BProv HFFinAx_s (domainContextAt rho (PA.Term.bound t) ++ G)
    (formulaAt rho (PA.pEq t t)).
Proof.
  intros G rho t.
  apply completeness_inf_context.
  - exact Sentences_HFFin.
  - intros V mem v hHF hctx.
    apply (formulaAt_eqRefl_valid_of_HFFinAx_s_domainContext
      V mem v hHF rho t v).
    intros g hg.
    apply hctx.
    apply in_app_iff. now left.
Qed.

Theorem BProv_HFFin_termGraphAt_exists_domainContext :
  forall G rho t,
  BProv HFFinAx_s (domainContextAt rho (PA.Term.bound t) ++ G)
    (fEx (fAnd domainForm
      (termGraphAt (fun n => rho n + 1) 0 t))).
Proof.
  intros G rho t.
  apply completeness_inf_context.
  - exact Sentences_HFFin.
  - intros V mem v hHF hctx.
    apply (termGraphAt_exists_valid_of_HFFinAx_s_domainContext
      V mem v hHF rho t v).
    intros g hg.
    apply hctx.
    apply in_app_iff. now left.
Qed.
