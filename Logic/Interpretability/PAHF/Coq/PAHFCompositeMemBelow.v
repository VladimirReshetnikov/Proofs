(* ===================================================================== *)
(*  PAHFCompositeMemBelow.v                                              *)
(*                                                                       *)
(*  Arithmetic boundedness of translated Ackermann membership in an      *)
(*  arbitrary finite-HF model.  PA supplies hfMem -> lt; ordinal          *)
(*  successor-recursion semantics turns translated lt into ambient HF     *)
(*  membership.                                                          *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Lia List.
From FirstOrder Require Import Fol Calculus.
From PAHF Require Import PAHF PAHFInterpretations
  PAHFTranslatedHFFin PAHFMembershipBound PAHFMembershipBoundSucc
  PAHFMembershipTail
  PAHFHFRoundTrip PAHFHFRepresentationFinite PAHFDeductiveAssembly
  PAHFHFRepresentationRange.
Import ListNotations.

(* A value occurring in a successor-recursion trace is the base at zero
   and contains the base at every positive ordinal key. *)
Lemma fofam_succ_rec_approx_value_eq_or_base_mem :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V)
    s f m k z,
  OrdinalLike (foam_mem V M) m ->
  foam_succ_rec_approx V M s f m ->
  (foam_mem V M k m \/ k = m) ->
  foam_mem V M (foam_kpair_obj V M k z) f ->
    z = s \/ foam_mem V M s z.
Proof.
  intros V M s f m k z hm hf hk hz.
  pose (phi :=
    fAll
      (fImp (fOr (fMem 1 0) (fEq 1 0))
        (fImp (HF_ordinalLikeAt 0)
          (fImp (HF_succRecApproxAt 3 2 0)
            (fAll
              (fImp (HF_pairMemAt 2 0 4)
                (fOr (fEq 0 3) (fMem 3 0)))))))).
  pose (tail := fun _ : nat => foam_empty V M).
  pose proof (foam_induction_schema V M phi
    (scons V s (scons V f tail))) as hind.
  assert (hall : forall key,
      Sat V (foam_mem V M)
        (scons V key (scons V s (scons V f tail))) phi).
  {
    apply hind.
    intros key ih.
    unfold phi. simpl.
    intros bound hkey hboundSat hfSat value hpairSat.
    pose (Ebound := scons V bound
      (scons V key (scons V s (scons V f tail)))).
    pose (Evalue := scons V value Ebound).
    assert (hboundOrd : OrdinalLike (foam_mem V M) bound).
    {
      apply (proj1 (HF_ordinalLikeAt_spec V (foam_mem V M)
        Ebound 0)).
      exact hboundSat.
    }
    assert (hfApprox : foam_succ_rec_approx V M s f bound).
    {
      apply (proj1 (foam_HF_succRecApproxAt_spec V M Ebound 3 2 0)).
      exact hfSat.
    }
    assert (hpair :
        foam_mem V M (foam_kpair_obj V M key value) f).
    {
      apply (proj1 (foam_HF_pairMemAt_spec V M Evalue 2 0 4)).
      exact hpairSat.
    }
    assert (hkeyOrd : OrdinalLike (foam_mem V M) key).
    {
      destruct hkey as [hkey | hkey].
      - exact (OrdinalLike_of_mem V (foam_mem V M)
          bound key hboundOrd hkey).
      - subst key. exact hboundOrd.
    }
    destruct (fofam_OrdinalLike_empty_or_succ V M key hkeyOrd)
      as [hkeyEmpty | [predecessor [hpredKey hkeySucc]]].
    - destruct hfApprox as
        [hfun [_hkeys [hbase [_htotal _hstep]]]].
      assert (hpairEmpty : foam_mem V M
          (foam_kpair_obj V M (foam_empty V M) value) f).
      { rewrite <- hkeyEmpty. exact hpair. }
      left.
      exact (hfun (foam_empty V M) value s hpairEmpty hbase).
    - destruct hfApprox as
        [_hfun [_hkeys [_hbase [htotal hstep]]]].
      assert (hpredBound : foam_mem V M predecessor bound).
      {
        destruct hkey as [hkeyBound | hkeyBound].
        - exact (proj1 hboundOrd key hkeyBound
            predecessor hpredKey).
        - subst key. exact hpredKey.
      }
      destruct (htotal predecessor (or_introl hpredBound))
        as [previous hprevious].
      assert (hpredSat : Sat V (foam_mem V M)
          (scons V predecessor (scons V s (scons V f tail))) phi).
      {
        exact (proj1 (Sat_rename_rSkipParam V (foam_mem V M)
          phi (scons V s (scons V f tail)) key predecessor)
          (ih predecessor hpredKey)).
      }
      pose (Epred := scons V bound
        (scons V predecessor (scons V s (scons V f tail)))).
      pose (Eprevious := scons V previous Epred).
      assert (hboundSatPred : Sat V (foam_mem V M) Epred
          (HF_ordinalLikeAt 0)).
      {
        apply (proj2 (HF_ordinalLikeAt_spec V (foam_mem V M)
          Epred 0)).
        exact hboundOrd.
      }
      assert (hfSatPred : Sat V (foam_mem V M) Epred
          (HF_succRecApproxAt 3 2 0)).
      {
        apply (proj2 (foam_HF_succRecApproxAt_spec V M Epred 3 2 0)).
        exact (conj _hfun
          (conj _hkeys (conj _hbase (conj htotal hstep)))).
      }
      assert (hpreviousSat : Sat V (foam_mem V M) Eprevious
          (HF_pairMemAt 2 0 4)).
      {
        apply (proj2 (foam_HF_pairMemAt_spec V M Eprevious 2 0 4)).
        exact hprevious.
      }
      pose proof (hpredSat bound (or_introl hpredBound)
        hboundSatPred hfSatPred previous hpreviousSat) as hrec.
      assert (hpairSucc : foam_mem V M
          (foam_kpair_obj V M
            (foam_adjoin V M predecessor predecessor) value) f).
      { rewrite <- hkeySucc. exact hpair. }
      pose proof (hstep predecessor previous value
        hpredBound hprevious hpairSucc) as hvalue.
      right. rewrite hvalue.
      destruct hrec as [hpreviousBase | hbasePrevious].
      * apply (proj2 (foam_adjoin_spec V M s previous previous)).
        right. symmetry. exact hpreviousBase.
      * apply (proj2 (foam_adjoin_spec V M s previous previous)).
        now left.
  }
  pose (Em := scons V m
    (scons V k (scons V s (scons V f tail)))).
  pose (Ez := scons V z Em).
  pose proof (hall k) as hmain.
  unfold phi in hmain. simpl in hmain.
  assert (hmSat : Sat V (foam_mem V M) Em (HF_ordinalLikeAt 0)).
  {
    apply (proj2 (HF_ordinalLikeAt_spec V (foam_mem V M) Em 0)).
    exact hm.
  }
  assert (hfSat : Sat V (foam_mem V M) Em
      (HF_succRecApproxAt 3 2 0)).
  {
    apply (proj2 (foam_HF_succRecApproxAt_spec V M Em 3 2 0)).
    exact hf.
  }
  assert (hzSat : Sat V (foam_mem V M) Ez (HF_pairMemAt 2 0 4)).
  {
    apply (proj2 (foam_HF_pairMemAt_spec V M Ez 2 0 4)).
    exact hz.
  }
  exact (hmain m hk hmSat hfSat z hzSat).
Qed.

Lemma fofam_succ_rec_approx_base_mem_value_at_succ :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V)
    s f predecessor value,
  OrdinalLike (foam_mem V M) predecessor ->
  foam_succ_rec_approx V M s f
    (foam_adjoin V M predecessor predecessor) ->
  foam_mem V M
    (foam_kpair_obj V M
      (foam_adjoin V M predecessor predecessor) value) f ->
    foam_mem V M s value.
Proof.
  intros V M s f predecessor value hpred hf hvalue.
  pose proof (foam_adjoin_self_mem V M predecessor) as hpredSucc.
  destruct hf as [hfun [hkeys [hbase [htotal hstep]]]].
  destruct (htotal predecessor (or_introl hpredSucc))
    as [previous hprevious].
  pose proof (fofam_succ_rec_approx_value_eq_or_base_mem
    V M s f (foam_adjoin V M predecessor predecessor)
    predecessor previous
    (foam_OrdinalLike_adjoin_self V M predecessor
      (foam_adjoin V M predecessor predecessor) hpred eq_refl)
    (conj hfun (conj hkeys (conj hbase (conj htotal hstep))))
    (or_introl hpredSucc) hprevious) as hrec.
  pose proof (hstep predecessor previous value
    hpredSucc hprevious hvalue) as hvalueSucc.
  rewrite hvalueSucc.
  destruct hrec as [hpreviousBase | hbasePrevious].
  - apply (proj2 (foam_adjoin_spec V M s previous previous)).
    right. symmetry. exact hpreviousBase.
  - apply (proj2 (foam_adjoin_spec V M s previous previous)).
    now left.
Qed.

Lemma termGraphAt_succ_var_value_finite_model :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V)
    rho out n e,
  Sat V (foam_mem V M) e
    (termGraphAt rho out (PA.tSucc (PA.tVar n))) ->
    e out = foam_adjoin V M (e (rho n)) (e (rho n)).
Proof.
  intros V M rho out n e hgraph.
  pose proof (proj1 (termGraphAt_succ_var_spec V (foam_mem V M)
    rho out n e) hgraph) as hspec.
  apply (foam_extensional V (fofam_base V M)).
  intro x.
  rewrite hspec.
  symmetry.
  apply foam_adjoin_spec.
Qed.

(* The translated definition of strict order is addition of a nonzero
   successor.  The recursion trace at that successor therefore contains its
   left/base argument. *)
Lemma formulaAt_ltAt_mem_finite_model :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V)
    (e : nat -> V) rho elem set,
  Sat V (foam_mem V M) e
    (formulaAt rho (PA.Formula.ltAt elem set)) ->
    foam_mem V M (e (rho elem)) (e (rho set)).
Proof.
  intros V M e rho elem set hlt.
  destruct hlt as [w [hwDomain heq]].
  pose (Ew := scons V w e).
  assert (hwOrd : OrdinalLike (foam_mem V M) w).
  {
    apply (proj1 (HF_ordinalLikeAt_spec V (foam_mem V M) Ew 0)).
    exact hwDomain.
  }
  destruct heq as [x [y [hadd [hset hxy]]]].
  pose (Eeq := scons V y (scons V x Ew)).
  assert (hy : y = e (rho set)).
  {
    pose proof (proj1 (termGraphAt_var_spec V (foam_mem V M)
      (fun n => upVarMap rho n + 2) 0 (S set) Eeq) hset) as hyRaw.
    unfold Eeq, Ew in hyRaw.
    cbn [upVarMap scons] in hyRaw.
    replace (S (rho set) + 2) with
      (S (S (S (rho set)))) in hyRaw by lia.
    cbn [scons] in hyRaw.
    exact hyRaw.
  }
  destruct hadd as
    [leftValue [rightValue [hleft [hright hgraph]]]].
  pose (Eadd := scons V rightValue (scons V leftValue Eeq)).
  assert (hleftValue : leftValue = e (rho elem)).
  {
    pose proof (proj1 (termGraphAt_var_spec V (foam_mem V M)
      (fun n => upVarMap rho n + 2 + 2) 1 (S elem) Eadd)
      hleft) as hleftRaw.
    unfold Eadd, Eeq, Ew in hleftRaw.
    cbn [upVarMap scons] in hleftRaw.
    replace (S (rho elem) + 2 + 2) with
      (S (S (S (S (S (rho elem)))))) in hleftRaw by lia.
    cbn [scons] in hleftRaw.
    exact hleftRaw.
  }
  assert (hrightValue : rightValue = foam_adjoin V M w w).
  {
    pose proof (termGraphAt_succ_var_value_finite_model V M
      (fun n => upVarMap rho n + 2 + 2) 0 0 Eadd hright)
      as hrightRaw.
    unfold Eadd, Eeq, Ew in hrightRaw.
    cbn [upVarMap scons] in hrightRaw.
    exact hrightRaw.
  }
  destruct hgraph as [trace [htraceSat houtSat]].
  pose (Etrace := scons V trace Eadd).
  assert (htrace : foam_succ_rec_approx V M
      leftValue trace rightValue).
  {
    apply (proj1 (foam_HF_succRecApproxAt_spec V M
      Etrace 0 2 1)).
    exact htraceSat.
  }
  assert (hout : foam_mem V M
      (foam_kpair_obj V M rightValue x) trace).
  {
    apply (proj1 (foam_HF_pairMemAt_spec V M Etrace 1 4 0)).
    exact houtSat.
  }
  assert (hbaseMem : foam_mem V M leftValue x).
  {
    apply (fofam_succ_rec_approx_base_mem_value_at_succ
      V M leftValue trace w x hwOrd).
    - now rewrite <- hrightValue.
    - now rewrite <- hrightValue.
  }
  rewrite hleftValue, hxy, hy in hbaseMem.
  exact hbaseMem.
Qed.

(* Extract the two-free-variable membership bound from the uniform theorem
   produced by the membership-tail development. *)
Definition PAHFMembershipBoundProof : Prop :=
  PA.Formula.BProv PA.Formula.Ax_s []
    (PA.pImp (PA.Formula.hfMemAt 0 1)
      (PA.Formula.ltAt 0 1)).

Lemma PA_BProv_hfMem_imp_lt_of_tail :
  HFMembershipTailStep ->
  PAHFMembershipBoundProof.
Proof.
  intro htail.
  pose proof (BProv_Ax_s_all_hfMembersBelowAt_of_tail htail) as hall.
  pose proof (PA.Formula.BProv_allE PA.Formula.Ax_s []
    (hfMembersBelowAt 0) (PA.tVar 1) hall) as hset.
  change (PA.Formula.BProv PA.Formula.Ax_s []
    (hfMembersBelowAt 1)) in hset.
  pose proof (PA.Formula.BProv_allE PA.Formula.Ax_s []
    (PA.pImp (PA.Formula.hfMemAt 0 2) (PA.Formula.ltAt 0 2))
    (PA.tVar 0) hset) as helem.
  change (PA.Formula.BProv PA.Formula.Ax_s []
    (PA.pImp (PA.Formula.hfMemAt 0 1)
      (PA.Formula.ltAt 0 1))) in helem.
  exact helem.
Qed.

(** The PA beta-shift construction supplies the concrete tail certificate,
    hence the two-variable Ackermann membership bound is now unconditional. *)
Lemma PA_BProv_hfMem_imp_lt :
  PAHFMembershipBoundProof.
Proof.
  exact (PA_BProv_hfMem_imp_lt_of_tail hfMembershipTailStep).
Qed.

Lemma HFFinModelCompositeMemBelowLaw_of_translation_and_bound :
  HFFinPAProofTranslation ->
  PAHFMembershipBoundProof ->
    HFFinModelCompositeMemBelowLaw.
Proof.
  intros htranslate hbound V mem v hHF.
  cbn.
  pose (M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s
    V mem v hHF).
  change (ModelCompositeMemBelowLaw M).
  intros elemCode setCode helemOrd hsetOrd hcomp.
  destruct
    (BProv_HFFin_formulaAt_of_PA_BProv_domainContext_of_translation
      htranslate []
      (PA.pImp (PA.Formula.hfMemAt 0 1)
        (PA.Formula.ltAt 0 1))
      hbound)
    as [n htranslated].
  pose (rho := repPairSlotMap 0 1).
  pose (env := scons V elemCode
    (scons V setCode (fun _ : nat => foam_empty V M))).
  assert (hord : forall k, k < n ->
      OrdinalLike mem (env (rho k))).
  {
    intros [|k] hk.
    - change (OrdinalLike (foam_mem V M) elemCode).
      exact helemOrd.
    - change (OrdinalLike (foam_mem V M) setCode).
      exact hsetOrd.
  }
  assert (hdomain : forall g,
      In g (domainContextAt rho n) -> Sat V mem env g).
  {
    apply Sat_domainContextAt_of_ordinalLike.
    exact hord.
  }
  assert (hcontext : forall g,
      In g (domainContextAt rho n ++ translateContextAt rho []) ->
        Sat V mem env g).
  {
    intros g hg.
    unfold translateContextAt in hg.
    rewrite app_nil_r in hg.
    exact (hdomain g hg).
  }
  assert (hAx : forall g, HFFinAx_s g -> Sat V mem env g).
  {
    intros g hg.
    apply (proj1 (Sat_sentence_inv V mem g
      (Sentences_HFFin g hg) v env)).
    exact (hHF g hg).
  }
  pose proof (soundness_BProv_FOL V mem HFFinAx_s
    (domainContextAt rho n ++ translateContextAt rho [])
    (formulaAt rho
      (PA.pImp (PA.Formula.hfMemAt 0 1)
        (PA.Formula.ltAt 0 1)))
    (htranslated rho) env hAx hcontext) as htranslatedSat.
  assert (hmemSat : Sat V mem env
      (formulaAt rho (PA.Formula.hfMemAt 0 1))).
  {
    unfold ModelCompositeMem in hcomp.
    unfold HF_compositeMemAt in hcomp.
    unfold rho, env, repPairSlotMap.
    exact hcomp.
  }
  pose proof (htranslatedSat hmemSat) as hltSat.
  pose proof (formulaAt_ltAt_mem_finite_model V M
    env rho 0 1 hltSat) as hmem.
  unfold env, rho, repPairSlotMap in hmem.
  cbn [scons] in hmem.
  exact hmem.
Qed.

Lemma HFFinModelCompositeMemBelowLaw_of_translation_and_tail :
  HFFinPAProofTranslation ->
  HFMembershipTailStep ->
    HFFinModelCompositeMemBelowLaw.
Proof.
  intros htranslate htail.
  exact (HFFinModelCompositeMemBelowLaw_of_translation_and_bound
    htranslate (PA_BProv_hfMem_imp_lt_of_tail htail)).
Qed.

(** Translated PA proofs preserve the ambient finite-HF rank ordering for
    composite Ackermann membership, with all PA arithmetic discharged. *)
Lemma HFFinModelCompositeMemBelowLaw_of_translation :
  HFFinPAProofTranslation ->
    HFFinModelCompositeMemBelowLaw.
Proof.
  intro htranslate.
  exact (HFFinModelCompositeMemBelowLaw_of_translation_and_bound
    htranslate PA_BProv_hfMem_imp_lt).
Qed.

Lemma HFRoundTripProof_of_translation_composite_arithmetic_and_bound :
  HFFinPAProofTranslation ->
  HFFinModelCompositeMemExtensionality ->
  HFFinModelCompositeAdjoinCode ->
  PAHFMembershipBoundProof ->
    HFRoundTripProof.
Proof.
  intros htranslate hext hcode hbound.
  exact (HFRoundTripProof_of_translation_and_composite_arithmetic
    htranslate hext hcode
    (HFFinModelCompositeMemBelowLaw_of_translation_and_bound
      htranslate hbound)).
Qed.

Lemma HFRoundTripProof_of_translation_composite_arithmetic_and_tail :
  HFFinPAProofTranslation ->
  HFFinModelCompositeMemExtensionality ->
  HFFinModelCompositeAdjoinCode ->
  HFMembershipTailStep ->
    HFRoundTripProof.
Proof.
  intros htranslate hext hcode htail.
  exact (HFRoundTripProof_of_translation_composite_arithmetic_and_bound
    htranslate hext hcode (PA_BProv_hfMem_imp_lt_of_tail htail)).
Qed.

(** Public HF round-trip endpoint: the shifted-tail and membership-bound
    arithmetic is internal, leaving only the translation and the two
    structural composite-model certificates. *)
Lemma HFRoundTripProof_of_translation_composite_arithmetic :
  HFFinPAProofTranslation ->
  HFFinModelCompositeMemExtensionality ->
  HFFinModelCompositeAdjoinCode ->
    HFRoundTripProof.
Proof.
  intros htranslate hext hcode.
  exact (HFRoundTripProof_of_translation_composite_arithmetic_and_bound
    htranslate hext hcode PA_BProv_hfMem_imp_lt).
Qed.
