(* ===================================================================== *)
(*  PAHFHFRepresentation.v                                               *)
(*                                                                       *)
(*  Honest base case for the internal HF set-to-ordinal representation.  *)
(*  The model semantics are environment-independent; the only arithmetic  *)
(*  boundary is isolated as [NoCompositeMembersOfEmpty].                  *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Lia List.
From SetTheory Require Import Fol Calculus Completeness PAHF
  PAHFHFRoundTrip PAHFInterpretations.
Import ListNotations.

(* Semantic totality in every reconstructed finite-HF model implies the
   corresponding object-language existential by relative completeness. *)
Lemma BProv_HFFin_setOrdinalRep_total_of_model_total :
  (forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V)
      (e : nat -> V) set,
    exists code,
      ModelSetOrdinalRep (fofam_base V M) (e set) code) ->
  forall G set,
    BProv HFFinAx_s G
      (fEx (HF_setOrdinalRepAt (S set) 0)).
Proof.
  intros hmodel G set.
  apply (completeness_inf_context HFFinAx_s G
    (fEx (HF_setOrdinalRepAt (S set) 0)) Sentences_HFFin).
  intros V mem v hHF hG.
  pose (M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s V mem v hHF).
  destruct (hmodel V M v set) as [code hrep].
  exists code.
  apply (proj2 (HF_setOrdinalRepAt_model V (fofam_base V M)
    (scons V code v) (S set) 0)).
  cbn [scons].
  exact hrep.
Qed.

(* PA proves the arithmetic fact used at the empty-code boundary. *)
Lemma PA_BProv_no_hfMem_of_eq_zero :
  PA.Formula.BProv PA.Formula.Ax_s []
    (PA.pImp (PA.Formula.eqConstAt 1 0)
      (PA.pImp (PA.Formula.hfMemAt 0 1) PA.pBot)).
Proof.
  apply PA.Formula.BProv_impI.
  apply PA.Formula.BProv_impI.
  apply (PA.Formula.BProv_Ax_s_hfMemAt_bot_of_eqConst_zero
    [PA.Formula.hfMemAt 0 1; PA.Formula.eqConstAt 1 0] 0 1).
  - apply PA.Formula.BProv_ass.
    simpl. right. left. reflexivity.
  - apply PA.Formula.BProv_ass.
    simpl. left. reflexivity.
Qed.

(* No ordinal code is an Ackermann member of the internal zero code. *)
Definition NoCompositeMembersOfEmpty {V : Type}
    (M : FirstOrderAdjunctionModel V) : Prop :=
  forall elemCode,
    OrdinalLike (foam_mem V M) elemCode ->
      ~ ModelCompositeMem M elemCode (foam_empty V M).

(* The singleton graph whose only root is <empty,empty>. *)
Definition emptySetOrdinalRepGraph {V : Type}
    (M : FirstOrderAdjunctionModel V) : V :=
  foam_single_obj V M
    (foam_kpair_obj V M (foam_empty V M) (foam_empty V M)).

Lemma emptySetOrdinalRepGraph_root : forall (V : Type)
    (M : FirstOrderAdjunctionModel V),
  foam_mem V M
    (foam_kpair_obj V M (foam_empty V M) (foam_empty V M))
    (emptySetOrdinalRepGraph M).
Proof.
  intros V M.
  apply (proj2 (foam_single_spec V M
    (foam_kpair_obj V M (foam_empty V M) (foam_empty V M))
    (foam_kpair_obj V M (foam_empty V M) (foam_empty V M)))).
  reflexivity.
Qed.

(* All graph-theoretic obligations for the empty representation; only the
   explicit arithmetic boundary above remains as a premise. *)
Lemma ModelSetOrdinalRep_empty : forall (V : Type)
    (M : FirstOrderAdjunctionModel V),
  NoCompositeMembersOfEmpty M ->
    ModelSetOrdinalRep M (foam_empty V M) (foam_empty V M).
Proof.
  intros V M hzero.
  exists (emptySetOrdinalRepGraph M).
  split.
  - apply emptySetOrdinalRepGraph_root.
  - split.
    + unfold foam_pair_functional.
      intros k y y' hky hky'.
      pose proof (proj1 (foam_single_spec V M
        (foam_kpair_obj V M (foam_empty V M) (foam_empty V M))
        (foam_kpair_obj V M k y)) hky) as hkyEq.
      pose proof (proj1 (foam_single_spec V M
        (foam_kpair_obj V M (foam_empty V M) (foam_empty V M))
        (foam_kpair_obj V M k y')) hky') as hky'Eq.
      pose proof (proj2 (foam_kpair_injective V M
        k y (foam_empty V M) (foam_empty V M) hkyEq)) as hy.
      pose proof (proj2 (foam_kpair_injective V M
        k y' (foam_empty V M) (foam_empty V M) hky'Eq)) as hy'.
      now rewrite hy, hy'.
    + intros set code hpair.
      pose proof (proj1 (foam_single_spec V M
        (foam_kpair_obj V M (foam_empty V M) (foam_empty V M))
        (foam_kpair_obj V M set code)) hpair) as hpairEq.
      pose proof (foam_kpair_injective V M set code
        (foam_empty V M) (foam_empty V M) hpairEq) as hrootEq.
      destruct hrootEq as [hset hcode].
      subst set. subst code.
      split.
      * apply foam_OrdinalLike_empty.
      * split.
        -- intro elem.
           split.
           ++ intro hmem.
              exfalso. exact (foam_empty_spec V M elem hmem).
           ++ intros [elemCode [hchild hcoded]].
              pose proof (proj1 (foam_single_spec V M
                (foam_kpair_obj V M (foam_empty V M) (foam_empty V M))
                (foam_kpair_obj V M elem elemCode)) hchild) as hchildEq.
              pose proof (proj2 (foam_kpair_injective V M elem elemCode
                (foam_empty V M) (foam_empty V M) hchildEq)) as helemCode.
              subst elemCode.
              exfalso.
              exact (hzero (foam_empty V M)
                (foam_OrdinalLike_empty V M) hcoded).
        -- intros elemCode helemOrd hcoded.
           exfalso.
           exact (hzero elemCode helemOrd hcoded).
Qed.

(* The currently isolated PA-proof translation residual suffices to transport
   the arithmetic zero-code theorem into every arbitrary HFFin model. *)
Lemma NoCompositeMembersOfEmpty_of_HFFinAx_s_of_translation :
  HFFinPAProofTranslation ->
  forall (V : Type) (mem : V -> V -> Prop) (v : nat -> V)
      (hHF : forall g, HFFinAx_s g -> Sat V mem v g),
    NoCompositeMembersOfEmpty
      (fofam_base V
        (firstOrderFiniteAdjunctionModel_of_HFFinAx_s V mem v hHF)).
Proof.
  intros htranslate V mem v hHF.
  pose (M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s V mem v hHF).
  change (NoCompositeMembersOfEmpty (fofam_base V M)).
  destruct
    (BProv_HFFin_formulaAt_of_PA_BProv_domainContext_of_translation
      htranslate []
      (PA.pImp (PA.Formula.eqConstAt 1 0)
        (PA.pImp (PA.Formula.hfMemAt 0 1) PA.pBot))
      PA_BProv_no_hfMem_of_eq_zero) as [n htranslated].
  intros elemCode helemOrd hcomp.
  pose (rho := repPairSlotMap 0 1).
  pose (env := scons V elemCode
    (scons V (foam_empty V M) (fun _ : nat => foam_empty V M))).
  assert (hord : forall k, k < n ->
      OrdinalLike mem (env (rho k))).
  {
    intros [|k] hk.
    - change (OrdinalLike (foam_mem V M) elemCode).
      exact helemOrd.
    - change (OrdinalLike (foam_mem V M) (foam_empty V M)).
      apply foam_OrdinalLike_empty.
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
    apply in_app_iff in hg.
    destruct hg as [hg | hg].
    - apply hdomain. exact hg.
    - simpl in hg. contradiction.
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
      (PA.pImp (PA.Formula.eqConstAt 1 0)
        (PA.pImp (PA.Formula.hfMemAt 0 1) PA.pBot)))
    (htranslated rho) env hAx hcontext) as htranslatedSat.
  assert (hzeroEq : Sat V mem env
      (formulaAt rho (PA.Formula.eqConstAt 1 0))).
  {
    change (exists x y,
      Sat V mem (scons V y (scons V x env))
        (termGraphAt (fun k => rho k + 2) 1 (PA.tVar 1)) /\
      Sat V mem (scons V y (scons V x env))
        (termGraphAt (fun k => rho k + 2) 0 PA.tZero) /\
      x = y).
    exists (foam_empty V M), (foam_empty V M).
    split.
    - apply (proj2 (termGraphAt_var_spec V mem
        (fun k => rho k + 2) 1 1
        (scons V (foam_empty V M)
          (scons V (foam_empty V M) env)))).
      unfold rho, repPairSlotMap, env.
      cbn [scons]. reflexivity.
    - split.
      + apply (proj2 (termGraphAt_zero_spec V mem
          (fun k => rho k + 2) 0
          (scons V (foam_empty V M)
            (scons V (foam_empty V M) env)))).
        cbn [scons].
        exact (foam_empty_spec V M).
      + reflexivity.
  }
  assert (hmem : Sat V mem env
      (formulaAt rho (PA.Formula.hfMemAt 0 1))).
  {
    unfold ModelCompositeMem in hcomp.
    unfold HF_compositeMemAt in hcomp.
    unfold rho, env.
    exact hcomp.
  }
  exact (htranslatedSat hzeroEq hmem).
Qed.

Lemma ModelSetOrdinalRep_empty_of_HFFinAx_s_of_translation :
  HFFinPAProofTranslation ->
  forall (V : Type) (mem : V -> V -> Prop) (v : nat -> V)
      (hHF : forall g, HFFinAx_s g -> Sat V mem v g),
    let M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s V mem v hHF in
    ModelSetOrdinalRep (fofam_base V M)
      (foam_empty V M) (foam_empty V M).
Proof.
  intros htranslate V mem v hHF.
  pose (M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s V mem v hHF).
  change (ModelSetOrdinalRep (fofam_base V M)
    (foam_empty V M) (foam_empty V M)).
  apply ModelSetOrdinalRep_empty.
  exact (NoCompositeMembersOfEmpty_of_HFFinAx_s_of_translation
    htranslate V mem v hHF).
Qed.

(* Completeness closes the object-language empty-base theorem once the exact
   PA proof-translation residual is supplied. *)
Lemma BProv_HFFin_setOrdinalRep_total_of_empty_of_translation :
  HFFinPAProofTranslation ->
  forall G set,
    BProv HFFinAx_s G
      (fImp (HF_emptyAt set)
        (fEx (HF_setOrdinalRepAt (S set) 0))).
Proof.
  intros htranslate G set.
  apply (completeness_inf_context HFFinAx_s G
    (fImp (HF_emptyAt set)
      (fEx (HF_setOrdinalRepAt (S set) 0))) Sentences_HFFin).
  intros V mem v hHF hG hEmpty.
  pose (M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s V mem v hHF).
  assert (hset : v set = foam_empty V M).
  {
    exact (proj1 (foam_HF_emptyAt_empty V (fofam_base V M) v set)
      hEmpty).
  }
  exists (foam_empty V M).
  apply (proj2 (HF_setOrdinalRepAt_model V (fofam_base V M)
    (scons V (foam_empty V M) v) (S set) 0)).
  cbn [scons].
  rewrite hset.
  exact (ModelSetOrdinalRep_empty_of_HFFinAx_s_of_translation
    htranslate V mem v hHF).
Qed.
