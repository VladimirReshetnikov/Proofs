(* ===================================================================== *)
(*  PAHFCompositeArithmetic.v                                            *)
(*                                                                       *)
(*  Finite-HF semantic transfer for the two structural arithmetic laws   *)
(*  used by the HF round trip: Ackermann-membership extensionality and    *)
(*  one-point Ackermann adjunction.                                      *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Lia List Logic.FunctionalExtensionality.
From FirstOrder Require Import Fol Calculus.
From PAHF Require Import PAHF PAHFInterpretations PAHFOrdinalCode
  PAHFOrdinalCodeTotalInduction PAHFHFRoundTrip
  PAHFHFRepresentationFinite PAHFHFRoundTripSemantic.

Import ListNotations.
Import PA PA.Term PA.Formula.

Definition PAHFCompositeSameMembers : formula :=
  pAll (iffForm (hfMemAt 0 2) (hfMemAt 0 1)).

(** Exact raw-PA theorem needed for extensionality of Ackermann codes. *)
Definition PAHFMembershipExtensionalityProof : Prop :=
  BProv Ax_s [PAHFCompositeSameMembers]
    (pEq (tVar 1) (tVar 0)).

(** Exact raw-PA theorem needed for one-point Ackermann adjunction. *)
Definition PAHFCompositeAdjoinExistenceProof : Prop :=
  BProv Ax_s [] (hfAdjoinExistsTermAt (tVar 1) (tVar 0)).

Lemma PAHFCompositeAdjoinExistenceProof_of_total :
  PAHFAdjoinExistence ->
    PAHFCompositeAdjoinExistenceProof.
Proof.
  intro hadjoin.
  exact (hadjoin [] (tVar 1) (tVar 0)).
Qed.

Lemma ModelCompositeMemExtensionalLaw_finite_of_translation :
  HFFinPAProofTranslation ->
  PAHFMembershipExtensionalityProof ->
  forall (V : Type) (mem : V -> V -> Prop) (v : nat -> V)
    (hHF : forall g, HFFinAx_s g -> Fol.Sat V mem v g),
  let M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s V mem v hHF in
    ModelCompositeMemExtensionalLaw (fofam_base V M).
Proof.
  intros htranslate hextPA V mem v hHF.
  pose (M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s
    V mem v hHF).
  change (ModelCompositeMemExtensionalLaw (fofam_base V M)).
  unfold PAHFMembershipExtensionalityProof in hextPA.
  destruct
    (BProv_HFFin_formulaAt_of_PA_BProv_domainContext_of_translation
      htranslate [PAHFCompositeSameMembers]
      (pEq (tVar 1) (tVar 0)) hextPA)
    as [n htranslated].
  intros left right hleft hright hsame.
  pose (env := scons V right
    (scons V left (fun _ : nat => foam_empty V M))).
  pose (rho := fun k : nat => k).
  assert (hord : forall k, k < n ->
      OrdinalLike mem (env (rho k))).
  {
    intros [|[|k]] hk.
    - change (OrdinalLike (foam_mem V M) right).
      exact hright.
    - change (OrdinalLike (foam_mem V M) left).
      exact hleft.
    - change (OrdinalLike (foam_mem V M) (foam_empty V M)).
      apply foam_OrdinalLike_empty.
  }
  assert (hdomain : forall g,
      In g (domainContextAt rho n) -> Fol.Sat V mem env g).
  {
    apply Sat_domainContextAt_of_ordinalLike.
    exact hord.
  }
  assert (hleftFormula :
      formulaAt (upVarMap rho) (hfMemAt 0 2) =
        HF_compositeMemAt 0 2).
  {
    assert (hup : upVarMap rho = (fun k : nat => k)).
    {
      apply functional_extensionality. intros [|k]; reflexivity.
    }
    rewrite hup.
    change (hfCompositeAt (fun k : nat => k) (fMem 0 2) =
      HF_compositeMemAt 0 2).
    exact (hfCompositeAt_mem (fun k : nat => k) 0 2).
  }
  assert (hrightFormula :
      formulaAt (upVarMap rho) (hfMemAt 0 1) =
        HF_compositeMemAt 0 1).
  {
    assert (hup : upVarMap rho = (fun k : nat => k)).
    {
      apply functional_extensionality. intros [|k]; reflexivity.
    }
    rewrite hup.
    change (hfCompositeAt (fun k : nat => k) (fMem 0 1) =
      HF_compositeMemAt 0 1).
    exact (hfCompositeAt_mem (fun k : nat => k) 0 1).
  }
  assert (hsameSat : Fol.Sat V mem env
      (formulaAt rho PAHFCompositeSameMembers)).
  {
    intro query. intro hqueryDomain.
    assert (hqueryOrd : OrdinalLike mem query).
    {
      apply (proj1 (HF_ordinalLikeAt_spec V mem
        (scons V query env) 0)).
      exact hqueryDomain.
    }
    change (Fol.Sat V mem (scons V query env)
      (fIff
        (formulaAt (upVarMap rho) (hfMemAt 0 2))
        (formulaAt (upVarMap rho) (hfMemAt 0 1)))).
    rewrite hleftFormula, hrightFormula.
    split.
    - intro hqueryLeft.
      apply (proj2 (HF_compositeMemAt_01_model
        V (fofam_base V M) (scons V query env))).
      apply (proj1 (hsame query hqueryOrd)).
      apply (proj1 (HF_compositeMemAt_model
        V (fofam_base V M) (scons V query env) 0 2)).
      exact hqueryLeft.
    - intro hqueryRight.
      apply (proj2 (HF_compositeMemAt_model
        V (fofam_base V M) (scons V query env) 0 2)).
      apply (proj2 (hsame query hqueryOrd)).
      apply (proj1 (HF_compositeMemAt_01_model
        V (fofam_base V M) (scons V query env))).
      exact hqueryRight.
  }
  assert (hcontext : forall g,
      In g (domainContextAt rho n ++
        translateContextAt rho [PAHFCompositeSameMembers]) ->
      Fol.Sat V mem env g).
  {
    intros g hg.
    apply in_app_iff in hg.
    destruct hg as [hg | hg].
    - exact (hdomain g hg).
    - simpl in hg. destruct hg as [<- | []]. exact hsameSat.
  }
  assert (hAx : forall g,
      HFFinAx_s g -> Fol.Sat V mem env g).
  {
    intros g hg.
    apply (proj1 (Sat_sentence_inv V mem g
      (Sentences_HFFin g hg) v env)).
    exact (hHF g hg).
  }
  pose proof (soundness_BProv_FOL V mem HFFinAx_s
    (domainContextAt rho n ++
      translateContextAt rho [PAHFCompositeSameMembers])
    (formulaAt rho (pEq (tVar 1) (tVar 0)))
    (htranslated rho) env hAx hcontext) as heqSat.
  apply (proj1 (formulaAt_eq_var_spec V mem rho 1 0 env)).
  exact heqSat.
Qed.

Lemma HFFinModelCompositeMemExtensionality_of_translation :
  HFFinPAProofTranslation ->
  PAHFMembershipExtensionalityProof ->
    HFFinModelCompositeMemExtensionality.
Proof.
  intros htranslate hext V mem v hHF.
  exact (ModelCompositeMemExtensionalLaw_finite_of_translation
    htranslate hext V mem v hHF).
Qed.

Lemma ModelCompositeAdjoinCodeData_exists_finite_of_translation :
  HFFinPAProofTranslation ->
  PAHFCompositeAdjoinExistenceProof ->
  forall (V : Type) (mem : V -> V -> Prop) (v : nat -> V)
    (hHF : forall g, HFFinAx_s g -> Fol.Sat V mem v g)
    oldCode elemCode,
  let M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s V mem v hHF in
  OrdinalLike mem oldCode ->
  OrdinalLike mem elemCode ->
    exists newCode,
      ModelCompositeAdjoinCodeData (fofam_base V M)
        oldCode elemCode newCode.
Proof.
  intros htranslate hadjoinPA V mem v hHF oldCode elemCode.
  pose (M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s
    V mem v hHF).
  change (OrdinalLike (foam_mem V M) oldCode ->
    OrdinalLike (foam_mem V M) elemCode ->
    exists newCode,
      ModelCompositeAdjoinCodeData (fofam_base V M)
        oldCode elemCode newCode).
  intros hold helem.
  unfold PAHFCompositeAdjoinExistenceProof in hadjoinPA.
  destruct
    (BProv_HFFin_formulaAt_of_PA_BProv_domainContext_of_translation
      htranslate []
      (hfAdjoinExistsTermAt (tVar 1) (tVar 0)) hadjoinPA)
    as [n htranslated].
  pose (env := scons V elemCode
    (scons V oldCode (fun _ : nat => foam_empty V M))).
  pose (rho := fun k : nat => k).
  assert (hord : forall k, k < n ->
      OrdinalLike mem (env (rho k))).
  {
    intros [|[|k]] hk.
    - change (OrdinalLike (foam_mem V M) elemCode). exact helem.
    - change (OrdinalLike (foam_mem V M) oldCode). exact hold.
    - change (OrdinalLike (foam_mem V M) (foam_empty V M)).
      apply foam_OrdinalLike_empty.
  }
  assert (hdomain : forall g,
      In g (domainContextAt rho n) -> Fol.Sat V mem env g).
  {
    apply Sat_domainContextAt_of_ordinalLike.
    exact hord.
  }
  assert (hcontext : forall g,
      In g (domainContextAt rho n ++ translateContextAt rho []) ->
        Fol.Sat V mem env g).
  {
    intros g hg. apply in_app_iff in hg.
    destruct hg as [hg | hg].
    - exact (hdomain g hg).
    - simpl in hg. contradiction.
  }
  assert (hAx : forall g,
      HFFinAx_s g -> Fol.Sat V mem env g).
  {
    intros g hg.
    apply (proj1 (Sat_sentence_inv V mem g
      (Sentences_HFFin g hg) v env)).
    exact (hHF g hg).
  }
  pose proof (soundness_BProv_FOL V mem HFFinAx_s
    (domainContextAt rho n ++ translateContextAt rho [])
    (formulaAt rho (hfAdjoinExistsTermAt (tVar 1) (tVar 0)))
    (htranslated rho) env hAx hcontext) as htranslatedSat.
  destruct htranslatedSat as [newCode htranslatedSat].
  destruct htranslatedSat as [hnewDomain hgraph].
  assert (hnewOrd : OrdinalLike mem newCode).
  {
    apply (proj1 (HF_ordinalLikeAt_spec V mem
      (scons V newCode env) 0)).
    exact hnewDomain.
  }
  exists newCode.
  constructor.
  - exact hnewOrd.
  - intros query hqueryOrd.
    assert (hqueryDomain : Fol.Sat V mem
        (scons V query (scons V newCode env)) domainForm).
    {
      apply (proj2 (HF_ordinalLikeAt_spec V mem
        (scons V query (scons V newCode env)) 0)).
      exact hqueryOrd.
    }
    specialize (hgraph query hqueryDomain).
    set (queryEnv := scons V query (scons V newCode env)).
    assert (hrho2 : upVarMap (upVarMap rho) = (fun k : nat => k)).
    {
      apply functional_extensionality.
      intros [|[|k]]; reflexivity.
    }
    change (Fol.Sat V mem queryEnv
      (formulaAt (upVarMap (upVarMap rho))
        (iffForm
          (hfMemAt 0 1)
          (pOr (hfMemAt 0 3) (pEq (tVar 0) (tVar 2))))))
      in hgraph.
    rewrite hrho2 in hgraph.
    assert (hnewFormula :
        formulaAt (fun k : nat => k) (hfMemAt 0 1) =
          HF_compositeMemAt 0 1).
    {
      change (hfCompositeAt (fun k : nat => k) (fMem 0 1) =
        HF_compositeMemAt 0 1).
      exact (hfCompositeAt_mem (fun k : nat => k) 0 1).
    }
    assert (holdFormula :
        formulaAt (fun k : nat => k) (hfMemAt 0 3) =
          HF_compositeMemAt 0 3).
    {
      change (hfCompositeAt (fun k : nat => k) (fMem 0 3) =
        HF_compositeMemAt 0 3).
      exact (hfCompositeAt_mem (fun k : nat => k) 0 3).
    }
    change
      ((Fol.Sat V mem queryEnv
          (formulaAt (fun k : nat => k) (hfMemAt 0 1)) ->
        Fol.Sat V mem queryEnv
          (formulaAt (fun k : nat => k) (hfMemAt 0 3)) \/
        Fol.Sat V mem queryEnv
          (formulaAt (fun k : nat => k)
            (pEq (tVar 0) (tVar 2)))) /\
       ((Fol.Sat V mem queryEnv
          (formulaAt (fun k : nat => k) (hfMemAt 0 3)) \/
        Fol.Sat V mem queryEnv
          (formulaAt (fun k : nat => k)
            (pEq (tVar 0) (tVar 2)))) ->
        Fol.Sat V mem queryEnv
          (formulaAt (fun k : nat => k) (hfMemAt 0 1))))
      in hgraph.
    rewrite hnewFormula, holdFormula in hgraph.
    split.
    + intro hnewModel.
      assert (hnewSat : Fol.Sat V mem queryEnv
          (HF_compositeMemAt 0 1)).
      {
        apply (proj2 (HF_compositeMemAt_model
          V (fofam_base V M) queryEnv 0 1)).
        exact hnewModel.
      }
      destruct (proj1 hgraph hnewSat) as [holdSat | helemSat].
      * left.
        apply (proj1 (HF_compositeMemAt_model
          V (fofam_base V M) queryEnv 0 3)).
        exact holdSat.
      * right.
        apply (proj1 (formulaAt_eq_var_spec V mem
          (fun k : nat => k) 0 2 queryEnv)).
        exact helemSat.
    + intro hrhs.
      apply (proj1 (HF_compositeMemAt_model
        V (fofam_base V M) queryEnv 0 1)).
      apply (proj2 hgraph).
      destruct hrhs as [holdModel | heq].
      * left.
        apply (proj2 (HF_compositeMemAt_model
          V (fofam_base V M) queryEnv 0 3)).
        exact holdModel.
      * right.
        apply (proj2 (formulaAt_eq_var_spec V mem
          (fun k : nat => k) 0 2 queryEnv)).
        exact heq.
Qed.

Lemma HFFinModelCompositeAdjoinCode_of_translation :
  HFFinPAProofTranslation ->
  PAHFCompositeAdjoinExistenceProof ->
    HFFinModelCompositeAdjoinCode.
Proof.
  intros htranslate hadjoin V mem v hHF.
  cbn.
  intros oldCode elemCode hold helem.
  exact (ModelCompositeAdjoinCodeData_exists_finite_of_translation
    htranslate hadjoin V mem v hHF oldCode elemCode hold helem).
Qed.
