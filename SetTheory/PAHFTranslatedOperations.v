(* ===================================================================== *)
(*  PAHFTranslatedOperations.v                                          *)
(*                                                                       *)
(*  Small HFFin theorems used by the PA round-trip term arithmetic.      *)
(*                                                                       *)
(*  The operation laws are proved once by arbitrary-model semantics and  *)
(*  completeness, then transported into PA through any concrete proof of *)
(*  the translated HFFin axioms.  This avoids replaying the internal      *)
(*  finite-set recursions in the PA natural-deduction calculus.           *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Lia List Logic.FunctionalExtensionality.
From SetTheory Require Import Fol Calculus Completeness PAHF
  PAHFOrdinalCode PAHFTermGraphFunctional.

Import ListNotations.
Import PA PA.Term PA.Formula.

(** A single reusable bridge from a semantic HFFin theorem to PA. *)
Lemma BProv_Ax_s_translateHFFin_theorem : forall
    (P : TranslatedHFFinAxiomProofs) phi,
  Completeness.BProv HFFinAx_s [] phi ->
  BProv Ax_s [] (translateHFFormula phi).
Proof.
  intros P phi hphi.
  apply (BProv_lift_translatedHFFinAx_to_PA
    (BProv_Ax_s_of_translatedHFFinAx_of_proofs P)).
  apply BProv_translateHFFormula_of_BProv_HFFin.
  exact hphi.
Qed.

(** Reverse translations of the HF addition and multiplication graphs. *)
Definition hfAddGraphAt (out left right : nat) : formula :=
  hfFormulaAt (fun n : nat => n) (addGraphAt out left right).

Definition hfMulGraphAt (out left right : nat) : formula :=
  hfFormulaAt (fun n : nat => n) (mulGraphAt out left right).

Definition addHFOrdinalLikeAt (slot : nat) : formula :=
  hfFormulaAt (fun n : nat => n) (HF_ordinalLikeAt slot).

Definition hfEmptyCodeAt (slot : nat) : formula :=
  hfFormulaAt (fun n : nat => n) (HF_emptyAt slot).

Lemma hfUpVarMap_id :
  hfUpVarMap (fun n : nat => n) = (fun n : nat => n).
Proof.
  apply functional_extensionality.
  intros [|n]; reflexivity.
Qed.

(* --------------------------------------------------------------------- *)
(*  Addition                                                             *)
(* --------------------------------------------------------------------- *)

Definition HF_addZeroRightSentence : form :=
  fAll (fAll (fAll
    (fImp
      (HF_emptyAt 1)
      (fImp
        (fEq 0 2)
        (addGraphAt 0 2 1))))).

Lemma HF_addZeroRightSentence_sentence :
  Fol.Sentence HF_addZeroRightSentence.
Proof.
  intros i hi.
  unfold HF_addZeroRightSentence, HF_emptyAt, addGraphAt,
    HF_succRecApproxAt, HF_pairMemAt, HF_kpairAt, HF_singleAt,
    HF_upairAt, HF_pairFunctionalAt, HF_pairKeysBelowSuccAt,
    HF_pairZeroBaseAt, HF_pairTotalBelowSuccAt, HF_pairSuccStepAt,
    HF_succAt, HF_adjoinAt, fIff in hi.
  simpl in hi.
  lia.
Qed.

Lemma BProv_HFFin_addZeroRightSentence :
  Completeness.BProv HFFinAx_s [] HF_addZeroRightSentence.
Proof.
  apply Completeness.completeness_inf.
  - exact Sentences_HFFin.
  - exact HF_addZeroRightSentence_sentence.
  - intros V mem v hHF.
    pose (M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s V mem v hHF).
    intros left right out hright hout.
    set (e := scons V out (scons V right (scons V left v))).
    assert (hrightM : Fol.Sat V (foam_mem V M) e (HF_emptyAt 1)).
    {
      change (Fol.Sat V mem e (HF_emptyAt 1)).
      unfold e, scons.
      exact hright.
    }
    apply (addGraphAt_zero_right_model V M e 0 2 1).
    + unfold e, scons. exact hout.
    + exact (proj1 (foam_HF_emptyAt_empty V M e 1) hrightM).
Qed.

Lemma translateHFFormula_addZeroRightSentence :
  translateHFFormula HF_addZeroRightSentence =
    pAll (pAll (pAll
      (pImp
        (hfEmptyCodeAt 1)
        (pImp
          (pEq (tVar 0) (tVar 2))
          (hfAddGraphAt 0 2 1))))).
Proof.
  unfold HF_addZeroRightSentence, translateHFFormula,
    hfAddGraphAt, hfEmptyCodeAt.
  simpl.
  repeat rewrite hfUpVarMap_id.
  reflexivity.
Qed.

Lemma BProv_Ax_s_addZeroRightSentence : forall
    (P : TranslatedHFFinAxiomProofs),
  BProv Ax_s []
    (pAll (pAll (pAll
      (pImp
        (hfEmptyCodeAt 1)
        (pImp
          (pEq (tVar 0) (tVar 2))
          (hfAddGraphAt 0 2 1)))))).
Proof.
  intro P.
  rewrite <- translateHFFormula_addZeroRightSentence.
  exact (BProv_Ax_s_translateHFFin_theorem P _
    BProv_HFFin_addZeroRightSentence).
Qed.

Definition HF_addSuccRightSentence : form :=
  fAll (fAll (fAll (fAll (fAll
    (fImp
      (HF_ordinalLikeAt 3)
      (fImp
        (HF_succAt 2 3)
        (fImp
          (HF_succAt 0 1)
          (fImp
            (addGraphAt 1 4 3)
            (addGraphAt 0 4 2))))))))).

Lemma HF_addSuccRightSentence_sentence :
  Fol.Sentence HF_addSuccRightSentence.
Proof.
  intros i hi.
  unfold HF_addSuccRightSentence, HF_ordinalLikeAt, HF_transitiveAt,
    HF_memTotalOnAt, HF_succAt, HF_adjoinAt, addGraphAt,
    HF_succRecApproxAt, HF_pairMemAt, HF_kpairAt, HF_singleAt,
    HF_upairAt, HF_pairFunctionalAt, HF_pairKeysBelowSuccAt,
    HF_pairZeroBaseAt, HF_pairTotalBelowSuccAt, HF_pairSuccStepAt, fIff in hi.
  simpl in hi.
  lia.
Qed.

Lemma BProv_HFFin_addSuccRightSentence :
  Completeness.BProv HFFinAx_s [] HF_addSuccRightSentence.
Proof.
  apply Completeness.completeness_inf.
  - exact Sentences_HFFin.
  - exact HF_addSuccRightSentence_sentence.
  - intros V mem v hHF.
    pose (M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s V mem v hHF).
    intros left right rightSucc out outSucc
      hrightOrd hrightSucc houtSucc hadd.
    set (e := scons V outSucc
      (scons V out (scons V rightSucc
        (scons V right (scons V left v))))).
    assert (hrightOrdM : Fol.Sat V (foam_mem V M) e (HF_ordinalLikeAt 3)).
    { change (Fol.Sat V mem e (HF_ordinalLikeAt 3)). unfold e, scons. exact hrightOrd. }
    assert (hrightSuccM : Fol.Sat V (foam_mem V M) e (HF_succAt 2 3)).
    { change (Fol.Sat V mem e (HF_succAt 2 3)). unfold e, scons. exact hrightSucc. }
    assert (houtSuccM : Fol.Sat V (foam_mem V M) e (HF_succAt 0 1)).
    { change (Fol.Sat V mem e (HF_succAt 0 1)). unfold e, scons. exact houtSucc. }
    assert (haddM : Fol.Sat V (foam_mem V M) e (addGraphAt 1 4 3)).
    { change (Fol.Sat V mem e (addGraphAt 1 4 3)). unfold e, scons. exact hadd. }
    unfold addGraphAt in haddM.
    destruct haddM as [f [hf hpair]].
    apply (addGraphAt_succ_right_of_succRecApprox_model V
      M e 0 4 2 3 f (e 1)).
    + exact (proj1 (HF_ordinalLikeAt_spec V (foam_mem V M) e 3)
        hrightOrdM).
    + exact (proj1 (foam_HF_succAt_spec V M e 2 3) hrightSuccM).
    + exact (proj1 (foam_HF_succAt_spec V M e 0 1) houtSuccM).
    + exact (proj1 (foam_HF_succRecApproxAt_spec V M
        (scons V f e) 0 5 4) hf).
    + exact (proj1 (foam_HF_pairMemAt_spec V M
        (scons V f e) 4 2 0) hpair).
Qed.

Lemma translateHFFormula_addSuccRightSentence :
  translateHFFormula HF_addSuccRightSentence =
    pAll (pAll (pAll (pAll (pAll
      (pImp
        (addHFOrdinalLikeAt 3)
        (pImp
          (hfAdjoinGraphTermAt (tVar 2) (tVar 3) (tVar 3))
          (pImp
            (hfAdjoinGraphTermAt (tVar 0) (tVar 1) (tVar 1))
            (pImp
              (hfAddGraphAt 1 4 3)
              (hfAddGraphAt 0 4 2))))))))).
Proof.
  unfold HF_addSuccRightSentence, translateHFFormula,
    addHFOrdinalLikeAt, hfAdjoinGraphTermAt, hfAddGraphAt.
  simpl.
  repeat rewrite hfUpVarMap_id.
  reflexivity.
Qed.

Lemma BProv_Ax_s_addSuccRightSentence : forall
    (P : TranslatedHFFinAxiomProofs),
  BProv Ax_s []
    (pAll (pAll (pAll (pAll (pAll
      (pImp
        (addHFOrdinalLikeAt 3)
        (pImp
          (hfAdjoinGraphTermAt (tVar 2) (tVar 3) (tVar 3))
          (pImp
            (hfAdjoinGraphTermAt (tVar 0) (tVar 1) (tVar 1))
            (pImp
              (hfAddGraphAt 1 4 3)
              (hfAddGraphAt 0 4 2)))))))))).
Proof.
  intro P.
  rewrite <- translateHFFormula_addSuccRightSentence.
  exact (BProv_Ax_s_translateHFFin_theorem P _
    BProv_HFFin_addSuccRightSentence).
Qed.

Definition HF_addFunctionalSentence : form :=
  fAll (fAll (fAll (fAll
    (fImp
      (HF_ordinalLikeAt 2)
      (fImp
        (addGraphAt 1 3 2)
        (fImp
          (addGraphAt 0 3 2)
          (fEq 1 0))))))).

Lemma HF_addFunctionalSentence_sentence :
  Fol.Sentence HF_addFunctionalSentence.
Proof.
  intros i hi.
  unfold HF_addFunctionalSentence, HF_ordinalLikeAt, HF_transitiveAt,
    HF_memTotalOnAt, addGraphAt, HF_succRecApproxAt, HF_pairMemAt,
    HF_kpairAt, HF_singleAt, HF_upairAt, HF_pairFunctionalAt,
    HF_pairKeysBelowSuccAt, HF_pairZeroBaseAt, HF_pairTotalBelowSuccAt,
    HF_pairSuccStepAt, HF_succAt, HF_adjoinAt, fIff in hi.
  simpl in hi.
  lia.
Qed.

Lemma BProv_HFFin_addFunctionalSentence :
  Completeness.BProv HFFinAx_s [] HF_addFunctionalSentence.
Proof.
  apply Completeness.completeness_inf.
  - exact Sentences_HFFin.
  - exact HF_addFunctionalSentence_sentence.
  - intros V mem v hHF.
    pose (M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s V mem v hHF).
    intros left right out1 out2 hrightOrd hgraph1 hgraph2.
    set (e := scons V out2 (scons V out1
      (scons V right (scons V left v)))).
    apply (addGraphAt_outputs_eq_finite_model V M e e
      1 0 3 3 2 2); try reflexivity.
    + exact (proj1 (HF_ordinalLikeAt_spec V (foam_mem V M) e 2)
        hrightOrd).
    + exact hgraph1.
    + exact hgraph2.
Qed.

Lemma translateHFFormula_addFunctionalSentence :
  translateHFFormula HF_addFunctionalSentence =
    pAll (pAll (pAll (pAll
      (pImp
        (addHFOrdinalLikeAt 2)
        (pImp
          (hfAddGraphAt 1 3 2)
          (pImp
            (hfAddGraphAt 0 3 2)
            (pEq (tVar 1) (tVar 0)))))))).
Proof.
  unfold HF_addFunctionalSentence, translateHFFormula,
    addHFOrdinalLikeAt, hfAddGraphAt.
  simpl.
  repeat rewrite hfUpVarMap_id.
  reflexivity.
Qed.

Lemma BProv_Ax_s_addFunctionalSentence : forall
    (P : TranslatedHFFinAxiomProofs),
  BProv Ax_s []
    (pAll (pAll (pAll (pAll
      (pImp
        (addHFOrdinalLikeAt 2)
        (pImp
          (hfAddGraphAt 1 3 2)
          (pImp
            (hfAddGraphAt 0 3 2)
            (pEq (tVar 1) (tVar 0))))))))).
Proof.
  intro P.
  rewrite <- translateHFFormula_addFunctionalSentence.
  exact (BProv_Ax_s_translateHFFin_theorem P _
    BProv_HFFin_addFunctionalSentence).
Qed.
