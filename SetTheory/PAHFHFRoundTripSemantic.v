(* ===================================================================== *)
(*  PAHFHFRoundTripSemantic.v                                            *)
(*                                                                       *)
(*  Semantic HF -> PA -> HF round trip.  Certified representations turn  *)
(*  the translated membership and equality atoms back into their raw HF  *)
(*  meanings; one formula induction then handles all connectives and      *)
(*  quantifiers.  Completeness converts that arbitrary-model equivalence  *)
(*  into the published deductive round-trip proof.                         *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Lia List.
From SetTheory Require Import Fol Calculus Completeness PAHF
  PAHFHFRoundTrip PAHFInterpretations PAHFHFRepresentationFinite
  PAHFDeductiveAssembly.
Import ListNotations.

(* Every represented code is in the translated PA domain. *)
Lemma ModelSetOrdinalRep_code_ordinal :
  forall (V : Type) (M : FirstOrderAdjunctionModel V) set code,
  ModelSetOrdinalRep M set code ->
    OrdinalLike (foam_mem V M) code.
Proof.
  intros V M set code [relation [hroot hcertificate]].
  exact (proj1 (proj2 hcertificate set code hroot)).
Qed.

(* Atomic membership correctness.  Functionality identifies the child code
   selected by the set certificate with the independently supplied element
   code; injectivity handles the converse range witness. *)
Lemma ModelSetOrdinalRep_mem_iff_composite :
  forall (V : Type) (M : FirstOrderAdjunctionModel V),
  ModelCompositeMemExtensionalLaw M ->
  forall elem set elemCode setCode,
  ModelSetOrdinalRep M elem elemCode ->
  ModelSetOrdinalRep M set setCode ->
    (foam_mem V M elem set <->
      ModelCompositeMem M elemCode setCode).
Proof.
  intros V M hext elem set elemCode setCode helem hset.
  pose proof
    (ModelSetOrdinalRepCodeFunctionalLaw_of_composite_extensionality
      V M hext) as hfunctional.
  pose proof (ModelSetOrdinalRepSetInjectiveLaw_of_induction V M)
    as hinjective.
  pose proof helem as helemRep.
  destruct hset as [relation [hsetRoot hcertificate]].
  pose proof (proj2 hcertificate set setCode hsetRoot) as hlocal.
  split.
  - intro hmem.
    destruct (proj1 (proj1 (proj2 hlocal) elem) hmem)
      as [childCode [hchildRoot hchildBit]].
    assert (hcodeEq : childCode = elemCode).
    {
      apply (hfunctional elem childCode elemCode).
      - exists relation. now split.
      - exact helemRep.
    }
    now rewrite <- hcodeEq.
  - intro hbit.
    pose proof (ModelSetOrdinalRep_code_ordinal
      V M elem elemCode helemRep) as helemCodeOrd.
    destruct (proj2 (proj2 hlocal) elemCode helemCodeOrd hbit)
      as [represented hrepresentedRoot].
    assert (hrepresentedMem : foam_mem V M represented set).
    {
      apply (proj2 (proj1 (proj2 hlocal) represented)).
      exists elemCode. now split.
    }
    assert (hsetEq : represented = elem).
    {
      apply (hinjective represented elem elemCode).
      - exists relation. now split.
      - exact helemRep.
    }
    now rewrite <- hsetEq.
Qed.

(* Atomic equality correctness is precisely the two uniqueness directions
   of the representation relation. *)
Lemma ModelSetOrdinalRep_eq_iff_code_eq :
  forall (V : Type) (M : FirstOrderAdjunctionModel V),
  ModelCompositeMemExtensionalLaw M ->
  forall left right leftCode rightCode,
  ModelSetOrdinalRep M left leftCode ->
  ModelSetOrdinalRep M right rightCode ->
    (left = right <-> leftCode = rightCode).
Proof.
  intros V M hext left right leftCode rightCode hleft hright.
  split.
  - intro hset. subst right.
    exact (ModelSetOrdinalRepCodeFunctionalLaw_of_composite_extensionality
      V M hext left leftCode rightCode hleft hright).
  - intro hcode. subst rightCode.
    exact (ModelSetOrdinalRepSetInjectiveLaw_of_induction
      V M left right leftCode hleft hright).
Qed.

(* Small normal forms used only by the semantic formula induction. *)
Lemma hfCompositeAt_mem : forall codedMap elem set,
  hfCompositeAt codedMap (fMem elem set) =
    HF_compositeMemAt (codedMap elem) (codedMap set).
Proof.
  intros codedMap elem set.
  change (formulaAt codedMap (PA.Formula.hfMemAt elem set) =
    formulaAt (repPairSlotMap (codedMap elem) (codedMap set))
      (PA.Formula.hfMemAt 0 1)).
  pose proof (PA.Formula.rename_hfMemAt
    (repPairSlotMap elem set) 0 1) as hrename.
  cbn [repPairSlotMap] in hrename.
  rewrite <- hrename.
  rewrite formulaAt_PA_rename.
  apply formulaAt_map_ext.
  intros [|n]; reflexivity.
Qed.

Lemma hfCompositeAt_all : forall codedMap phi,
  hfCompositeAt codedMap (fAll phi) =
    fAll (fImp domainForm
      (hfCompositeAt (upVarMap codedMap) phi)).
Proof.
  intros codedMap phi.
  unfold hfCompositeAt. simpl.
  rewrite (PA.Formula.hfFormulaAt_ext phi
    (PA.Formula.hfUpVarMap (fun n : nat => n))
    (fun n : nat => n)).
  - reflexivity.
  - intros [|n]; reflexivity.
Qed.

Lemma hfCompositeAt_ex : forall codedMap phi,
  hfCompositeAt codedMap (fEx phi) =
    fEx (fAnd domainForm
      (hfCompositeAt (upVarMap codedMap) phi)).
Proof.
  intros codedMap phi.
  unfold hfCompositeAt. simpl.
  rewrite (PA.Formula.hfFormulaAt_ext phi
    (PA.Formula.hfUpVarMap (fun n : nat => n))
    (fun n : nat => n)).
  - reflexivity.
  - intros [|n]; reflexivity.
Qed.

Lemma hfCompositeAt_mem_sat_iff_of_representations :
  forall (V : Type) (M : FirstOrderAdjunctionModel V),
  ModelCompositeMemExtensionalLaw M ->
  forall rawEnv codedEnv codedMap elem set,
  ModelSetOrdinalRep M (rawEnv elem)
    (codedEnv (codedMap elem)) ->
  ModelSetOrdinalRep M (rawEnv set)
    (codedEnv (codedMap set)) ->
    (Sat V (foam_mem V M) rawEnv (fMem elem set) <->
      Sat V (foam_mem V M) codedEnv
        (hfCompositeAt codedMap (fMem elem set))).
Proof.
  intros V M hext rawEnv codedEnv codedMap elem set helem hset.
  rewrite hfCompositeAt_mem.
  rewrite (HF_compositeMemAt_model V M codedEnv
    (codedMap elem) (codedMap set)).
  exact (ModelSetOrdinalRep_mem_iff_composite V M hext
    (rawEnv elem) (rawEnv set)
    (codedEnv (codedMap elem)) (codedEnv (codedMap set))
    helem hset).
Qed.

Lemma hfCompositeAt_eq_sat_iff_of_representations :
  forall (V : Type) (M : FirstOrderAdjunctionModel V),
  ModelCompositeMemExtensionalLaw M ->
  forall rawEnv codedEnv codedMap left right,
  ModelSetOrdinalRep M (rawEnv left)
    (codedEnv (codedMap left)) ->
  ModelSetOrdinalRep M (rawEnv right)
    (codedEnv (codedMap right)) ->
    (Sat V (foam_mem V M) rawEnv (fEq left right) <->
      Sat V (foam_mem V M) codedEnv
        (hfCompositeAt codedMap (fEq left right))).
Proof.
  intros V M hext rawEnv codedEnv codedMap left right hleft hright.
  change (rawEnv left = rawEnv right <->
    Sat V (foam_mem V M) codedEnv
      (formulaAt codedMap
        (PA.pEq (PA.tVar left) (PA.tVar right)))).
  rewrite (formulaAt_eq_var_spec V (foam_mem V M)
    codedMap left right codedEnv).
  exact (ModelSetOrdinalRep_eq_iff_code_eq V M hext
    (rawEnv left) (rawEnv right)
    (codedEnv (codedMap left)) (codedEnv (codedMap right))
    hleft hright).
Qed.

Definition ModelSetOrdinalRepTotalLaw {V : Type}
    (M : FirstOrderAdjunctionModel V) : Prop :=
  forall set, HasSetOrdinalRep M set.

Definition ModelSetOrdinalRepRangeLaw {V : Type}
    (M : FirstOrderAdjunctionModel V) : Prop :=
  forall code,
    OrdinalLike (foam_mem V M) code ->
      exists set, ModelSetOrdinalRep M set code.

(* The central semantic theorem.  Raw and coded variables may live in
   different environments.  Only genuinely free slots need representation
   witnesses, which makes the sentence endpoint immediate. *)
Lemma hfCompositeAt_sat_iff_of_representations :
  forall phi (V : Type) (M : FirstOrderAdjunctionModel V),
  ModelCompositeMemExtensionalLaw M ->
  ModelSetOrdinalRepTotalLaw M ->
  ModelSetOrdinalRepRangeLaw M ->
  forall (rawEnv codedEnv : nat -> V) (codedMap : nat -> nat),
  (forall n, Free n phi ->
    ModelSetOrdinalRep M (rawEnv n) (codedEnv (codedMap n))) ->
    (Sat V (foam_mem V M) rawEnv phi <->
      Sat V (foam_mem V M) codedEnv
        (hfCompositeAt codedMap phi)).
Proof.
  induction phi as [elem set | left right | | a IHa b IHb |
      a IHa b IHb | a IHa b IHb | a IHa | a IHa];
    intros V M hext htotal hrange rawEnv codedEnv codedMap hreps.
  - exact (hfCompositeAt_mem_sat_iff_of_representations
      V M hext rawEnv codedEnv codedMap elem set
      (hreps elem (or_introl eq_refl))
      (hreps set (or_intror eq_refl))).
  - exact (hfCompositeAt_eq_sat_iff_of_representations
      V M hext rawEnv codedEnv codedMap left right
      (hreps left (or_introl eq_refl))
      (hreps right (or_intror eq_refl))).
  - reflexivity.
  - cbn [Sat hfCompositeAt PA.Formula.hfFormulaAt formulaAt].
    pose proof (IHa V M hext htotal hrange rawEnv codedEnv codedMap
      (fun n hn => hreps n (or_introl hn))) as ha.
    pose proof (IHb V M hext htotal hrange rawEnv codedEnv codedMap
      (fun n hn => hreps n (or_intror hn))) as hb.
    tauto.
  - cbn [Sat hfCompositeAt PA.Formula.hfFormulaAt formulaAt].
    pose proof (IHa V M hext htotal hrange rawEnv codedEnv codedMap
      (fun n hn => hreps n (or_introl hn))) as ha.
    pose proof (IHb V M hext htotal hrange rawEnv codedEnv codedMap
      (fun n hn => hreps n (or_intror hn))) as hb.
    tauto.
  - cbn [Sat hfCompositeAt PA.Formula.hfFormulaAt formulaAt].
    pose proof (IHa V M hext htotal hrange rawEnv codedEnv codedMap
      (fun n hn => hreps n (or_introl hn))) as ha.
    pose proof (IHb V M hext htotal hrange rawEnv codedEnv codedMap
      (fun n hn => hreps n (or_intror hn))) as hb.
    tauto.
  - rewrite hfCompositeAt_all.
    cbn [Sat]. split.
    + intros hraw code hcodeDomain.
      pose proof (proj1 (HF_ordinalLikeAt_spec V (foam_mem V M)
        (scons V code codedEnv) 0) hcodeDomain) as hcodeOrd.
      destruct (hrange code hcodeOrd) as [raw hrep].
      assert (hrepsBody : forall n, Free n a ->
          ModelSetOrdinalRep M (scons V raw rawEnv n)
            (scons V code codedEnv (upVarMap codedMap n))).
      {
        intros [|n] hn; cbn [scons upVarMap].
        - exact hrep.
        - apply hreps. exact hn.
      }
      apply (proj1 (IHa V M hext htotal hrange
        (scons V raw rawEnv) (scons V code codedEnv)
        (upVarMap codedMap) hrepsBody)).
      exact (hraw raw).
    + intros hcoded raw.
      destruct (htotal raw) as [code hrep].
      pose proof (ModelSetOrdinalRep_code_ordinal
        V M raw code hrep) as hcodeOrd.
      assert (hrepsBody : forall n, Free n a ->
          ModelSetOrdinalRep M (scons V raw rawEnv n)
            (scons V code codedEnv (upVarMap codedMap n))).
      {
        intros [|n] hn; cbn [scons upVarMap].
        - exact hrep.
        - apply hreps. exact hn.
      }
      apply (proj2 (IHa V M hext htotal hrange
        (scons V raw rawEnv) (scons V code codedEnv)
        (upVarMap codedMap) hrepsBody)).
      apply (hcoded code).
      apply (proj2 (HF_ordinalLikeAt_spec V (foam_mem V M)
        (scons V code codedEnv) 0)).
      exact hcodeOrd.
  - rewrite hfCompositeAt_ex.
    cbn [Sat]. split.
    + intros [raw hraw].
      destruct (htotal raw) as [code hrep].
      exists code. split.
      * apply (proj2 (HF_ordinalLikeAt_spec V (foam_mem V M)
          (scons V code codedEnv) 0)).
        exact (ModelSetOrdinalRep_code_ordinal V M raw code hrep).
      * assert (hrepsBody : forall n, Free n a ->
            ModelSetOrdinalRep M (scons V raw rawEnv n)
              (scons V code codedEnv (upVarMap codedMap n))).
        {
          intros [|n] hn; cbn [scons upVarMap].
          - exact hrep.
          - apply hreps. exact hn.
        }
        apply (proj1 (IHa V M hext htotal hrange
          (scons V raw rawEnv) (scons V code codedEnv)
          (upVarMap codedMap) hrepsBody)).
        exact hraw.
    + intros [code [hcodeDomain hcoded]].
      pose proof (proj1 (HF_ordinalLikeAt_spec V (foam_mem V M)
        (scons V code codedEnv) 0) hcodeDomain) as hcodeOrd.
      destruct (hrange code hcodeOrd) as [raw hrep].
      exists raw.
      assert (hrepsBody : forall n, Free n a ->
          ModelSetOrdinalRep M (scons V raw rawEnv n)
            (scons V code codedEnv (upVarMap codedMap n))).
      {
        intros [|n] hn; cbn [scons upVarMap].
        - exact hrep.
        - apply hreps. exact hn.
      }
      apply (proj2 (IHa V M hext htotal hrange
        (scons V raw rawEnv) (scons V code codedEnv)
        (upVarMap codedMap) hrepsBody)).
      exact hcoded.
Qed.

Definition HFFinModelSetOrdinalRepTotalLaw : Prop :=
  forall (V : Type) (mem : V -> V -> Prop) (v : nat -> V)
    (hHF : forall g, HFFinAx_s g -> Sat V mem v g),
  let M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s V mem v hHF in
    ModelSetOrdinalRepTotalLaw (fofam_base V M).

Definition HFFinModelSetOrdinalRepRangeLaw : Prop :=
  forall (V : Type) (mem : V -> V -> Prop) (v : nat -> V)
    (hHF : forall g, HFFinAx_s g -> Sat V mem v g),
  let M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s V mem v hHF in
    ModelSetOrdinalRepRangeLaw (fofam_base V M).

Lemma HFFinModelSetOrdinalRepTotalLaw_of_translation :
  HFFinPAProofTranslation ->
  HFFinModelCompositeMemExtensionality ->
  HFFinModelCompositeAdjoinCode ->
    HFFinModelSetOrdinalRepTotalLaw.
Proof.
  intros htranslate hext hcode V mem v hHF.
  cbn.
  intro set.
  exact (HasSetOrdinalRep_total_of_HFFinAx_s_of_translation
    htranslate hext hcode V mem v hHF set).
Qed.

(* Completeness is used once, after the entire formula induction. *)
Lemma HFRoundTripProof_of_model_representation_laws :
  HFFinModelCompositeMemExtensionality ->
  HFFinModelSetOrdinalRepTotalLaw ->
  HFFinModelSetOrdinalRepRangeLaw ->
    HFRoundTripProof.
Proof.
  intros hext htotal hrange phi hphi.
  apply (completeness_inf_context HFFinAx_s []
    (fIff phi
      (translateFormula (PA.Formula.translateHFFormula phi)))
    Sentences_HFFin).
  intros V mem v hHF _hcontext.
  pose (M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s
    V mem v hHF).
  rewrite <- hfCompositeAt_id.
  cbn [Sat fIff].
  pose proof (hfCompositeAt_sat_iff_of_representations phi V
    (fofam_base V M) (hext V mem v hHF)
    (htotal V mem v hHF) (hrange V mem v hHF)
    v v (fun n : nat => n)
    (fun n hn => False_rect _ (hphi n hn))) as hsemantic.
  exact (conj (proj1 hsemantic) (proj2 hsemantic)).
Qed.

(* Current honest endpoint: totality is discharged by the preceding finite
   representation layer; ordinal-code range remains an explicit semantic
   arithmetic boundary. *)
Lemma HFRoundTripProof_of_translation_and_arithmetic :
  HFFinPAProofTranslation ->
  HFFinModelCompositeMemExtensionality ->
  HFFinModelCompositeAdjoinCode ->
  HFFinModelSetOrdinalRepRangeLaw ->
    HFRoundTripProof.
Proof.
  intros htranslate hext hcode hrange.
  exact (HFRoundTripProof_of_model_representation_laws
    hext
    (HFFinModelSetOrdinalRepTotalLaw_of_translation
      htranslate hext hcode)
    hrange).
Qed.
