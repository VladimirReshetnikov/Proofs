(* ===================================================================== *)
(*  PAHFHFRepresentationRange.v                                         *)
(*                                                                       *)
(*  Surjectivity of certified set representations onto ordinal-like      *)
(*  codes.  An outer HF induction supplies representations for smaller   *)
(*  ordinal positions; an inner finite-generation induction scans the     *)
(*  target code and accumulates exactly the Ackermann bits encountered.   *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Lia List Classical_Prop.
From SetTheory Require Import Fol PAHF PAHFHFRoundTrip
  PAHFInterpretations PAHFHFRepresentation PAHFHFRepresentationFinite
  PAHFDeductiveAssembly PAHFHFRoundTripSemantic.

(* The one arithmetic fact used by the range construction: on ordinal
   inputs, translated Ackermann membership is below ambient ordinal
   membership. *)
Definition ModelCompositeMemBelowLaw {V : Type}
    (M : FirstOrderFiniteAdjunctionModel V) : Prop :=
  forall elemCode setCode,
    OrdinalLike (foam_mem V M) elemCode ->
    OrdinalLike (foam_mem V M) setCode ->
    ModelCompositeMem (fofam_base V M) elemCode setCode ->
      foam_mem V M elemCode setCode.

Definition HFFinModelCompositeMemBelowLaw : Prop :=
  forall (V : Type) (mem : V -> V -> Prop) (v : nat -> V)
    (hHF : forall g, HFFinAx_s g -> Sat V mem v g),
  let M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s V mem v hHF in
    ModelCompositeMemBelowLaw M.

(* Slot 0 is the finite subset of code positions inspected so far and slot
   1 is the target code.  The witnesses are the accumulated raw set and its
   current Ackermann code. *)
Definition setOrdinalRangeAccumulator : form :=
  fEx (fEx
    (fAnd (HF_setOrdinalRepAt 1 0)
      (fAnd (HF_ordinalLikeAt 0)
        (fAll
          (fImp (HF_ordinalLikeAt 0)
            (fIff (HF_compositeMemAt 0 1)
              (fAnd (HF_compositeMemAt 0 4) (fMem 0 3)))))))).

Lemma setOrdinalRangeAccumulator_spec :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V)
    (env : nat -> V),
  Sat V (foam_mem V M) env setOrdinalRangeAccumulator <->
    exists raw code,
      ModelSetOrdinalRep (fofam_base V M) raw code /\
      OrdinalLike (foam_mem V M) code /\
      forall query,
        OrdinalLike (foam_mem V M) query ->
          (ModelCompositeMem (fofam_base V M) query code <->
            ModelCompositeMem (fofam_base V M) query (env 1) /\
            foam_mem V M query (env 0)).
Proof.
  intros V M env.
  unfold setOrdinalRangeAccumulator.
  cbn [Sat]. split.
  - intros [raw [code [hrepSat [hcodeSat hinvariantSat]]]].
    pose (E := scons V code (scons V raw env)).
    assert (hrep : ModelSetOrdinalRep (fofam_base V M) raw code).
    {
      apply (proj1 (HF_setOrdinalRepAt_model V (fofam_base V M)
        E 1 0)).
      exact hrepSat.
    }
    assert (hcode : OrdinalLike (foam_mem V M) code).
    {
      apply (proj1 (HF_ordinalLikeAt_spec V (foam_mem V M) E 0)).
      exact hcodeSat.
    }
    exists raw, code. split; [exact hrep |].
    split; [exact hcode |].
    intros query hquery.
    pose (Eq := scons V query E).
    assert (hquerySat : Sat V (foam_mem V M) Eq
        (HF_ordinalLikeAt 0)).
    {
      apply (proj2 (HF_ordinalLikeAt_spec V (foam_mem V M) Eq 0)).
      exact hquery.
    }
    pose proof (hinvariantSat query hquerySat) as hpoint.
    cbn [Sat fIff] in hpoint.
    change ((Sat V (foam_mem V M) Eq (HF_compositeMemAt 0 1) ->
      Sat V (foam_mem V M) Eq (HF_compositeMemAt 0 4) /\
        foam_mem V M (Eq 0) (Eq 3)) /\
      ((Sat V (foam_mem V M) Eq (HF_compositeMemAt 0 4) /\
        foam_mem V M (Eq 0) (Eq 3)) ->
       Sat V (foam_mem V M) Eq (HF_compositeMemAt 0 1))) in hpoint.
    rewrite (HF_compositeMemAt_model V (fofam_base V M) Eq 0 1)
      in hpoint.
    rewrite (HF_compositeMemAt_model V (fofam_base V M) Eq 0 4)
      in hpoint.
    cbn [E Eq scons] in hpoint.
    split; [exact (proj1 hpoint) | exact (proj2 hpoint)].
  - intros [raw [code [hrep [hcode hinvariant]]]].
    pose (E := scons V code (scons V raw env)).
    exists raw, code. split.
    + apply (proj2 (HF_setOrdinalRepAt_model V (fofam_base V M)
        E 1 0)).
      exact hrep.
    + split.
      * apply (proj2 (HF_ordinalLikeAt_spec V (foam_mem V M) E 0)).
        exact hcode.
      * intros query hquerySat.
        pose (Eq := scons V query E).
        assert (hquery : OrdinalLike (foam_mem V M) query).
        {
          apply (proj1 (HF_ordinalLikeAt_spec V (foam_mem V M) Eq 0)).
          exact hquerySat.
        }
        cbn [Sat fIff].
        change ((Sat V (foam_mem V M) Eq (HF_compositeMemAt 0 1) ->
          Sat V (foam_mem V M) Eq (HF_compositeMemAt 0 4) /\
            foam_mem V M (Eq 0) (Eq 3)) /\
          ((Sat V (foam_mem V M) Eq (HF_compositeMemAt 0 4) /\
            foam_mem V M (Eq 0) (Eq 3)) ->
           Sat V (foam_mem V M) Eq (HF_compositeMemAt 0 1))).
        rewrite (HF_compositeMemAt_model V (fofam_base V M) Eq 0 1).
        rewrite (HF_compositeMemAt_model V (fofam_base V M) Eq 0 4).
        cbn [E Eq scons].
        split.
        -- exact (proj1 (hinvariant query hquery)).
        -- exact (proj2 (hinvariant query hquery)).
Qed.

Lemma ModelSetOrdinalRepRangeLaw_of_empty_below :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V),
  ModelSetOrdinalRep (fofam_base V M)
    (foam_empty V M) (foam_empty V M) ->
  ModelCompositeMemBelowLaw M ->
  ModelCompositeMemExtensionalLaw (fofam_base V M) ->
  ModelCompositeAdjoinCodeLaw (fofam_base V M) ->
    ModelSetOrdinalRepRangeLaw (fofam_base V M).
Proof.
  intros V M hempty hbelow hext hcode.
  pose (N := fofam_base V M).
  pose (rangeForm :=
    fImp (HF_ordinalLikeAt 0) (fEx (HF_setOrdinalRepAt 0 1))).
  pose (tail := fun _ : nat => foam_empty V M).
  pose proof (foam_induction_schema V N rangeForm tail) as houter.
  assert (hall : forall code,
      Sat V (foam_mem V M) (scons V code tail) rangeForm).
  {
    apply houter.
    intros code hmembers hcodeSat.
    pose proof (proj1 (HF_ordinalLikeAt_spec V (foam_mem V M)
      (scons V code tail) 0) hcodeSat) as hcodeOrd.
    pose (codeEnv := scons V code tail).
    pose (subsetAccumulator :=
      fImp (HF_subsetAt 0 1) setOrdinalRangeAccumulator).
    pose proof (fofam_finite_induction_schema V M
      subsetAccumulator codeEnv) as hfinite.
    assert (hsubsets : forall current,
        Sat V (foam_mem V M) (scons V current codeEnv)
          subsetAccumulator).
    {
      apply (proj1 (HF_finite_induction_form_spec V
        (foam_mem V M) subsetAccumulator codeEnv) hfinite).
      split.
      - intros emptyLike hemptyLike _hsubset.
        assert (hemptyEq : emptyLike = foam_empty V M).
        {
          apply (foam_extensional V N emptyLike (foam_empty V M)).
          intro x. split.
          - intro hx. exfalso. exact (hemptyLike x hx).
          - intro hx. exfalso. exact (foam_empty_spec V N x hx).
        }
        subst emptyLike.
        pose proof hempty as hempty'.
        destruct hempty' as
          [emptyRelation [hemptyRoot hemptyCertificate]].
        pose proof (proj2 hemptyCertificate
          (foam_empty V M) (foam_empty V M) hemptyRoot)
          as hemptyLocal.
        apply (proj2 (setOrdinalRangeAccumulator_spec V M
          (scons V (foam_empty V M) codeEnv))).
        exists (foam_empty V M), (foam_empty V M).
        split; [exact hempty |].
        split; [apply foam_OrdinalLike_empty |].
        intros query hquery. split.
        + intro hqueryEmpty.
          destruct (proj2 (proj2 hemptyLocal) query hquery hqueryEmpty)
            as [represented hrepresentedRoot].
          assert (hrepresentedEmpty :
              foam_mem V M represented (foam_empty V M)).
          {
            apply (proj2 (proj1 (proj2 hemptyLocal) represented)).
            exists query. now split.
          }
          exfalso.
          exact (foam_empty_spec V N represented hrepresentedEmpty).
        + intros [_hqueryCode hqueryEmpty].
          exfalso.
          exact (foam_empty_spec V N query hqueryEmpty).
      - intros old elem newCurrent hcurrentAdjoin hOld
          hnewSubsetSat.
        pose proof (proj1 (HF_subsetAt_spec V (foam_mem V M)
          (scons V newCurrent codeEnv) 0 1) hnewSubsetSat)
          as hnewSubset.
        assert (holdSubset : forall x,
            foam_mem V M x old -> foam_mem V M x code).
        {
          intros x hxold.
          apply hnewSubset.
          apply (proj2 (hcurrentAdjoin x)). now left.
        }
        assert (holdSubsetSat : Sat V (foam_mem V M)
            (scons V old codeEnv) (HF_subsetAt 0 1)).
        {
          apply (proj2 (HF_subsetAt_spec V (foam_mem V M)
            (scons V old codeEnv) 0 1)).
          exact holdSubset.
        }
        pose proof (hOld holdSubsetSat) as hOldAccumulatorSat.
        destruct (proj1 (setOrdinalRangeAccumulator_spec V M
          (scons V old codeEnv)) hOldAccumulatorSat)
          as [oldRaw [oldCode [holdRep [holdCodeOrd holdInvariant]]]].
        assert (helemCode : foam_mem V M elem code).
        {
          apply hnewSubset.
          apply (proj2 (hcurrentAdjoin elem)). now right.
        }
        pose proof (OrdinalLike_of_mem V (foam_mem V M)
          code elem hcodeOrd helemCode) as helemCodeOrd.
        destruct (classic
          (ModelCompositeMem N elem code)) as [helemBit | helemNotBit].
        + pose proof (proj1 (Sat_rename_rSkipParam V (foam_mem V M)
            rangeForm tail code elem)
            (hmembers elem helemCode)) as helemOuter.
          assert (helemOrdSat : Sat V (foam_mem V M)
              (scons V elem tail) (HF_ordinalLikeAt 0)).
          {
            apply (proj2 (HF_ordinalLikeAt_spec V (foam_mem V M)
              (scons V elem tail) 0)).
            exact helemCodeOrd.
          }
          destruct (helemOuter helemOrdSat) as [elemRaw helemRepSat].
          assert (helemRep : ModelSetOrdinalRep N elemRaw elem).
          {
            apply (proj1 (HF_setOrdinalRepAt_model V N
              (scons V elemRaw (scons V elem tail)) 0 1)).
            exact helemRepSat.
          }
          destruct (hcode oldCode elem holdCodeOrd helemCodeOrd)
            as [newCode C].
          pose (newRaw := foam_adjoin V N oldRaw elemRaw).
          assert (hrawAdjoin : forall x,
              foam_mem V M x newRaw <->
                foam_mem V M x oldRaw \/ x = elemRaw).
          {
            intro x. unfold newRaw.
            apply foam_adjoin_spec.
          }
          assert (hnewRep : ModelSetOrdinalRep N newRaw newCode).
          {
            exact (ModelSetOrdinalRep_adjoin_exact_finite V M hext
              oldRaw oldCode elemRaw elem newRaw newCode
              hrawAdjoin holdRep helemRep C).
          }
          apply (proj2 (setOrdinalRangeAccumulator_spec V M
            (scons V newCurrent codeEnv))).
          exists newRaw, newCode.
          split; [exact hnewRep |].
          split; [exact (composite_adjoin_newCode_ordinal C) |].
          intros query hquery. split.
          -- intro hqueryNew.
             destruct (proj1 (composite_adjoin_code C query hquery)
               hqueryNew) as [hqueryOldCode | hqueryElem].
             ++ destruct (proj1 (holdInvariant query hquery)
                  hqueryOldCode) as [hqueryTarget hqueryOld].
                split; [exact hqueryTarget |].
                apply (proj2 (hcurrentAdjoin query)).
                now left.
             ++ subst query.
                split; [exact helemBit |].
                apply (proj2 (hcurrentAdjoin elem)).
                now right.
          -- intros [hqueryTarget hqueryCurrent].
             apply (proj2 (composite_adjoin_code C query hquery)).
             destruct (proj1 (hcurrentAdjoin query) hqueryCurrent)
               as [hqueryOld | hqueryElem].
             ++ left.
                apply (proj2 (holdInvariant query hquery)).
                now split.
             ++ right. exact hqueryElem.
        + apply (proj2 (setOrdinalRangeAccumulator_spec V M
            (scons V newCurrent codeEnv))).
          exists oldRaw, oldCode.
          split; [exact holdRep |].
          split; [exact holdCodeOrd |].
          intros query hquery. split.
          -- intro hqueryOldCode.
             destruct (proj1 (holdInvariant query hquery)
               hqueryOldCode) as [hqueryTarget hqueryOld].
             split; [exact hqueryTarget |].
             apply (proj2 (hcurrentAdjoin query)).
             now left.
          -- intros [hqueryTarget hqueryCurrent].
             apply (proj2 (holdInvariant query hquery)).
             split; [exact hqueryTarget |].
             destruct (proj1 (hcurrentAdjoin query) hqueryCurrent)
               as [hqueryOld | hqueryElem].
             ++ exact hqueryOld.
             ++ subst query. exfalso. exact (helemNotBit hqueryTarget).
    }
    pose proof (hsubsets code) as hfinal.
    assert (hselfSubsetSat : Sat V (foam_mem V M)
        (scons V code codeEnv) (HF_subsetAt 0 1)).
    {
      apply (proj2 (HF_subsetAt_spec V (foam_mem V M)
        (scons V code codeEnv) 0 1)).
      intros x hx. exact hx.
    }
    pose proof (hfinal hselfSubsetSat) as hfinalAccumulatorSat.
    destruct (proj1 (setOrdinalRangeAccumulator_spec V M
      (scons V code codeEnv)) hfinalAccumulatorSat)
      as [raw [accumulatedCode
        [hrep [haccumulatedOrd hinvariant]]]].
    assert (hcodeEq : accumulatedCode = code).
    {
      apply (hext accumulatedCode code haccumulatedOrd hcodeOrd).
      intros query hquery. split.
      - intro hqueryAccumulated.
        exact (proj1 (proj1 (hinvariant query hquery)
          hqueryAccumulated)).
      - intro hqueryCode.
        apply (proj2 (hinvariant query hquery)).
        split; [exact hqueryCode |].
        exact (hbelow query code hquery hcodeOrd hqueryCode).
    }
    exists raw.
    apply (proj2 (HF_setOrdinalRepAt_model V N
      (scons V raw (scons V code tail)) 0 1)).
    now rewrite <- hcodeEq.
  }
  intros target htarget.
  assert (htargetSat : Sat V (foam_mem V M)
      (scons V target tail) (HF_ordinalLikeAt 0)).
  {
    apply (proj2 (HF_ordinalLikeAt_spec V (foam_mem V M)
      (scons V target tail) 0)).
    exact htarget.
  }
  destruct (hall target htargetSat) as [set hrepSat].
  exists set.
  apply (proj1 (HF_setOrdinalRepAt_model V N
    (scons V set (scons V target tail)) 0 1)).
  exact hrepSat.
Qed.

Lemma HFFinModelSetOrdinalRepRangeLaw_of_translation_and_arithmetic :
  HFFinPAProofTranslation ->
  HFFinModelCompositeMemExtensionality ->
  HFFinModelCompositeAdjoinCode ->
  HFFinModelCompositeMemBelowLaw ->
    HFFinModelSetOrdinalRepRangeLaw.
Proof.
  intros htranslate hext hcode hbelow V mem v hHF.
  cbn.
  pose (M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s
    V mem v hHF).
  change (ModelSetOrdinalRepRangeLaw (fofam_base V M)).
  apply (ModelSetOrdinalRepRangeLaw_of_empty_below V M).
  - exact (ModelSetOrdinalRep_empty_of_HFFinAx_s_of_translation
      htranslate V mem v hHF).
  - exact (hbelow V mem v hHF).
  - exact (hext V mem v hHF).
  - exact (hcode V mem v hHF).
Qed.

(* The HF round trip now depends on no representation-theoretic residual.
   Only the explicit arithmetic boundedness law remains beyond the three
   inputs already isolated by representation totality. *)
Lemma HFRoundTripProof_of_translation_and_composite_arithmetic :
  HFFinPAProofTranslation ->
  HFFinModelCompositeMemExtensionality ->
  HFFinModelCompositeAdjoinCode ->
  HFFinModelCompositeMemBelowLaw ->
    HFRoundTripProof.
Proof.
  intros htranslate hext hcode hbelow.
  apply (HFRoundTripProof_of_translation_and_arithmetic
    htranslate hext hcode).
  exact (HFFinModelSetOrdinalRepRangeLaw_of_translation_and_arithmetic
    htranslate hext hcode hbelow).
Qed.
