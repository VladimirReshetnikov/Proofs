(* ===================================================================== *)
(*  PAHFHFRepresentationFinite.v                                        *)
(*                                                                       *)
(*  Finite-model closure of certified HF-to-ordinal representations.     *)
(*  The representation semantics developed in PAHFHFRoundTrip is         *)
(*  environment-independent, so the recursive uniqueness arguments can   *)
(*  be stated directly at the model level.                               *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Lia List Classical_Prop.
From FirstOrder Require Import Fol Calculus Completeness.
From PAHF Require Import PAHF PAHFHFRoundTrip
  PAHFInterpretations PAHFHFRepresentation PAHFHFRepresentationMerge.

Definition ModelSetOrdinalRepCodeFunctionalLaw {V : Type}
    (M : FirstOrderAdjunctionModel V) : Prop :=
  forall set code1 code2,
    ModelSetOrdinalRep M set code1 ->
    ModelSetOrdinalRep M set code2 ->
      code1 = code2.

Definition ModelSetOrdinalRepSetInjectiveLaw {V : Type}
    (M : FirstOrderAdjunctionModel V) : Prop :=
  forall set1 set2 code,
    ModelSetOrdinalRep M set1 code ->
    ModelSetOrdinalRep M set2 code ->
      set1 = set2.

Lemma ModelSetOrdinalRepRelationsCompatibilityLaw_of_uniqueness :
  forall (V : Type) (M : FirstOrderAdjunctionModel V),
  ModelSetOrdinalRepCodeFunctionalLaw M ->
  ModelSetOrdinalRepSetInjectiveLaw M ->
    ModelSetOrdinalRepRelationsCompatibilityLaw M.
Proof.
  intros V M hfunctional hinjective left right hleft hright.
  assert (eitherRep : forall set code,
      (foam_mem V M (foam_kpair_obj V M set code) left \/
       foam_mem V M (foam_kpair_obj V M set code) right) ->
        ModelSetOrdinalRep M set code).
  {
    intros set code [hroot | hroot].
    - exists left. now split.
    - exists right. now split.
  }
  split.
  - intros set leftCode rightCode hleftRoot hrightRoot.
    exact (hfunctional set leftCode rightCode
      (eitherRep set leftCode (or_introl hleftRoot))
      (eitherRep set rightCode (or_intror hrightRoot))).
  - intros leftSet rightSet code hleftSet hrightSet.
    exact (hinjective leftSet rightSet code
      (eitherRep leftSet code hleftSet)
      (eitherRep rightSet code hrightSet)).
Qed.

Lemma ModelSetOrdinalRepMergeLaw_iff_uniqueness :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V),
  ModelSetOrdinalRepMergeLaw (fofam_base V M) <->
    ModelSetOrdinalRepCodeFunctionalLaw (fofam_base V M) /\
    ModelSetOrdinalRepSetInjectiveLaw (fofam_base V M).
Proof.
  intros V M.
  split.
  - intro hmerge. split.
    + intros set code1 code2 h1 h2.
      exact (ModelSetOrdinalRep_code_eq_of_mergeLaw V
        (fofam_base V M) hmerge set code1 code2 h1 h2).
    + intros set1 set2 code h1 h2.
      exact (ModelSetOrdinalRep_set_eq_of_mergeLaw V
        (fofam_base V M) hmerge set1 set2 code h1 h2).
  - intros [hfunctional hinjective].
    apply ModelSetOrdinalRepMergeLaw_of_finite_compatibility.
    exact (ModelSetOrdinalRepRelationsCompatibilityLaw_of_uniqueness
      V (fofam_base V M) hfunctional hinjective).
Qed.

(* Set injectivity is purely structural: induction on the first represented
   set recursively identifies the elements attached to a common child code. *)
Lemma ModelSetOrdinalRepSetInjectiveLaw_of_induction :
  forall (V : Type) (M : FirstOrderAdjunctionModel V),
    ModelSetOrdinalRepSetInjectiveLaw M.
Proof.
  intros V M.
  pose (phi :=
    fAll (fAll
      (fImp (HF_setOrdinalRepAt 2 0)
        (fImp (HF_setOrdinalRepAt 1 0) (fEq 2 1))))).
  pose (tail := fun _ : nat => foam_empty V M).
  pose proof (foam_induction_schema V M phi tail) as hind.
  assert (hall : forall set1,
      Sat V (foam_mem V M) (scons V set1 tail) phi).
  {
    apply hind.
    intros set1 ih set2 code hrep1Sat hrep2Sat.
    pose (E := scons V code (scons V set2 (scons V set1 tail))).
    assert (hrep1 : ModelSetOrdinalRep M set1 code).
    {
      apply (proj1 (HF_setOrdinalRepAt_model V M E 2 0)).
      exact hrep1Sat.
    }
    assert (hrep2 : ModelSetOrdinalRep M set2 code).
    {
      apply (proj1 (HF_setOrdinalRepAt_model V M E 1 0)).
      exact hrep2Sat.
    }
    destruct hrep1 as [relation1 [hroot1 hcert1]].
    destruct hrep2 as [relation2 [hroot2 hcert2]].
    pose proof (proj2 hcert1 set1 code hroot1) as hlocal1.
    pose proof (proj2 hcert2 set2 code hroot2) as hlocal2.
    assert (childSetEq : forall child other childCode,
      foam_mem V M child set1 ->
      foam_mem V M (foam_kpair_obj V M child childCode) relation1 ->
      foam_mem V M (foam_kpair_obj V M other childCode) relation2 ->
        child = other).
    {
      intros child other childCode hchild hchildRoot1 hotherRoot2.
      pose proof (proj1 (Sat_rename_rSkipParam V (foam_mem V M)
        phi tail set1 child) (ih child hchild)) as hchildIH.
      pose (EI :=
        scons V childCode (scons V other (scons V child tail))).
      assert (hchildRepSat : Sat V (foam_mem V M) EI
          (HF_setOrdinalRepAt 2 0)).
      {
        apply (proj2 (HF_setOrdinalRepAt_model V M EI 2 0)).
        exists relation1. now split.
      }
      assert (hotherRepSat : Sat V (foam_mem V M) EI
          (HF_setOrdinalRepAt 1 0)).
      {
        apply (proj2 (HF_setOrdinalRepAt_model V M EI 1 0)).
        exists relation2. now split.
      }
      exact (hchildIH other childCode hchildRepSat hotherRepSat).
    }
    apply (foam_extensional V M set1 set2).
    intro member. split.
    - intro hmember1.
      destruct (proj1 (proj1 (proj2 hlocal1) member) hmember1)
        as [memberCode [hmemberRoot1 hcoded]].
      pose proof (proj1 (proj2 hcert1 member memberCode
        hmemberRoot1)) as hmemberCodeOrd.
      destruct (proj2 (proj2 hlocal2) memberCode
        hmemberCodeOrd hcoded) as [other hotherRoot2].
      assert (hother2 : foam_mem V M other set2).
      {
        apply (proj2 (proj1 (proj2 hlocal2) other)).
        exists memberCode. now split.
      }
      pose proof (childSetEq member other memberCode
        hmember1 hmemberRoot1 hotherRoot2) as heq.
      now rewrite <- heq in hother2.
    - intro hmember2.
      destruct (proj1 (proj1 (proj2 hlocal2) member) hmember2)
        as [memberCode [hmemberRoot2 hcoded]].
      pose proof (proj1 (proj2 hcert2 member memberCode
        hmemberRoot2)) as hmemberCodeOrd.
      destruct (proj2 (proj2 hlocal1) memberCode
        hmemberCodeOrd hcoded) as [other hotherRoot1].
      assert (hother1 : foam_mem V M other set1).
      {
        apply (proj2 (proj1 (proj2 hlocal1) other)).
        exists memberCode. now split.
      }
      pose proof (childSetEq other member memberCode
        hother1 hotherRoot1 hmemberRoot2) as heq.
      now rewrite heq in hother1.
  }
  intros set1 set2 code hrep1 hrep2.
  pose proof (hall set1) as hmain.
  apply (hmain set2 code).
  - apply (proj2 (HF_setOrdinalRepAt_model V M
      (scons V code (scons V set2 (scons V set1 tail))) 2 0)).
    exact hrep1.
  - apply (proj2 (HF_setOrdinalRepAt_model V M
      (scons V code (scons V set2 (scons V set1 tail))) 1 0)).
    exact hrep2.
Qed.

Definition ModelCompositeMemExtensionalLaw {V : Type}
    (M : FirstOrderAdjunctionModel V) : Prop :=
  forall left right,
    OrdinalLike (foam_mem V M) left ->
    OrdinalLike (foam_mem V M) right ->
    (forall query, OrdinalLike (foam_mem V M) query ->
      (ModelCompositeMem M query left <->
       ModelCompositeMem M query right)) ->
      left = right.

(* Ackermann extensionality supplies the only arithmetic ingredient.  The
   recursive proof again uses only environment-independent certificates. *)
Lemma ModelSetOrdinalRepCodeFunctionalLaw_of_composite_extensionality :
  forall (V : Type) (M : FirstOrderAdjunctionModel V),
  ModelCompositeMemExtensionalLaw M ->
    ModelSetOrdinalRepCodeFunctionalLaw M.
Proof.
  intros V M hext.
  pose (phi :=
    fAll (fAll
      (fImp (HF_setOrdinalRepAt 2 1)
        (fImp (HF_setOrdinalRepAt 2 0) (fEq 1 0))))).
  pose (tail := fun _ : nat => foam_empty V M).
  pose proof (foam_induction_schema V M phi tail) as hind.
  assert (hall : forall set,
      Sat V (foam_mem V M) (scons V set tail) phi).
  {
    apply hind.
    intros set ih code1 code2 hrep1Sat hrep2Sat.
    pose (E := scons V code2 (scons V code1 (scons V set tail))).
    assert (hrep1 : ModelSetOrdinalRep M set code1).
    {
      apply (proj1 (HF_setOrdinalRepAt_model V M E 2 1)).
      exact hrep1Sat.
    }
    assert (hrep2 : ModelSetOrdinalRep M set code2).
    {
      apply (proj1 (HF_setOrdinalRepAt_model V M E 2 0)).
      exact hrep2Sat.
    }
    destruct hrep1 as [relation1 [hroot1 hcert1]].
    destruct hrep2 as [relation2 [hroot2 hcert2]].
    pose proof (proj2 hcert1 set code1 hroot1) as hlocal1.
    pose proof (proj2 hcert2 set code2 hroot2) as hlocal2.
    assert (childCodeEq : forall member leftCode rightCode,
      foam_mem V M member set ->
      foam_mem V M (foam_kpair_obj V M member leftCode) relation1 ->
      foam_mem V M (foam_kpair_obj V M member rightCode) relation2 ->
        leftCode = rightCode).
    {
      intros member leftCode rightCode hmember hleftRoot hrightRoot.
      pose proof (proj1 (Sat_rename_rSkipParam V (foam_mem V M)
        phi tail set member) (ih member hmember)) as hmemberIH.
      pose (EI :=
        scons V rightCode (scons V leftCode (scons V member tail))).
      assert (hleftRepSat : Sat V (foam_mem V M) EI
          (HF_setOrdinalRepAt 2 1)).
      {
        apply (proj2 (HF_setOrdinalRepAt_model V M EI 2 1)).
        exists relation1. now split.
      }
      assert (hrightRepSat : Sat V (foam_mem V M) EI
          (HF_setOrdinalRepAt 2 0)).
      {
        apply (proj2 (HF_setOrdinalRepAt_model V M EI 2 0)).
        exists relation2. now split.
      }
      pose proof (hmemberIH leftCode rightCode
        hleftRepSat hrightRepSat) as heq.
      cbn [scons] in heq.
      exact heq.
    }
    apply (hext code1 code2 (proj1 hlocal1) (proj1 hlocal2)).
    intro query. intro hqueryOrd. split.
    - intro hcoded1.
      destruct (proj2 (proj2 hlocal1) query hqueryOrd hcoded1)
        as [member hmemberRoot1].
      assert (hmember : foam_mem V M member set).
      {
        apply (proj2 (proj1 (proj2 hlocal1) member)).
        exists query. now split.
      }
      destruct (proj1 (proj1 (proj2 hlocal2) member) hmember)
        as [otherCode [hmemberRoot2 hcoded2]].
      pose proof (childCodeEq member query otherCode
        hmember hmemberRoot1 hmemberRoot2) as heq.
      now rewrite heq.
    - intro hcoded2.
      destruct (proj2 (proj2 hlocal2) query hqueryOrd hcoded2)
        as [member hmemberRoot2].
      assert (hmember : foam_mem V M member set).
      {
        apply (proj2 (proj1 (proj2 hlocal2) member)).
        exists query. now split.
      }
      destruct (proj1 (proj1 (proj2 hlocal1) member) hmember)
        as [otherCode [hmemberRoot1 hcoded1]].
      pose proof (childCodeEq member otherCode query
        hmember hmemberRoot1 hmemberRoot2) as heq.
      now rewrite heq in hcoded1.
  }
  intros set code1 code2 hrep1 hrep2.
  pose proof (hall set) as hmain.
  apply (hmain code1 code2).
  - apply (proj2 (HF_setOrdinalRepAt_model V M
      (scons V code2 (scons V code1 (scons V set tail))) 2 1)).
    exact hrep1.
  - apply (proj2 (HF_setOrdinalRepAt_model V M
      (scons V code2 (scons V code1 (scons V set tail))) 2 0)).
    exact hrep2.
Qed.

Lemma ModelSetOrdinalRepMergeLaw_of_composite_extensionality :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V),
  ModelCompositeMemExtensionalLaw (fofam_base V M) ->
    ModelSetOrdinalRepMergeLaw (fofam_base V M).
Proof.
  intros V M hext.
  apply (proj2 (ModelSetOrdinalRepMergeLaw_iff_uniqueness V M)).
  split.
  - exact (ModelSetOrdinalRepCodeFunctionalLaw_of_composite_extensionality
      V (fofam_base V M) hext).
  - exact (ModelSetOrdinalRepSetInjectiveLaw_of_induction
      V (fofam_base V M)).
Qed.

(* The graph-independent arithmetic datum for adjoining one Ackermann code
   to another.  Unlike [ModelSetOrdinalRepAdjoinData], it deliberately has
   no freshness or representation-graph premises. *)
Record ModelCompositeAdjoinCodeData {V : Type}
    (M : FirstOrderAdjunctionModel V)
    (oldCode elemCode newCode : V) : Prop := {
  composite_adjoin_newCode_ordinal :
    OrdinalLike (foam_mem V M) newCode;
  composite_adjoin_code : forall query,
    OrdinalLike (foam_mem V M) query ->
      (ModelCompositeMem M query newCode <->
       ModelCompositeMem M query oldCode \/ query = elemCode)
}.

Arguments composite_adjoin_newCode_ordinal
  {V M oldCode elemCode newCode} _.
Arguments composite_adjoin_code
  {V M oldCode elemCode newCode} _ _ _.

(* A root carrying the arithmetic adjunction code necessarily denotes the
   ambient-HF adjunction of the two represented roots. *)
Lemma ModelSetOrdinalRep_root_eq_of_adjoin_code :
  forall (V : Type) (M : FirstOrderAdjunctionModel V)
    old oldCode elem elemCode newSet newCode represented,
  forall (R : ModelSetOrdinalRepMergeResult M
      old oldCode elem elemCode),
  (forall x, foam_mem V M x newSet <->
    foam_mem V M x old \/ x = elem) ->
  ModelCompositeAdjoinCodeData M oldCode elemCode newCode ->
  foam_mem V M (foam_kpair_obj V M represented newCode)
    (merge_relation R) ->
    represented = newSet.
Proof.
  intros V M old oldCode elem elemCode newSet newCode represented
    R hnew C hrepresented.
  pose proof (proj2 (merge_certificate R)
    represented newCode hrepresented) as hrepresentedLocal.
  pose proof (proj2 (merge_certificate R)
    old oldCode (merge_old_root R)) as holdLocal.
  pose proof (proj2 (merge_certificate R)
    elem elemCode (merge_elem_root R)) as helemLocal.
  apply (foam_extensional V M represented newSet).
  intro x. split.
  - intro hx.
    destruct (proj1 (proj1 (proj2 hrepresentedLocal) x) hx)
      as [xCode [hxroot hxnew]].
    pose proof (proj1 (proj2 (merge_certificate R)
      x xCode hxroot)) as hxCodeOrd.
    apply (proj2 (hnew x)).
    destruct (proj1 (composite_adjoin_code C xCode hxCodeOrd) hxnew)
      as [hxold | hxelem].
    + left.
      apply (proj2 (proj1 (proj2 holdLocal) x)).
      exists xCode. now split.
    + right.
      subst xCode.
      apply (merge_code_injective R x elem elemCode).
      * exact hxroot.
      * exact (merge_elem_root R).
  - intro hx.
    apply (proj2 (proj1 (proj2 hrepresentedLocal) x)).
    destruct (proj1 (hnew x) hx) as [hxold | hxelem].
    + destruct (proj1 (proj1 (proj2 holdLocal) x) hxold)
        as [xCode [hxroot hxcoded]].
      pose proof (proj1 (proj2 (merge_certificate R)
        x xCode hxroot)) as hxCodeOrd.
      exists xCode. split; [exact hxroot |].
      apply (proj2 (composite_adjoin_code C xCode hxCodeOrd)).
      now left.
    + subst x.
      exists elemCode. split; [exact (merge_elem_root R) |].
      apply (proj2 (composite_adjoin_code C elemCode
        (proj1 helemLocal))).
      now right.
Qed.

(* If the merged graph already represents [newSet], reuse that root.  If it
   does not, the arithmetic adjunction law itself forces every freshness
   clause required by the certified graph-extension theorem. *)
Lemma ModelSetOrdinalRep_adjoin_of_merge_arithmetic :
  forall (V : Type) (M : FirstOrderAdjunctionModel V)
    old oldCode elem elemCode newSet newCode,
  forall (R : ModelSetOrdinalRepMergeResult M
      old oldCode elem elemCode),
  (forall x, foam_mem V M x newSet <->
    foam_mem V M x old \/ x = elem) ->
  ModelCompositeAdjoinCodeData M oldCode elemCode newCode ->
    exists code, ModelSetOrdinalRep M newSet code.
Proof.
  intros V M old oldCode elem elemCode newSet newCode R hnew C.
  destruct (classic (exists code,
      foam_mem V M (foam_kpair_obj V M newSet code)
        (merge_relation R))) as [hexisting | hmissing].
  - destruct hexisting as [code hroot].
    exists code, (merge_relation R).
    now split; [| exact (merge_certificate R)].
  - assert (hrootEq : forall represented,
      foam_mem V M (foam_kpair_obj V M represented newCode)
        (merge_relation R) -> represented = newSet).
    {
      intros represented hrepresented.
      exact (ModelSetOrdinalRep_root_eq_of_adjoin_code V M
        old oldCode elem elemCode newSet newCode represented
        R hnew C hrepresented).
    }
    assert (hnotOldMember : forall set code,
      foam_mem V M (foam_kpair_obj V M set code)
        (merge_relation R) ->
      ~ ModelCompositeMem M newCode code).
    {
      intros represented code hroot hcoded.
      pose proof (proj2 (merge_certificate R)
        represented code hroot) as hlocal.
      destruct (proj2 (proj2 hlocal) newCode
        (composite_adjoin_newCode_ordinal C) hcoded)
        as [represented' hrepresented'].
      pose proof (hrootEq represented' hrepresented') as heq.
      subst represented'.
      apply hmissing. exists newCode. exact hrepresented'.
    }
    assert (hirrefl : ~ ModelCompositeMem M newCode newCode).
    {
      intro hself.
      destruct (proj1 (composite_adjoin_code C newCode
        (composite_adjoin_newCode_ordinal C)) hself)
        as [holdBit | helemEq].
      - pose proof (proj2 (merge_certificate R)
          old oldCode (merge_old_root R)) as holdLocal.
        destruct (proj2 (proj2 holdLocal) newCode
          (composite_adjoin_newCode_ordinal C) holdBit)
          as [represented hrepresented].
        pose proof (hrootEq represented hrepresented) as heq.
        subst represented.
        apply hmissing. exists newCode. exact hrepresented.
      - assert (hrepresented :
          foam_mem V M (foam_kpair_obj V M elem newCode)
            (merge_relation R)).
        {
          now rewrite helemEq; exact (merge_elem_root R).
        }
        pose proof (hrootEq elem hrepresented) as heq.
        subst elem.
        apply hmissing. exists newCode. exact hrepresented.
    }
    exists newCode.
    exists (adjoinSetOrdinalRepGraph M
      (merge_relation R) newSet newCode).
    split.
    + apply adjoinSetOrdinalRepGraph_new.
    + apply (ModelSetOrdinalRepCertificate_adjoin V M
        (merge_relation R) old oldCode elem elemCode newSet newCode).
      refine {| adjoin_certificate := merge_certificate R;
                adjoin_code_injective := merge_code_injective R;
                adjoin_old_root := merge_old_root R;
                adjoin_elem_root := merge_elem_root R;
                adjoin_newSet_spec := hnew;
                adjoin_newCode_ordinal :=
                  composite_adjoin_newCode_ordinal C;
                adjoin_code_adjoin := composite_adjoin_code C;
                adjoin_newCode_not_old_member := hnotOldMember;
                adjoin_newCode_irrefl := hirrefl |}.
      intros code hroot.
      exfalso. apply hmissing. now exists code.
Qed.

(* Exact code/set adjunction.  The merge construction may initially reuse an
   arbitrary existing root for [newSet]; Ackermann extensionality identifies
   that root's code with the arithmetic adjunction code. *)
Lemma ModelSetOrdinalRep_adjoin_exact :
  forall (V : Type) (M : FirstOrderAdjunctionModel V),
  ModelSetOrdinalRepMergeLaw M ->
  ModelCompositeMemExtensionalLaw M ->
  forall old oldCode elem elemCode newSet newCode,
  (forall x, foam_mem V M x newSet <->
    foam_mem V M x old \/ x = elem) ->
  ModelSetOrdinalRep M old oldCode ->
  ModelSetOrdinalRep M elem elemCode ->
  ModelCompositeAdjoinCodeData M oldCode elemCode newCode ->
    ModelSetOrdinalRep M newSet newCode.
Proof.
  intros V M hmerge hext old oldCode elem elemCode newSet newCode
    hnew hold helem C.
  pose proof hold as holdRep.
  pose proof helem as helemRep.
  destruct hold as [oldRelation [holdRoot holdCertificate]].
  destruct helem as [elemRelation [helemRoot helemCertificate]].
  destruct (hmerge old oldCode elem elemCode holdRep helemRep) as [R].
  destruct (ModelSetOrdinalRep_adjoin_of_merge_arithmetic V M
    old oldCode elem elemCode newSet newCode R hnew C)
    as [resultCode hresult].
  pose proof hresult as hresultRep.
  destruct hresult as
    [resultRelation [hresultRoot hresultCertificate]].
  pose proof (proj2 holdCertificate old oldCode holdRoot) as holdLocal.
  pose proof (proj2 hresultCertificate
    newSet resultCode hresultRoot) as hresultLocal.
  pose proof
    (ModelSetOrdinalRepCodeFunctionalLaw_of_composite_extensionality
      V M hext) as hfunctional.
  assert (hresultCodeEq : resultCode = newCode).
  {
    apply (hext resultCode newCode
      (proj1 hresultLocal)
      (composite_adjoin_newCode_ordinal C)).
    intros query hqueryOrd. split.
    - intro hqueryResult.
      destruct (proj2 (proj2 hresultLocal) query
        hqueryOrd hqueryResult) as [represented hrepresentedRoot].
      assert (hrepresentedNew : foam_mem V M represented newSet).
      {
        apply (proj2 (proj1 (proj2 hresultLocal) represented)).
        exists query. now split.
      }
      apply (proj2 (composite_adjoin_code C query hqueryOrd)).
      destruct (proj1 (hnew represented) hrepresentedNew)
        as [hrepresentedOld | hrepresentedElem].
      + destruct (proj1 (proj1 (proj2 holdLocal) represented)
          hrepresentedOld)
          as [oldChildCode [holdChildRoot holdChildBit]].
        left.
        assert (hcodeEq : query = oldChildCode).
        {
          apply (hfunctional represented query oldChildCode).
          - exists resultRelation. now split.
          - exists oldRelation. now split.
        }
        now rewrite hcodeEq.
      + subst represented.
        right.
        apply (hfunctional elem query elemCode).
        * exists resultRelation. now split.
        * exact helemRep.
    - intro hqueryNew.
      destruct (proj1 (composite_adjoin_code C query hqueryOrd)
        hqueryNew) as [hqueryOld | hqueryElem].
      + destruct (proj2 (proj2 holdLocal) query
          hqueryOrd hqueryOld) as [represented holdChildRoot].
        assert (hrepresentedOld : foam_mem V M represented old).
        {
          apply (proj2 (proj1 (proj2 holdLocal) represented)).
          exists query. now split.
        }
        assert (hrepresentedNew : foam_mem V M represented newSet).
        { apply (proj2 (hnew represented)). now left. }
        destruct (proj1 (proj1 (proj2 hresultLocal) represented)
          hrepresentedNew)
          as [resultChildCode [hresultChildRoot hresultChildBit]].
        assert (hcodeEq : query = resultChildCode).
        {
          apply (hfunctional represented query resultChildCode).
          - exists oldRelation. now split.
          - exists resultRelation. now split.
        }
        now rewrite hcodeEq.
      + subst query.
        assert (helemNew : foam_mem V M elem newSet).
        { apply (proj2 (hnew elem)). now right. }
        destruct (proj1 (proj1 (proj2 hresultLocal) elem) helemNew)
          as [resultChildCode [hresultChildRoot hresultChildBit]].
        assert (hcodeEq : elemCode = resultChildCode).
        {
          apply (hfunctional elem elemCode resultChildCode).
          - exact helemRep.
          - exists resultRelation. now split.
        }
        now rewrite hcodeEq.
  }
  now rewrite <- hresultCodeEq.
Qed.

Lemma ModelSetOrdinalRep_adjoin_exact_finite :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V),
  ModelCompositeMemExtensionalLaw (fofam_base V M) ->
  forall old oldCode elem elemCode newSet newCode,
  (forall x, foam_mem V M x newSet <->
    foam_mem V M x old \/ x = elem) ->
  ModelSetOrdinalRep (fofam_base V M) old oldCode ->
  ModelSetOrdinalRep (fofam_base V M) elem elemCode ->
  ModelCompositeAdjoinCodeData (fofam_base V M)
    oldCode elemCode newCode ->
    ModelSetOrdinalRep (fofam_base V M) newSet newCode.
Proof.
  intros V M hext old oldCode elem elemCode newSet newCode
    hnew hold helem C.
  apply (ModelSetOrdinalRep_adjoin_exact V (fofam_base V M)
    (ModelSetOrdinalRepMergeLaw_of_composite_extensionality V M hext)
    hext old oldCode elem elemCode newSet newCode
    hnew hold helem C).
Qed.

Definition HasSetOrdinalRep {V : Type}
    (M : FirstOrderAdjunctionModel V) (set : V) : Prop :=
  exists code, ModelSetOrdinalRep M set code.

Lemma setOrdinalRepExists_model :
  forall (V : Type) (M : FirstOrderAdjunctionModel V)
    (env : nat -> V),
  Sat V (foam_mem V M) env (fEx (HF_setOrdinalRepAt 1 0)) <->
    HasSetOrdinalRep M (env 0).
Proof.
  intros V M env.
  unfold HasSetOrdinalRep.
  cbn [Sat].
  setoid_rewrite HF_setOrdinalRepAt_model.
  cbn [scons].
  reflexivity.
Qed.

Definition ModelCompositeAdjoinCodeLaw {V : Type}
    (M : FirstOrderAdjunctionModel V) : Prop :=
  forall oldCode elemCode,
    OrdinalLike (foam_mem V M) oldCode ->
    OrdinalLike (foam_mem V M) elemCode ->
      exists newCode,
        ModelCompositeAdjoinCodeData M oldCode elemCode newCode.

Lemma HasSetOrdinalRep_adjoin_of_merge_code :
  forall (V : Type) (M : FirstOrderAdjunctionModel V),
  ModelSetOrdinalRepMergeLaw M ->
  ModelCompositeAdjoinCodeLaw M ->
  forall old elem newSet,
  (forall x, foam_mem V M x newSet <->
    foam_mem V M x old \/ x = elem) ->
  HasSetOrdinalRep M old ->
  HasSetOrdinalRep M elem ->
    HasSetOrdinalRep M newSet.
Proof.
  intros V M hmerge hcode old elem newSet hnew
    [oldCode hold] [elemCode helem].
  destruct (hmerge old oldCode elem elemCode hold helem) as [R].
  pose proof (proj1 (proj2 (merge_certificate R)
    old oldCode (merge_old_root R))) as holdOrd.
  pose proof (proj1 (proj2 (merge_certificate R)
    elem elemCode (merge_elem_root R))) as helemOrd.
  destruct (hcode oldCode elemCode holdOrd helemOrd)
    as [newCode C].
  exact (ModelSetOrdinalRep_adjoin_of_merge_arithmetic V M
    old oldCode elem elemCode newSet newCode R hnew C).
Qed.

(* Set induction supplies representations of all elements of a target set;
   finite-generation induction then builds representations of its subsets. *)
Lemma HasSetOrdinalRep_total_of_empty_adjoin :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V),
  HasSetOrdinalRep (fofam_base V M) (foam_empty V M) ->
  (forall old elem newSet,
    (forall x, foam_mem V M x newSet <->
      foam_mem V M x old \/ x = elem) ->
    HasSetOrdinalRep (fofam_base V M) old ->
    HasSetOrdinalRep (fofam_base V M) elem ->
      HasSetOrdinalRep (fofam_base V M) newSet) ->
  forall set, HasSetOrdinalRep (fofam_base V M) set.
Proof.
  intros V M hempty hadjoin.
  pose (N := fofam_base V M).
  pose (repForm := fEx (HF_setOrdinalRepAt 1 0)).
  pose (subsetRepForm := fImp (HF_subsetAt 0 1) repForm).
  pose (tail := fun _ : nat => foam_empty V M).
  pose proof (foam_induction_schema V N repForm tail) as houter.
  assert (hall : forall target,
      Sat V (foam_mem V M) (scons V target tail) repForm).
  {
    apply houter.
    intros target hmembers.
    pose (targetEnv := scons V target tail).
    pose proof (fofam_finite_induction_schema V M
      subsetRepForm targetEnv) as hfinite.
    assert (hsubsets : forall current,
        Sat V (foam_mem V M) (scons V current targetEnv)
          subsetRepForm).
    {
      apply (proj1 (HF_finite_induction_form_spec V
        (foam_mem V M) subsetRepForm targetEnv) hfinite).
      split.
      - intros emptyLike hemptyLike _hsubset.
        assert (hEmptyEq : emptyLike = foam_empty V M).
        {
          apply (foam_extensional V N emptyLike (foam_empty V M)).
          intro x. split.
          - intro hx. exfalso. exact (hemptyLike x hx).
          - intro hx. exfalso. exact (foam_empty_spec V N x hx).
        }
        subst emptyLike.
        apply (proj2 (setOrdinalRepExists_model V N
          (scons V (foam_empty V M) targetEnv))).
        exact hempty.
      - intros old elem newSet hnew holdImp hnewSubsetSat.
        pose proof (proj1 (HF_subsetAt_spec V (foam_mem V M)
          (scons V newSet targetEnv) 0 1) hnewSubsetSat)
          as hnewSubset.
        assert (holdSubset : forall x,
            foam_mem V M x old -> foam_mem V M x target).
        {
          intros x hxold.
          apply hnewSubset.
          apply (proj2 (hnew x)). now left.
        }
        assert (helemTarget : foam_mem V M elem target).
        {
          apply hnewSubset.
          apply (proj2 (hnew elem)). now right.
        }
        assert (holdSubsetSat : Sat V (foam_mem V M)
            (scons V old targetEnv) (HF_subsetAt 0 1)).
        {
          apply (proj2 (HF_subsetAt_spec V (foam_mem V M)
            (scons V old targetEnv) 0 1)).
          exact holdSubset.
        }
        pose proof (holdImp holdSubsetSat) as holdRepSat.
        pose proof (proj1 (setOrdinalRepExists_model V N
          (scons V old targetEnv)) holdRepSat) as holdRep.
        pose proof (proj1 (Sat_rename_rSkipParam V (foam_mem V M)
          repForm tail target elem)
          (hmembers elem helemTarget)) as helemRepSat.
        pose proof (proj1 (setOrdinalRepExists_model V N
          (scons V elem tail)) helemRepSat) as helemRep.
        apply (proj2 (setOrdinalRepExists_model V N
          (scons V newSet targetEnv))).
        exact (hadjoin old elem newSet hnew holdRep helemRep).
    }
    pose proof (hsubsets target) as htarget.
    apply htarget.
    apply (proj2 (HF_subsetAt_spec V (foam_mem V M)
      (scons V target targetEnv) 0 1)).
    intros x hx. exact hx.
  }
  intro set.
  apply (proj1 (setOrdinalRepExists_model V N (scons V set tail))).
  exact (hall set).
Qed.

Lemma HasSetOrdinalRep_total_of_empty_merge_code :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V),
  HasSetOrdinalRep (fofam_base V M) (foam_empty V M) ->
  ModelSetOrdinalRepMergeLaw (fofam_base V M) ->
  ModelCompositeAdjoinCodeLaw (fofam_base V M) ->
  forall set, HasSetOrdinalRep (fofam_base V M) set.
Proof.
  intros V M hempty hmerge hcode.
  apply (HasSetOrdinalRep_total_of_empty_adjoin V M hempty).
  intros old elem newSet hnew hold helem.
  exact (HasSetOrdinalRep_adjoin_of_merge_code V (fofam_base V M)
    hmerge hcode old elem newSet hnew hold helem).
Qed.

Lemma HasSetOrdinalRep_total_of_empty_composite_laws :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V),
  HasSetOrdinalRep (fofam_base V M) (foam_empty V M) ->
  ModelCompositeMemExtensionalLaw (fofam_base V M) ->
  ModelCompositeAdjoinCodeLaw (fofam_base V M) ->
  forall set, HasSetOrdinalRep (fofam_base V M) set.
Proof.
  intros V M hempty hext hcode.
  exact (HasSetOrdinalRep_total_of_empty_merge_code V M hempty
    (ModelSetOrdinalRepMergeLaw_of_composite_extensionality V M hext)
    hcode).
Qed.

(* Honest arithmetic boundaries still awaiting their PA-to-HFFin transfer.
   They are stated only for the reconstructed models used by completeness;
   no stronger arbitrary-model assumption is hidden here. *)
Definition HFFinModelCompositeMemExtensionality : Prop :=
  forall (V : Type) (mem : V -> V -> Prop) (v : nat -> V)
    (hHF : forall g, HFFinAx_s g -> Sat V mem v g),
  let M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s V mem v hHF in
    ModelCompositeMemExtensionalLaw (fofam_base V M).

Definition HFFinModelCompositeAdjoinCode : Prop :=
  forall (V : Type) (mem : V -> V -> Prop) (v : nat -> V)
    (hHF : forall g, HFFinAx_s g -> Sat V mem v g),
  let M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s V mem v hHF in
    ModelCompositeAdjoinCodeLaw (fofam_base V M).

Lemma HasSetOrdinalRep_total_of_HFFinAx_s_of_translation :
  HFFinPAProofTranslation ->
  HFFinModelCompositeMemExtensionality ->
  HFFinModelCompositeAdjoinCode ->
  forall (V : Type) (mem : V -> V -> Prop) (v : nat -> V)
    (hHF : forall g, HFFinAx_s g -> Sat V mem v g) set,
  let M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s V mem v hHF in
    HasSetOrdinalRep (fofam_base V M) set.
Proof.
  intros htranslate hext hcode V mem v hHF set.
  pose (M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s
    V mem v hHF).
  change (HasSetOrdinalRep (fofam_base V M) set).
  apply (HasSetOrdinalRep_total_of_empty_composite_laws V M).
  - exists (foam_empty V M).
    exact (ModelSetOrdinalRep_empty_of_HFFinAx_s_of_translation
      htranslate V mem v hHF).
  - exact (hext V mem v hHF).
  - exact (hcode V mem v hHF).
Qed.

(* Relative completeness turns the semantic finite-induction result into
   the desired object-language totality theorem. *)
Lemma BProv_HFFin_setOrdinalRep_total_of_translation_and_arithmetic :
  HFFinPAProofTranslation ->
  HFFinModelCompositeMemExtensionality ->
  HFFinModelCompositeAdjoinCode ->
  forall G set,
    BProv HFFinAx_s G
      (fEx (HF_setOrdinalRepAt (S set) 0)).
Proof.
  intros htranslate hext hcode G set.
  apply (completeness_inf_context HFFinAx_s G
    (fEx (HF_setOrdinalRepAt (S set) 0)) Sentences_HFFin).
  intros V mem v hHF hG.
  pose (M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s
    V mem v hHF).
  destruct (HasSetOrdinalRep_total_of_HFFinAx_s_of_translation
    htranslate hext hcode V mem v hHF (v set)) as [code hrep].
  exists code.
  apply (proj2 (HF_setOrdinalRepAt_model V (fofam_base V M)
    (scons V code v) (S set) 0)).
  exact hrep.
Qed.
