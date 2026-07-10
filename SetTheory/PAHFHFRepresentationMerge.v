(* ===================================================================== *)
(*  PAHFHFRepresentationMerge.v                                          *)
(*                                                                       *)
(*  Algebra of certified set-to-ordinal representation graphs: extending *)
(*  one common graph by an adjunction root and merging two compatible     *)
(*  graphs by binary union.  Certificate semantics are independent of an  *)
(*  ambient environment, so no environment-transport layer is needed.     *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Lia List.
From SetTheory Require Import Fol PAHF PAHFHFRoundTrip
  PAHFHFRepresentation.

Record ModelSetOrdinalRepAdjoinData {V : Type}
    (M : FirstOrderAdjunctionModel V)
    (relation old oldCode elem elemCode newSet newCode : V) : Prop := {
  adjoin_certificate : ModelSetOrdinalRepCertificate M relation;
  adjoin_code_injective : forall set1 set2 code,
    foam_mem V M (foam_kpair_obj V M set1 code) relation ->
    foam_mem V M (foam_kpair_obj V M set2 code) relation ->
      set1 = set2;
  adjoin_old_root :
    foam_mem V M (foam_kpair_obj V M old oldCode) relation;
  adjoin_elem_root :
    foam_mem V M (foam_kpair_obj V M elem elemCode) relation;
  adjoin_newSet_spec : forall x,
    foam_mem V M x newSet <-> foam_mem V M x old \/ x = elem;
  adjoin_newCode_ordinal : OrdinalLike (foam_mem V M) newCode;
  adjoin_code_adjoin : forall query,
    OrdinalLike (foam_mem V M) query ->
      (ModelCompositeMem M query newCode <->
        ModelCompositeMem M query oldCode \/ query = elemCode);
  adjoin_root_compatible : forall code,
    foam_mem V M (foam_kpair_obj V M newSet code) relation ->
      code = newCode;
  adjoin_newCode_not_old_member : forall set code,
    foam_mem V M (foam_kpair_obj V M set code) relation ->
      ~ ModelCompositeMem M newCode code;
  adjoin_newCode_irrefl : ~ ModelCompositeMem M newCode newCode
}.

Arguments adjoin_certificate
  {V M relation old oldCode elem elemCode newSet newCode} _.
Arguments adjoin_code_injective
  {V M relation old oldCode elem elemCode newSet newCode} _ _ _ _ _ _.
Arguments adjoin_old_root
  {V M relation old oldCode elem elemCode newSet newCode} _.
Arguments adjoin_elem_root
  {V M relation old oldCode elem elemCode newSet newCode} _.
Arguments adjoin_newSet_spec
  {V M relation old oldCode elem elemCode newSet newCode} _ _.
Arguments adjoin_newCode_ordinal
  {V M relation old oldCode elem elemCode newSet newCode} _.
Arguments adjoin_code_adjoin
  {V M relation old oldCode elem elemCode newSet newCode} _ _ _.
Arguments adjoin_root_compatible
  {V M relation old oldCode elem elemCode newSet newCode} _ _ _.
Arguments adjoin_newCode_not_old_member
  {V M relation old oldCode elem elemCode newSet newCode} _ _ _ _.
Arguments adjoin_newCode_irrefl
  {V M relation old oldCode elem elemCode newSet newCode} _.

Definition adjoinSetOrdinalRepGraph {V : Type}
    (M : FirstOrderAdjunctionModel V)
    (relation newSet newCode : V) : V :=
  foam_adjoin V M relation (foam_kpair_obj V M newSet newCode).

Lemma adjoinSetOrdinalRepGraph_old : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) relation newSet newCode p,
  foam_mem V M p relation ->
    foam_mem V M p
      (adjoinSetOrdinalRepGraph M relation newSet newCode).
Proof.
  intros V M relation newSet newCode p hp.
  apply (proj2 (foam_adjoin_spec V M p relation
    (foam_kpair_obj V M newSet newCode))).
  left. exact hp.
Qed.

(* Mixed functionality and injectivity are exactly what binary union needs
   in order to preserve a representation certificate. *)
Definition ModelSetOrdinalRepRelationsCompatible {V : Type}
    (M : FirstOrderAdjunctionModel V) (left right : V) : Prop :=
  (forall set leftCode rightCode,
    foam_mem V M (foam_kpair_obj V M set leftCode) left ->
    foam_mem V M (foam_kpair_obj V M set rightCode) right ->
      leftCode = rightCode) /\
  (forall leftSet rightSet code,
    (foam_mem V M (foam_kpair_obj V M leftSet code) left \/
     foam_mem V M (foam_kpair_obj V M leftSet code) right) ->
    (foam_mem V M (foam_kpair_obj V M rightSet code) left \/
     foam_mem V M (foam_kpair_obj V M rightSet code) right) ->
      leftSet = rightSet).

(* The certificate argument is purely algebraic; finiteness is needed only
   by callers to obtain an object realizing the binary union. *)
Lemma ModelSetOrdinalRepCertificate_binUnion : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) left right union,
  ModelSetOrdinalRepCertificate M left ->
  ModelSetOrdinalRepCertificate M right ->
  ModelSetOrdinalRepRelationsCompatible M left right ->
  (forall p, foam_mem V M p union <->
    foam_mem V M p left \/ foam_mem V M p right) ->
  ModelSetOrdinalRepCertificate M union.
Proof.
  intros V M left right union hleft hright hcompat hunion.
  split.
  - unfold foam_pair_functional.
    intros set code code' hcode hcode'.
    destruct (proj1 (hunion _) hcode) as [hcodeLeft | hcodeRight];
    destruct (proj1 (hunion _) hcode') as [hcodeLeft' | hcodeRight'].
    + exact (proj1 hleft set code code' hcodeLeft hcodeLeft').
    + exact (proj1 hcompat set code code' hcodeLeft hcodeRight').
    + symmetry. exact (proj1 hcompat set code' code hcodeLeft' hcodeRight).
    + exact (proj1 hright set code code' hcodeRight hcodeRight').
  - intros set code hroot.
    destruct (proj1 (hunion _) hroot) as [hrootLeft | hrootRight].
    + pose proof (proj2 hleft set code hrootLeft) as hlocal.
      destruct hlocal as [hcodeOrd [hmembers hrange]].
      split; [exact hcodeOrd |].
      split.
      * intro elem.
        split.
        -- intro helem.
           destruct (proj1 (hmembers elem) helem) as
             [elemCode [hpair hcoded]].
           exists elemCode. split.
           ++ apply (proj2 (hunion _)). left. exact hpair.
           ++ exact hcoded.
        -- intros [elemCode [hpair hcoded]].
           destruct (proj1 (hunion _) hpair) as [hpairLeft | hpairRight].
           ++ apply (proj2 (hmembers elem)).
              exists elemCode. split; assumption.
           ++ pose proof (proj1 (proj2 hright elem elemCode hpairRight))
                as helemOrd.
              destruct (hrange elemCode helemOrd hcoded)
                as [leftElem hleftPair].
              assert (heq : leftElem = elem).
              {
                exact (proj2 hcompat leftElem elem elemCode
                  (or_introl hleftPair) (or_intror hpairRight)).
              }
              subst leftElem.
              apply (proj2 (hmembers elem)).
              exists elemCode. split; assumption.
      * intros elemCode helemOrd hcoded.
        destruct (hrange elemCode helemOrd hcoded) as [elem hpair].
        exists elem.
        apply (proj2 (hunion _)). left. exact hpair.
    + pose proof (proj2 hright set code hrootRight) as hlocal.
      destruct hlocal as [hcodeOrd [hmembers hrange]].
      split; [exact hcodeOrd |].
      split.
      * intro elem.
        split.
        -- intro helem.
           destruct (proj1 (hmembers elem) helem) as
             [elemCode [hpair hcoded]].
           exists elemCode. split.
           ++ apply (proj2 (hunion _)). right. exact hpair.
           ++ exact hcoded.
        -- intros [elemCode [hpair hcoded]].
           destruct (proj1 (hunion _) hpair) as [hpairLeft | hpairRight].
           ++ pose proof (proj1 (proj2 hleft elem elemCode hpairLeft))
                as helemOrd.
              destruct (hrange elemCode helemOrd hcoded)
                as [rightElem hrightPair].
              assert (heq : elem = rightElem).
              {
                exact (proj2 hcompat elem rightElem elemCode
                  (or_introl hpairLeft) (or_intror hrightPair)).
              }
              subst rightElem.
              apply (proj2 (hmembers elem)).
              exists elemCode. split; assumption.
           ++ apply (proj2 (hmembers elem)).
              exists elemCode. split; assumption.
      * intros elemCode helemOrd hcoded.
        destruct (hrange elemCode helemOrd hcoded) as [elem hpair].
        exists elem.
        apply (proj2 (hunion _)). right. exact hpair.
Qed.

Lemma adjoinSetOrdinalRepGraph_new : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) relation newSet newCode,
  foam_mem V M (foam_kpair_obj V M newSet newCode)
    (adjoinSetOrdinalRepGraph M relation newSet newCode).
Proof.
  intros V M relation newSet newCode.
  apply (proj2 (foam_adjoin_spec V M
    (foam_kpair_obj V M newSet newCode) relation
    (foam_kpair_obj V M newSet newCode))).
  right. reflexivity.
Qed.

Lemma ModelSetOrdinalRepCertificate_adjoin : forall (V : Type)
    (M : FirstOrderAdjunctionModel V)
    relation old oldCode elem elemCode newSet newCode,
  ModelSetOrdinalRepAdjoinData M relation
    old oldCode elem elemCode newSet newCode ->
  ModelSetOrdinalRepCertificate M
    (adjoinSetOrdinalRepGraph M relation newSet newCode).
Proof.
  intros V M relation old oldCode elem elemCode newSet newCode D.
  set (newPair := foam_kpair_obj V M newSet newCode).
  set (extended := adjoinSetOrdinalRepGraph M relation newSet newCode).
  assert (hmemExtended : forall p,
      foam_mem V M p extended <->
        foam_mem V M p relation \/ p = newPair).
  {
    intro p.
    unfold extended, adjoinSetOrdinalRepGraph, newPair.
    apply foam_adjoin_spec.
  }
  split.
  - unfold foam_pair_functional.
    intros key value value' hvalue hvalue'.
    destruct (proj1 (hmemExtended
      (foam_kpair_obj V M key value)) hvalue) as [hOld | hNew].
    + destruct (proj1 (hmemExtended
        (foam_kpair_obj V M key value')) hvalue') as [hOld' | hNew'].
      * exact (proj1 (adjoin_certificate D) key value value' hOld hOld').
      * assert (hk : key = newSet).
        { exact (proj1 (foam_kpair_injective V M key value'
            newSet newCode hNew')). }
        assert (hv' : value' = newCode).
        { exact (proj2 (foam_kpair_injective V M key value'
            newSet newCode hNew')). }
        assert (hv : value = newCode).
        {
          apply (adjoin_root_compatible D value).
          now rewrite <- hk.
        }
        now rewrite hv, hv'.
    + destruct (proj1 (hmemExtended
        (foam_kpair_obj V M key value')) hvalue') as [hOld' | hNew'].
      * assert (hk : key = newSet).
        { exact (proj1 (foam_kpair_injective V M key value
            newSet newCode hNew)). }
        assert (hv : value = newCode).
        { exact (proj2 (foam_kpair_injective V M key value
            newSet newCode hNew)). }
        assert (hv' : value' = newCode).
        {
          apply (adjoin_root_compatible D value').
          now rewrite <- hk.
        }
        now rewrite hv, hv'.
      * assert (hv : value = newCode).
        { exact (proj2 (foam_kpair_injective V M key value
            newSet newCode hNew)). }
        assert (hv' : value' = newCode).
        { exact (proj2 (foam_kpair_injective V M key value'
            newSet newCode hNew')). }
        now rewrite hv, hv'.
  - intros set code hpair.
    destruct (proj1 (hmemExtended
      (foam_kpair_obj V M set code)) hpair) as [hOld | hNew].
    + pose proof (proj2 (adjoin_certificate D) set code hOld) as hlocal.
      destruct hlocal as [hcodeOrd [hmembers hrange]].
      split; [exact hcodeOrd |].
      split.
      * intro child.
        split.
        -- intro hchild.
           destruct (proj1 (hmembers child) hchild) as
             [childCode [hchildPair hcoded]].
           exists childCode.
           split.
           ++ apply adjoinSetOrdinalRepGraph_old. exact hchildPair.
           ++ exact hcoded.
        -- intros [childCode [hchildPair hcoded]].
           destruct (proj1 (hmemExtended
             (foam_kpair_obj V M child childCode)) hchildPair)
             as [hchildOld | hchildNew].
           ++ apply (proj2 (hmembers child)).
              exists childCode. split; assumption.
           ++ assert (hchildCode : childCode = newCode).
              { exact (proj2 (foam_kpair_injective V M child childCode
                  newSet newCode hchildNew)). }
              exfalso.
              apply (adjoin_newCode_not_old_member D set code hOld).
              now rewrite <- hchildCode.
      * intros query hqueryOrd hcoded.
        destruct (hrange query hqueryOrd hcoded) as [child hchildPair].
        exists child.
        apply adjoinSetOrdinalRepGraph_old. exact hchildPair.
    + pose proof (foam_kpair_injective V M set code
        newSet newCode hNew) as hrootEq.
      destruct hrootEq as [hset hcode].
      subst set. subst code.
      pose proof (proj2 (adjoin_certificate D)
        old oldCode (adjoin_old_root D)) as holdLocal.
      split; [exact (adjoin_newCode_ordinal D) |].
      split.
      * intro child.
        split.
        -- intro hchild.
           destruct (proj1 (adjoin_newSet_spec D child) hchild)
             as [hchildOld | hchildElem].
           ++ destruct (proj1 (proj1 (proj2 holdLocal) child) hchildOld)
                as [childCode [hchildPair hcodedOld]].
              pose proof (proj1 (proj2 (adjoin_certificate D)
                child childCode hchildPair)) as hchildOrd.
              exists childCode.
              split.
              ** apply adjoinSetOrdinalRepGraph_old. exact hchildPair.
              ** apply (proj2 (adjoin_code_adjoin D childCode hchildOrd)).
                 left. exact hcodedOld.
           ++ subst child.
              pose proof (proj1 (proj2 (adjoin_certificate D)
                elem elemCode (adjoin_elem_root D))) as helemOrd.
              exists elemCode.
              split.
              ** apply adjoinSetOrdinalRepGraph_old.
                 exact (adjoin_elem_root D).
              ** apply (proj2 (adjoin_code_adjoin D elemCode helemOrd)).
                 right. reflexivity.
        -- intros [childCode [hchildPair hcodedNew]].
           destruct (proj1 (hmemExtended
             (foam_kpair_obj V M child childCode)) hchildPair)
             as [hchildOld | hchildNew].
           ++ pose proof (proj1 (proj2 (adjoin_certificate D)
                child childCode hchildOld)) as hchildOrd.
              destruct (proj1 (adjoin_code_adjoin D childCode hchildOrd)
                hcodedNew) as [hcodedOld | hchildCode].
              ** apply (proj2 (adjoin_newSet_spec D child)).
                 left.
                 apply (proj2 (proj1 (proj2 holdLocal) child)).
                 exists childCode. split; assumption.
              ** apply (proj2 (adjoin_newSet_spec D child)).
                 right.
                 assert (hchildOld' :
                   foam_mem V M (foam_kpair_obj V M child elemCode)
                     relation).
                 { now rewrite <- hchildCode. }
                 exact (adjoin_code_injective D child elem elemCode
                   hchildOld' (adjoin_elem_root D)).
           ++ assert (hchildCode : childCode = newCode).
              { exact (proj2 (foam_kpair_injective V M child childCode
                  newSet newCode hchildNew)). }
              apply False_rect.
              apply (adjoin_newCode_irrefl D).
              rewrite hchildCode in hcodedNew.
              exact hcodedNew.
      * intros query hqueryOrd hcodedNew.
        destruct (proj1 (adjoin_code_adjoin D query hqueryOrd) hcodedNew)
          as [hcodedOld | hquery].
        -- destruct (proj2 (proj2 holdLocal) query hqueryOrd hcodedOld)
             as [child hchildPair].
           exists child.
           apply adjoinSetOrdinalRepGraph_old. exact hchildPair.
        -- subst query.
           exists elem.
           apply adjoinSetOrdinalRepGraph_old.
           exact (adjoin_elem_root D).
Qed.

(* A common certified graph containing two independently chosen roots. *)
Record ModelSetOrdinalRepMergeResult {V : Type}
    (M : FirstOrderAdjunctionModel V)
    (old oldCode elem elemCode : V) : Type := {
  merge_relation : V;
  merge_certificate :
    ModelSetOrdinalRepCertificate M merge_relation;
  merge_code_injective : forall set1 set2 code,
    foam_mem V M (foam_kpair_obj V M set1 code) merge_relation ->
    foam_mem V M (foam_kpair_obj V M set2 code) merge_relation ->
      set1 = set2;
  merge_old_root :
    foam_mem V M (foam_kpair_obj V M old oldCode) merge_relation;
  merge_elem_root :
    foam_mem V M (foam_kpair_obj V M elem elemCode) merge_relation
}.

Arguments merge_relation {V M old oldCode elem elemCode} _.
Arguments merge_certificate {V M old oldCode elem elemCode} _.
Arguments merge_code_injective {V M old oldCode elem elemCode}
  _ _ _ _ _ _.
Arguments merge_old_root {V M old oldCode elem elemCode} _.
Arguments merge_elem_root {V M old oldCode elem elemCode} _.

Definition ModelSetOrdinalRepMergeLaw {V : Type}
    (M : FirstOrderAdjunctionModel V) : Prop :=
  forall old oldCode elem elemCode,
    ModelSetOrdinalRep M old oldCode ->
    ModelSetOrdinalRep M elem elemCode ->
      inhabited (ModelSetOrdinalRepMergeResult M
        old oldCode elem elemCode).

Lemma ModelSetOrdinalRepMergeResult_of_compatible : forall (V : Type)
    (M : FirstOrderFiniteAdjunctionModel V)
    old oldCode elem elemCode,
  ModelSetOrdinalRep (fofam_base V M) old oldCode ->
  ModelSetOrdinalRep (fofam_base V M) elem elemCode ->
  (forall left right,
    ModelSetOrdinalRepCertificate (fofam_base V M) left ->
    ModelSetOrdinalRepCertificate (fofam_base V M) right ->
      ModelSetOrdinalRepRelationsCompatible
        (fofam_base V M) left right) ->
  inhabited (ModelSetOrdinalRepMergeResult (fofam_base V M)
    old oldCode elem elemCode).
Proof.
  intros V M old oldCode elem elemCode hold helem hcompat.
  destruct hold as [left [holdRoot hleft]].
  destruct helem as [right [helemRoot hright]].
  destruct (fofam_binUnion_exists V M left right) as [union hunion].
  pose proof (hcompat left right hleft hright) as hcompat'.
  assert (hcertificate :
      ModelSetOrdinalRepCertificate (fofam_base V M) union).
  {
    apply (ModelSetOrdinalRepCertificate_binUnion V
      (fofam_base V M) left right union hleft hright hcompat').
    exact hunion.
  }
  constructor.
  refine {| merge_relation := union;
            merge_certificate := hcertificate |}.
  - intros set1 set2 code hset1 hset2.
    exact (proj2 hcompat' set1 set2 code
      (proj1 (hunion _) hset1) (proj1 (hunion _) hset2)).
  - apply (proj2 (hunion _)). left. exact holdRoot.
  - apply (proj2 (hunion _)). right. exact helemRoot.
Qed.

Definition ModelSetOrdinalRepRelationsCompatibilityLaw {V : Type}
    (M : FirstOrderAdjunctionModel V) : Prop :=
  forall left right,
    ModelSetOrdinalRepCertificate M left ->
    ModelSetOrdinalRepCertificate M right ->
      ModelSetOrdinalRepRelationsCompatible M left right.

Lemma ModelSetOrdinalRepMergeLaw_of_finite_compatibility :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V),
  ModelSetOrdinalRepRelationsCompatibilityLaw (fofam_base V M) ->
    ModelSetOrdinalRepMergeLaw (fofam_base V M).
Proof.
  intros V M hcompat old oldCode elem elemCode hold helem.
  apply (ModelSetOrdinalRepMergeResult_of_compatible V M
    old oldCode elem elemCode hold helem).
  intros left right hleft hright.
  exact (hcompat left right hleft hright).
Qed.

Lemma ModelSetOrdinalRep_code_eq_of_mergeLaw : forall (V : Type)
    (M : FirstOrderAdjunctionModel V),
  ModelSetOrdinalRepMergeLaw M ->
  forall set code1 code2,
    ModelSetOrdinalRep M set code1 ->
    ModelSetOrdinalRep M set code2 ->
      code1 = code2.
Proof.
  intros V M hmerge set code1 code2 h1 h2.
  destruct (hmerge set code1 set code2 h1 h2) as [R].
  exact (proj1 (merge_certificate R) set code1 code2
    (merge_old_root R) (merge_elem_root R)).
Qed.

Lemma ModelSetOrdinalRep_set_eq_of_mergeLaw : forall (V : Type)
    (M : FirstOrderAdjunctionModel V),
  ModelSetOrdinalRepMergeLaw M ->
  forall set1 set2 code,
    ModelSetOrdinalRep M set1 code ->
    ModelSetOrdinalRep M set2 code ->
      set1 = set2.
Proof.
  intros V M hmerge set1 set2 code h1 h2.
  destruct (hmerge set1 code set2 code h1 h2) as [R].
  exact (merge_code_injective R set1 set2 code
    (merge_old_root R) (merge_elem_root R)).
Qed.
