(* ===================================================================== *)
(*  PAHFHFRoundTrip.v                                                    *)
(*                                                                       *)
(*  HF-side semantic infrastructure for the deductive PA/HFFin round     *)
(*  trip.  This module deliberately starts at the arbitrary-model        *)
(*  boundary: standard-model coding and explicit proof-calculus          *)
(*  congruence machinery already live elsewhere or are unnecessary once  *)
(*  the semantic argument is closed with completeness.                    *)
(* ===================================================================== *)

From Stdlib Require Import Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.

(* A total map for the two free PA variables of [hfMemAt 0 1]. *)
Definition repPairSlotMap (elemCode setCode : nat) : nat -> nat :=
  fun n =>
    match n with
    | 0 => elemCode
    | S _ => setCode
    end.

(* Ackermann membership, translated back into the HF language, between
   finite-ordinal codes in the indicated HF slots. *)
Definition HF_compositeMemAt (elemCode setCode : nat) : form :=
  formulaAt (repPairSlotMap elemCode setCode)
    (PA.Formula.hfMemAt 0 1).

(* A finite graph certificate is functional and recursively relates sets to
   ordinal codes according to the composite Ackermann-membership relation. *)
Definition HF_setOrdinalRepCertificateAt (relation : nat) : form :=
  fAnd
    (HF_pairFunctionalAt relation)
    (fAll
      (fAll
        (fImp
          (HF_pairMemAt 1 0 (S (S relation)))
          (fAnd
            (HF_ordinalLikeAt 0)
            (fAnd
              (fAll
                (fIff
                  (fMem 0 2)
                  (fEx
                    (fAnd
                      (HF_pairMemAt 1 0 (S (S (S (S relation)))))
                      (HF_compositeMemAt 0 2)))))
              (fAll
                (fImp
                  (fAnd
                    (HF_ordinalLikeAt 0)
                    (HF_compositeMemAt 0 1))
                  (fEx
                    (HF_pairMemAt 0 1
                      (S (S (S (S relation))))))))))))).

(* A set and an ordinal code occur as a root in some certified graph. *)
Definition HF_setOrdinalRepAt (set code : nat) : form :=
  fEx
    (fAnd
      (HF_pairMemAt (S set) (S code) 0)
      (HF_setOrdinalRepCertificateAt 0)).

(* Formula-level HF -> PA -> HF composite with explicit coded slots. *)
Definition hfCompositeAt (codedMap : nat -> nat) (phi : form) : form :=
  formulaAt codedMap
    (PA.Formula.hfFormulaAt (fun n : nat => n) phi).

Lemma hfCompositeAt_id : forall phi,
  hfCompositeAt (fun n : nat => n) phi =
    translateFormula (PA.Formula.translateHFFormula phi).
Proof. reflexivity. Qed.

Lemma rename_HF_compositeMemAt : forall r elemCode setCode,
  rename r (HF_compositeMemAt elemCode setCode) =
    HF_compositeMemAt (r elemCode) (r setCode).
Proof.
  intros r elemCode setCode.
  unfold HF_compositeMemAt.
  rewrite formulaAt_rename.
  apply formulaAt_map_ext.
  intros [|n]; reflexivity.
Qed.

Lemma HF_compositeMemAt_free : forall i elemCode setCode,
  Free i (HF_compositeMemAt elemCode setCode) ->
    i = elemCode \/ i = setCode.
Proof.
  intros i elemCode setCode h.
  destruct (formulaAt_free (PA.Formula.hfMemAt 0 1)
    (repPairSlotMap elemCode setCode) i h) as [n [hn hi]].
  destruct (PA.Formula.hfMemAt_free n 0 1 hn) as [hn0 | hn1].
  - subst n. left. exact hi.
  - subst n. right. exact hi.
Qed.

Lemma rename_HF_ordinalLikeAt : forall r code,
  rename r (HF_ordinalLikeAt code) = HF_ordinalLikeAt (r code).
Proof.
  intros r code.
  unfold HF_ordinalLikeAt, HF_transitiveAt, HF_memTotalOnAt.
  simpl.
  reflexivity.
Qed.

Local Opaque HF_pairFunctionalAt HF_pairMemAt HF_ordinalLikeAt
  HF_compositeMemAt.

Lemma rename_HF_setOrdinalRepCertificateAt : forall r relation,
  rename r (HF_setOrdinalRepCertificateAt relation) =
    HF_setOrdinalRepCertificateAt (r relation).
Proof.
  intros r relation.
  unfold HF_setOrdinalRepCertificateAt.
  unfold fIff.
  cbn [rename up].
  repeat rewrite rename_HF_pairFunctionalAt.
  repeat rewrite rename_HF_pairMemAt.
  repeat rewrite rename_HF_ordinalLikeAt.
  repeat rewrite rename_HF_compositeMemAt.
  reflexivity.
Qed.

Local Opaque HF_setOrdinalRepCertificateAt.

Lemma rename_HF_setOrdinalRepAt : forall r set code,
  rename r (HF_setOrdinalRepAt set code) =
    HF_setOrdinalRepAt (r set) (r code).
Proof.
  intros r set code.
  unfold HF_setOrdinalRepAt.
  simpl.
  rewrite rename_HF_pairMemAt.
  rewrite rename_HF_setOrdinalRepCertificateAt.
  reflexivity.
Qed.

Local Transparent HF_setOrdinalRepCertificateAt.

Lemma HF_setOrdinalRepCertificateAt_free : forall i relation,
  Free i (HF_setOrdinalRepCertificateAt relation) -> i = relation.
Proof.
  intros i relation h.
  unfold HF_setOrdinalRepCertificateAt, fIff in h.
  simpl in h.
  repeat match goal with
  | h : _ \/ _ |- _ => destruct h as [h | h]
  | h : Free ?j (HF_pairFunctionalAt ?f) |- _ =>
      apply HF_pairFunctionalAt_free in h
  | h : Free ?j (HF_pairMemAt ?a ?b ?r) |- _ =>
      apply HF_pairMemAt_free in h; destruct h as [h | [h | h]]
  | h : Free ?j (HF_ordinalLikeAt ?a) |- _ =>
      apply HF_ordinalLikeAt_free in h
  | h : Free ?j (HF_compositeMemAt ?a ?b) |- _ =>
      apply HF_compositeMemAt_free in h; destruct h as [h | h]
  end; lia.
Qed.

Local Opaque HF_setOrdinalRepCertificateAt.

Lemma HF_setOrdinalRepAt_free : forall i set code,
  Free i (HF_setOrdinalRepAt set code) -> i = set \/ i = code.
Proof.
  intros i set code h.
  unfold HF_setOrdinalRepAt in h.
  simpl in h.
  destruct h as [hroot | hcert].
  - destruct (HF_pairMemAt_free (S i) (S set) (S code) 0 hroot)
      as [hi | [hi | hi]]; lia.
  - pose proof (HF_setOrdinalRepCertificateAt_free (S i) 0 hcert).
    lia.
Qed.

(* ===================================================================== *)
(*  Arbitrary-model semantics                                             *)
(* ===================================================================== *)

(* The environment tail is immaterial: [HF_compositeMemAt 0 1] has only
   slots zero and one free. *)
Definition ModelCompositeMem {V : Type}
    (M : FirstOrderAdjunctionModel V) (elemCode setCode : V) : Prop :=
  Sat V (foam_mem V M)
    (scons V elemCode
      (scons V setCode (fun _ : nat => foam_empty V M)))
    (HF_compositeMemAt 0 1).

Lemma HF_compositeMemAt_01_model : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (e : nat -> V),
  Sat V (foam_mem V M) e (HF_compositeMemAt 0 1) <->
    ModelCompositeMem M (e 0) (e 1).
Proof.
  intros V M e.
  unfold ModelCompositeMem.
  apply Sat_ext_free.
  intros n hn.
  destruct (HF_compositeMemAt_free n 0 1 hn) as [-> | ->]; reflexivity.
Qed.

Lemma HF_compositeMemAt_model : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (e : nat -> V) elemSlot setSlot,
  Sat V (foam_mem V M) e
      (HF_compositeMemAt elemSlot setSlot) <->
    ModelCompositeMem M (e elemSlot) (e setSlot).
Proof.
  intros V M e elemSlot setSlot.
  pose (r := repPairSlotMap elemSlot setSlot).
  assert (hren : rename r (HF_compositeMemAt 0 1) =
      HF_compositeMemAt elemSlot setSlot).
  {
    unfold r.
    rewrite rename_HF_compositeMemAt.
    reflexivity.
  }
  rewrite <- hren.
  rewrite Sat_rename.
  pose proof (HF_compositeMemAt_01_model V M (fun n => e (r n))) as h.
  unfold r, repPairSlotMap in h.
  simpl in h.
  exact h.
Qed.

(* Environment-independent semantic reading of a certified representation
   graph. *)
Definition ModelSetOrdinalRepCertificate {V : Type}
    (M : FirstOrderAdjunctionModel V) (relation : V) : Prop :=
  foam_pair_functional V M relation /\
    forall set code,
      foam_mem V M (foam_kpair_obj V M set code) relation ->
        OrdinalLike (foam_mem V M) code /\
          (forall elem,
            foam_mem V M elem set <->
              exists elemCode,
                foam_mem V M (foam_kpair_obj V M elem elemCode) relation /\
                ModelCompositeMem M elemCode code) /\
          (forall elemCode,
            OrdinalLike (foam_mem V M) elemCode ->
            ModelCompositeMem M elemCode code ->
              exists elem,
                foam_mem V M
                  (foam_kpair_obj V M elem elemCode) relation).

Definition ModelSetOrdinalRep {V : Type}
    (M : FirstOrderAdjunctionModel V) (set code : V) : Prop :=
  exists relation,
    foam_mem V M (foam_kpair_obj V M set code) relation /\
      ModelSetOrdinalRepCertificate M relation.

Local Transparent HF_setOrdinalRepCertificateAt.

Lemma HF_setOrdinalRepCertificateAt_model : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (e : nat -> V) relation,
  Sat V (foam_mem V M) e
      (HF_setOrdinalRepCertificateAt relation) <->
    ModelSetOrdinalRepCertificate M (e relation).
Proof.
  intros V M e relation.
  unfold ModelSetOrdinalRepCertificate, HF_setOrdinalRepCertificateAt.
  cbn [Sat fIff].
  setoid_rewrite foam_HF_pairFunctionalAt_spec.
  setoid_rewrite foam_HF_pairMemAt_spec.
  setoid_rewrite HF_ordinalLikeAt_spec.
  setoid_rewrite HF_compositeMemAt_model.
  cbn [scons].
  split.
  - intros [hfun hcert]. split; [exact hfun |].
    intros set code hroot.
    destruct (hcert set code hroot) as [hord [hmembers hrange]].
    split; [exact hord |]. split.
    + intro elem. specialize (hmembers elem). split;
        [exact (proj1 hmembers) | exact (proj2 hmembers)].
    + intros elemCode hord' hcomp. apply hrange. now split.
  - intros [hfun hcert]. split; [exact hfun |].
    intros set code hroot.
    destruct (hcert set code hroot) as [hord [hmembers hrange]].
    split; [exact hord |]. split.
    + intro elem. specialize (hmembers elem). split;
        [exact (proj1 hmembers) | exact (proj2 hmembers)].
    + intros elemCode [hord' hcomp]. exact (hrange elemCode hord' hcomp).
Qed.

Local Opaque HF_setOrdinalRepCertificateAt.

Lemma HF_setOrdinalRepAt_model : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (e : nat -> V) set code,
  Sat V (foam_mem V M) e (HF_setOrdinalRepAt set code) <->
    ModelSetOrdinalRep M (e set) (e code).
Proof.
  intros V M e set code.
  unfold ModelSetOrdinalRep, HF_setOrdinalRepAt.
  cbn [Sat].
  setoid_rewrite foam_HF_pairMemAt_spec.
  setoid_rewrite HF_setOrdinalRepCertificateAt_model.
  cbn [scons].
  reflexivity.
Qed.
