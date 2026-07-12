(* ===================================================================== *)
(*  PAHFRawSemantics.v                                                  *)
(*                                                                       *)
(*  A lightweight PA term algebra on the ordinal-like part of an         *)
(*  arbitrary finite-HF model.  Unlike PA.Model, this algebra deliberately*)
(*  carries no arithmetic axioms or second-order induction principle: raw *)
(*  natural-deduction soundness needs only total term operations.         *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Lia List ClassicalEpsilon.
From FirstOrder Require Import Fol Calculus Completeness.
From PAHF Require Import PAHF
  PAHFInterpretations PAHFTermGraphTotal.

Import ListNotations.

Definition FOFAMOrdinal {V : Type}
    (M : FirstOrderFiniteAdjunctionModel V) : Type :=
  { x : V | OrdinalLike (foam_mem V M) x }.

Definition fofamAddRelation {V : Type}
    (M : FirstOrderFiniteAdjunctionModel V) (a b z : V) : Prop :=
  exists f,
    foam_succ_rec_approx V M a f b /\
    foam_mem V M (foam_kpair_obj V M b z) f.

Lemma fofamAddRelation_total :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V)
    (a b : FOFAMOrdinal M),
  exists z, fofamAddRelation M (proj1_sig a) (proj1_sig b) z.
Proof.
  intros V M [a ha] [b hb].
  destruct (fofam_succ_rec_total_of_ordinalLike V M a b hb) as
    [f [z [hf hz]]].
  exists z, f. now split.
Qed.

Definition fofamAddChoice {V : Type}
    (M : FirstOrderFiniteAdjunctionModel V)
    (a b : FOFAMOrdinal M) :
    { z : V | fofamAddRelation M (proj1_sig a) (proj1_sig b) z } :=
  constructive_indefinite_description _
    (fofamAddRelation_total V M a b).

Definition fofamOrdinalAdd {V : Type}
    (M : FirstOrderFiniteAdjunctionModel V)
    (a b : FOFAMOrdinal M) : FOFAMOrdinal M.
Proof.
  pose (z := proj1_sig (fofamAddChoice M a b)).
  refine (exist _ z _).
  destruct (proj2_sig (fofamAddChoice M a b)) as [f [hf hz]].
  exact (fofam_succ_rec_approx_value_OrdinalLike V M
    (proj1_sig a) f (proj1_sig b) z
    (proj2_sig a) (proj2_sig b) hf hz).
Defined.

Lemma fofamOrdinalAdd_spec :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V)
    (a b : FOFAMOrdinal M),
  fofamAddRelation M (proj1_sig a) (proj1_sig b)
    (proj1_sig (fofamOrdinalAdd M a b)).
Proof.
  intros V M a b.
  unfold fofamOrdinalAdd.
  exact (proj2_sig (fofamAddChoice M a b)).
Qed.

Definition fofamMulRelation {V : Type}
    (M : FirstOrderFiniteAdjunctionModel V) (a b z : V) : Prop :=
  exists f,
    foam_mul_rec_approx V M a f b /\
    foam_mem V M (foam_kpair_obj V M b z) f.

Lemma fofamMulRelation_total :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V)
    (a b : FOFAMOrdinal M),
  exists z, fofamMulRelation M (proj1_sig a) (proj1_sig b) z.
Proof.
  intros V M [a ha] [b hb].
  destruct (fofam_mul_rec_total_of_ordinalLike V M a b ha hb) as
    [f [z [hf hz]]].
  exists z, f. now split.
Qed.

Definition fofamMulChoice {V : Type}
    (M : FirstOrderFiniteAdjunctionModel V)
    (a b : FOFAMOrdinal M) :
    { z : V | fofamMulRelation M (proj1_sig a) (proj1_sig b) z } :=
  constructive_indefinite_description _
    (fofamMulRelation_total V M a b).

Definition fofamOrdinalMul {V : Type}
    (M : FirstOrderFiniteAdjunctionModel V)
    (a b : FOFAMOrdinal M) : FOFAMOrdinal M.
Proof.
  pose (z := proj1_sig (fofamMulChoice M a b)).
  refine (exist _ z _).
  destruct (proj2_sig (fofamMulChoice M a b)) as [f [hf hz]].
  exact (fofam_mul_rec_approx_value_OrdinalLike V M
    (proj1_sig a) f (proj1_sig b) z
    (proj2_sig a) (proj2_sig b) hf hz).
Defined.

Lemma fofamOrdinalMul_spec :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V)
    (a b : FOFAMOrdinal M),
  fofamMulRelation M (proj1_sig a) (proj1_sig b)
    (proj1_sig (fofamOrdinalMul M a b)).
Proof.
  intros V M a b.
  unfold fofamOrdinalMul.
  exact (proj2_sig (fofamMulChoice M a b)).
Qed.

Definition fofamOrdinalZero {V : Type}
    (M : FirstOrderFiniteAdjunctionModel V) : FOFAMOrdinal M :=
  exist _ (foam_empty V M) (foam_OrdinalLike_empty V M).

Definition fofamOrdinalSucc {V : Type}
    (M : FirstOrderFiniteAdjunctionModel V)
    (a : FOFAMOrdinal M) : FOFAMOrdinal M :=
  exist _ (foam_adjoin V M (proj1_sig a) (proj1_sig a))
    (foam_OrdinalLike_adjoin_self V M (proj1_sig a)
      (foam_adjoin V M (proj1_sig a) (proj1_sig a))
      (proj2_sig a) eq_refl).

Fixpoint fofamPATermEval {V : Type}
    (M : FirstOrderFiniteAdjunctionModel V)
    (e : nat -> FOFAMOrdinal M) (t : PA.term) : FOFAMOrdinal M :=
  match t with
  | PA.tVar n => e n
  | PA.tZero => fofamOrdinalZero M
  | PA.tSucc a => fofamOrdinalSucc M (fofamPATermEval M e a)
  | PA.tAdd a b =>
      fofamOrdinalAdd M (fofamPATermEval M e a) (fofamPATermEval M e b)
  | PA.tMul a b =>
      fofamOrdinalMul M (fofamPATermEval M e a) (fofamPATermEval M e b)
  end.

Fixpoint fofamPAFormulaSat {V : Type}
    (M : FirstOrderFiniteAdjunctionModel V)
    (e : nat -> FOFAMOrdinal M) (phi : PA.formula) : Prop :=
  match phi with
  | PA.pEq a b => fofamPATermEval M e a = fofamPATermEval M e b
  | PA.pBot => False
  | PA.pImp a b => fofamPAFormulaSat M e a -> fofamPAFormulaSat M e b
  | PA.pAnd a b => fofamPAFormulaSat M e a /\ fofamPAFormulaSat M e b
  | PA.pOr a b => fofamPAFormulaSat M e a \/ fofamPAFormulaSat M e b
  | PA.pAll a => forall x, fofamPAFormulaSat M (scons _ x e) a
  | PA.pEx a => exists x, fofamPAFormulaSat M (scons _ x e) a
  end.

Lemma fofamPATermEval_ext :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V)
    t (e e' : nat -> FOFAMOrdinal M),
  (forall n, e n = e' n) ->
  fofamPATermEval M e t = fofamPATermEval M e' t.
Proof.
  intros V M t.
  induction t as [n | | a IHa | a IHa b IHb | a IHa b IHb];
    simpl; intros e e' he; try reflexivity.
  - apply he.
  - now rewrite (IHa e e' he).
  - now rewrite (IHa e e' he), (IHb e e' he).
  - now rewrite (IHa e e' he), (IHb e e' he).
Qed.

Lemma fofamPATermEval_rename :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V)
    t r (e : nat -> FOFAMOrdinal M),
  fofamPATermEval M e (PA.Term.rename r t) =
    fofamPATermEval M (fun n => e (r n)) t.
Proof.
  intros V M t.
  induction t as [n | | a IHa | a IHa b IHb | a IHa b IHb];
    simpl; intros r e; try reflexivity.
  - now rewrite IHa.
  - now rewrite IHa, IHb.
  - now rewrite IHa, IHb.
Qed.

Lemma fofamPATermEval_subst :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V)
    t sigma (e : nat -> FOFAMOrdinal M),
  fofamPATermEval M e (PA.Term.subst sigma t) =
    fofamPATermEval M (fun n => fofamPATermEval M e (sigma n)) t.
Proof.
  intros V M t.
  induction t as [n | | a IHa | a IHa b IHb | a IHa b IHb];
    simpl; intros sigma e; try reflexivity.
  - now rewrite IHa.
  - now rewrite IHa, IHb.
  - now rewrite IHa, IHb.
Qed.

Lemma fofamPATermEval_upSubst :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V)
    sigma (e : nat -> FOFAMOrdinal M) d n,
  fofamPATermEval M (scons _ d e) (PA.Term.upSubst sigma n) =
    scons _ d (fun k => fofamPATermEval M e (sigma k)) n.
Proof.
  intros V M sigma e d [|n]; simpl.
  - reflexivity.
  - rewrite fofamPATermEval_rename.
    apply fofamPATermEval_ext.
    intro k. reflexivity.
Qed.

Lemma fofamPAFormulaSat_ext :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V)
    phi (e e' : nat -> FOFAMOrdinal M),
  (forall n, e n = e' n) ->
  (fofamPAFormulaSat M e phi <-> fofamPAFormulaSat M e' phi).
Proof.
  intros V M phi.
  induction phi as [a b | | a IHa b IHb | a IHa b IHb |
      a IHa b IHb | a IHa | a IHa];
    simpl; intros e e' he.
  - rewrite (fofamPATermEval_ext V M a e e' he).
    rewrite (fofamPATermEval_ext V M b e e' he).
    reflexivity.
  - reflexivity.
  - split; intros h ha.
    + apply (proj1 (IHb e e' he)).
      apply h.
      apply (proj2 (IHa e e' he)). exact ha.
    + apply (proj2 (IHb e e' he)).
      apply h.
      apply (proj1 (IHa e e' he)). exact ha.
  - split; intros [ha hb]; split.
    + apply (proj1 (IHa e e' he)). exact ha.
    + apply (proj1 (IHb e e' he)). exact hb.
    + apply (proj2 (IHa e e' he)). exact ha.
    + apply (proj2 (IHb e e' he)). exact hb.
  - split; intros h.
    + destruct h as [ha | hb].
      * left. apply (proj1 (IHa e e' he)). exact ha.
      * right. apply (proj1 (IHb e e' he)). exact hb.
    + destruct h as [ha | hb].
      * left. apply (proj2 (IHa e e' he)). exact ha.
      * right. apply (proj2 (IHb e e' he)). exact hb.
  - split; intros hall d.
    + apply (proj1 (IHa (scons _ d e) (scons _ d e')
        (fun n => match n with 0 => eq_refl | S k => he k end))).
      exact (hall d).
    + apply (proj2 (IHa (scons _ d e) (scons _ d e')
        (fun n => match n with 0 => eq_refl | S k => he k end))).
      exact (hall d).
  - split; intros hex.
    + destruct hex as [d hd].
      exists d.
      apply (proj1 (IHa (scons _ d e) (scons _ d e')
        (fun n => match n with 0 => eq_refl | S k => he k end))).
      exact hd.
    + destruct hex as [d hd].
      exists d.
      apply (proj2 (IHa (scons _ d e) (scons _ d e')
        (fun n => match n with 0 => eq_refl | S k => he k end))).
      exact hd.
Qed.

Lemma fofamPAFormulaSat_rename :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V)
    phi r (e : nat -> FOFAMOrdinal M),
  fofamPAFormulaSat M e (PA.Formula.rename r phi) <->
  fofamPAFormulaSat M (fun n => e (r n)) phi.
Proof.
  intros V M phi.
  induction phi as [a b | | a IHa b IHb | a IHa b IHb |
      a IHa b IHb | a IHa | a IHa];
    simpl; intros r e.
  - rewrite !fofamPATermEval_rename. reflexivity.
  - reflexivity.
  - rewrite IHa, IHb. reflexivity.
  - rewrite IHa, IHb. reflexivity.
  - rewrite IHa, IHb. reflexivity.
  - split; intros hall d.
    + pose proof (proj1 (IHa (up r) (scons _ d e)) (hall d)) as h.
      apply (proj1 (fofamPAFormulaSat_ext V M a
        (fun n => scons _ d e (up r n))
        (scons _ d (fun n => e (r n)))
        (fun n => match n with 0 => eq_refl | S _ => eq_refl end))).
      exact h.
    + apply (proj2 (IHa (up r) (scons _ d e))).
      apply (proj2 (fofamPAFormulaSat_ext V M a
        (fun n => scons _ d e (up r n))
        (scons _ d (fun n => e (r n)))
        (fun n => match n with 0 => eq_refl | S _ => eq_refl end))).
      exact (hall d).
  - split; intros hex.
    + destruct hex as [d hd].
      exists d.
      pose proof (proj1 (IHa (up r) (scons _ d e)) hd) as h.
      apply (proj1 (fofamPAFormulaSat_ext V M a
        (fun n => scons _ d e (up r n))
        (scons _ d (fun n => e (r n)))
        (fun n => match n with 0 => eq_refl | S _ => eq_refl end))).
      exact h.
    + destruct hex as [d hd].
      exists d.
      apply (proj2 (IHa (up r) (scons _ d e))).
      apply (proj2 (fofamPAFormulaSat_ext V M a
        (fun n => scons _ d e (up r n))
        (scons _ d (fun n => e (r n)))
        (fun n => match n with 0 => eq_refl | S _ => eq_refl end))).
      exact hd.
Qed.

Lemma fofamPAFormulaSat_subst :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V)
    phi sigma (e : nat -> FOFAMOrdinal M),
  fofamPAFormulaSat M e (PA.Formula.subst sigma phi) <->
  fofamPAFormulaSat M (fun n => fofamPATermEval M e (sigma n)) phi.
Proof.
  intros V M phi.
  induction phi as [a b | | a IHa b IHb | a IHa b IHb |
      a IHa b IHb | a IHa | a IHa];
    simpl; intros sigma e.
  - rewrite !fofamPATermEval_subst. reflexivity.
  - reflexivity.
  - rewrite IHa, IHb. reflexivity.
  - rewrite IHa, IHb. reflexivity.
  - rewrite IHa, IHb. reflexivity.
  - split; intros hall d.
    + pose proof (proj1 (IHa (PA.Term.upSubst sigma)
        (scons _ d e)) (hall d)) as h.
      apply (proj1 (fofamPAFormulaSat_ext V M a
        (fun n => fofamPATermEval M (scons _ d e)
          (PA.Term.upSubst sigma n))
        (scons _ d (fun k => fofamPATermEval M e (sigma k)))
        (fofamPATermEval_upSubst V M sigma e d))).
      exact h.
    + apply (proj2 (IHa (PA.Term.upSubst sigma) (scons _ d e))).
      apply (proj2 (fofamPAFormulaSat_ext V M a
        (fun n => fofamPATermEval M (scons _ d e)
          (PA.Term.upSubst sigma n))
        (scons _ d (fun k => fofamPATermEval M e (sigma k)))
        (fofamPATermEval_upSubst V M sigma e d))).
      exact (hall d).
  - split; intros hex.
    + destruct hex as [d hd].
      exists d.
      pose proof (proj1 (IHa (PA.Term.upSubst sigma)
        (scons _ d e)) hd) as h.
      apply (proj1 (fofamPAFormulaSat_ext V M a
        (fun n => fofamPATermEval M (scons _ d e)
          (PA.Term.upSubst sigma n))
        (scons _ d (fun k => fofamPATermEval M e (sigma k)))
        (fofamPATermEval_upSubst V M sigma e d))).
      exact h.
    + destruct hex as [d hd].
      exists d.
      apply (proj2 (IHa (PA.Term.upSubst sigma) (scons _ d e))).
      apply (proj2 (fofamPAFormulaSat_ext V M a
        (fun n => fofamPATermEval M (scons _ d e)
          (PA.Term.upSubst sigma n))
        (scons _ d (fun k => fofamPATermEval M e (sigma k)))
        (fofamPATermEval_upSubst V M sigma e d))).
      exact hd.
Qed.

Lemma fofamPAFormulaSat_instTerm :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V)
    phi t (e : nat -> FOFAMOrdinal M),
  fofamPAFormulaSat M e
      (PA.Formula.subst (PA.Formula.instTerm t) phi) <->
  fofamPAFormulaSat M
      (scons _ (fofamPATermEval M e t) e) phi.
Proof.
  intros V M phi t e.
  eapply iff_trans.
  - apply fofamPAFormulaSat_subst.
  - apply fofamPAFormulaSat_ext.
    intros [|n]; reflexivity.
Qed.

Lemma fofamPAFormulaSat_rename_succ :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V)
    phi (e : nat -> FOFAMOrdinal M) d,
  fofamPAFormulaSat M (scons _ d e) (PA.Formula.rename S phi) <->
  fofamPAFormulaSat M e phi.
Proof.
  intros V M phi e d.
  eapply iff_trans.
  - apply fofamPAFormulaSat_rename.
  - apply fofamPAFormulaSat_ext.
    intro n. reflexivity.
Qed.

(* Raw PA natural deduction is sound for every total term algebra.  None of
   the arithmetic laws stored in PA.Model is used by these logical rules, so
   proving this directly avoids inventing an unjustified induction field for
   a nonstandard finite-HF model. *)
Theorem fofam_PA_Prov_soundness :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V)
    G phi,
  PA.Formula.Prov G phi ->
  forall e : nat -> FOFAMOrdinal M,
    (forall psi, In psi G -> fofamPAFormulaSat M e psi) ->
    fofamPAFormulaSat M e phi.
Proof.
  intros V M G phi h.
  induction h; intros e hG; simpl.
  - exact (hG a H).
  - intros ha.
    apply IHh.
    intros x hx.
    simpl in hx.
    destruct hx as [hx | hx].
    + subst x. exact ha.
    + exact (hG x hx).
  - exact (IHh1 e hG (IHh2 e hG)).
  - exfalso. exact (IHh e hG).
  - destruct (classic (fofamPAFormulaSat M e a)) as [ha | hna].
    + left. exact ha.
    + right. exact hna.
  - split; [exact (IHh1 e hG) | exact (IHh2 e hG)].
  - exact (proj1 (IHh e hG)).
  - exact (proj2 (IHh e hG)).
  - left. exact (IHh e hG).
  - right. exact (IHh e hG).
  - destruct (IHh1 e hG) as [ha | hb].
    + apply IHh2.
      intros x hx.
      simpl in hx.
      destruct hx as [hx | hx].
      * subst x. exact ha.
      * exact (hG x hx).
    + apply IHh3.
      intros x hx.
      simpl in hx.
      destruct hx as [hx | hx].
      * subst x. exact hb.
      * exact (hG x hx).
  - intros d.
    apply IHh.
    intros x hx.
    apply in_map_iff in hx.
    destruct hx as [g [hg_eq hg]].
    subst x.
    apply (proj2 (fofamPAFormulaSat_rename_succ V M g e d)).
    exact (hG g hg).
  - apply (proj2 (fofamPAFormulaSat_instTerm V M a t e)).
    exact (IHh e hG (fofamPATermEval M e t)).
  - exists (fofamPATermEval M e t).
    apply (proj1 (fofamPAFormulaSat_instTerm V M a t e)).
    exact (IHh e hG).
  - destruct (IHh1 e hG) as [d hd].
    pose proof (IHh2 (scons _ d e)) as hc_shift.
    assert (hctx : forall x, In x (a :: map (PA.Formula.rename S) G) ->
        fofamPAFormulaSat M (scons _ d e) x).
    {
      intros x hx.
      simpl in hx.
      destruct hx as [hx | hx].
      - subst x. exact hd.
      - apply in_map_iff in hx.
        destruct hx as [g [hg_eq hg]].
        subst x.
        apply (proj2 (fofamPAFormulaSat_rename_succ V M g e d)).
        exact (hG g hg).
    }
    apply (proj1 (fofamPAFormulaSat_rename_succ V M c e d)).
    exact (hc_shift hctx).
  - reflexivity.
  - pose proof (IHh1 e hG) as heq.
    pose proof (proj1 (fofamPAFormulaSat_instTerm V M a s e)
      (IHh2 e hG)) as hs.
    assert (henv : forall n,
        scons _ (fofamPATermEval M e s) e n =
        scons _ (fofamPATermEval M e t) e n).
    {
      intros [|n]; simpl.
      - exact heq.
      - reflexivity.
    }
    pose proof (proj1 (fofamPAFormulaSat_ext V M a
      (scons _ (fofamPATermEval M e s) e)
      (scons _ (fofamPATermEval M e t) e) henv) hs) as ht.
    apply (proj2 (fofamPAFormulaSat_instTerm V M a t e)).
    exact ht.
Qed.
