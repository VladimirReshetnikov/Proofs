(**
  Canonical least/default selectors in every raw model of first-order PA.

  [CanonicalSelector] isolates definable least-number and order trichotomy as
  an abstract boundary.  Here both properties are derived from semantic
  validity of the genuine sealed PA axioms.  The sole induction step is an
  object-language instance of [PA.Formula.inductionForm]; no [PA.Model] or
  meta-level induction field is introduced into the carrier.
*)

From Stdlib Require Import List Arith Lia Classical.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF PAHFRawSemantics
  PAHFProofTranslationSemantic.
From PAFiniteBasisReduction Require Import HierarchyReduction
  FiniteSkolemHull CanonicalSelector.

Import ListNotations.
Import PAHierarchyReduction.
Import PAFiniteSkolemHull.
Import PACanonicalSelector.

Module PACanonicalSelectorPA.

Definition RawPASatisfies (M : RawPAModel) : Prop :=
  RawModelSatisfies M PA.Formula.Ax_s.

(** Contextual semantic soundness for the bounded-proof packaging used by
    PAHF's library of arithmetic order theorems. *)
Theorem raw_sat_of_BProv_axs_context :
  forall (M : RawPAModel) G phi,
    RawPASatisfies M ->
    PA.Formula.BProv PA.Formula.Ax_s G phi ->
    forall e : nat -> M,
      (forall g, In g G -> raw_formula_sat M e g) ->
      raw_formula_sat M e phi.
Proof.
  intros M G phi hPA [L [hL hProv]] e hG.
  apply (raw_PA_Prov_soundness M (L ++ G) phi hProv e).
  intros psi hpsi.
  apply in_app_iff in hpsi.
  destruct hpsi as [hpsi | hpsi].
  - exact (hPA psi (hL psi hpsi) e).
  - exact (hG psi hpsi).
Qed.

Corollary raw_sat_of_BProv_axs :
  forall (M : RawPAModel) phi,
    RawPASatisfies M ->
    PA.Formula.BProv PA.Formula.Ax_s [] phi ->
    forall e : nat -> M, raw_formula_sat M e phi.
Proof.
  intros M phi hPA hProv e.
  apply (raw_sat_of_BProv_axs_context M [] phi hPA hProv e).
  intros g hg. contradiction.
Qed.

Definition rawLe (M : RawPAModel) (x y : M) : Prop :=
  exists d : M, raw_add M x d = y.

Lemma raw_sat_ltTermAt_vars : forall (M : RawPAModel) x y e,
  raw_formula_sat M (scons M x (scons M y e))
      (PA.Formula.ltTermAt (PA.tVar 0) (PA.tVar 1)) <->
  rawLt M x y.
Proof.
  intros M x y e.
  unfold PA.Formula.ltTermAt, rawLt.
  simpl. reflexivity.
Qed.

Lemma raw_sat_leTermAt_vars : forall (M : RawPAModel) x y e,
  raw_formula_sat M (scons M x (scons M y e))
      (PA.Formula.leTermAt (PA.tVar 0) (PA.tVar 1)) <->
  rawLe M x y.
Proof.
  intros M x y e.
  unfold PA.Formula.leTermAt, rawLe.
  simpl. reflexivity.
Qed.

Theorem raw_not_lt_zero : forall (M : RawPAModel),
  RawPASatisfies M ->
  forall x : M, ~ rawLt M x (raw_zero M).
Proof.
  intros M hPA x hlt.
  set (f := PA.Formula.ltTermAt (PA.tVar 0) PA.tZero).
  set (G := [f] : list PA.formula).
  assert (hass : PA.Formula.BProv PA.Formula.Ax_s G f).
  {
    apply PA.Formula.BProv_ass.
    unfold G. simpl. left. reflexivity.
  }
  assert (hzeroLe : PA.Formula.BProv PA.Formula.Ax_s G
      (PA.Formula.leTermAt PA.tZero (PA.tVar 0))).
  {
    apply PA.Formula.BProv_Ax_s_leTermAt_zero_left.
  }
  pose proof (PA.Formula.BProv_Ax_s_ltTermAt_leTermAt_bot
    G (PA.tVar 0) PA.tZero hass hzeroLe) as hbot.
  set (e := fun _ : nat => raw_zero M).
  assert (hsat : raw_formula_sat M (scons M x e) f).
  {
    unfold f, PA.Formula.ltTermAt, rawLt in *.
    simpl in *. exact hlt.
  }
  apply (raw_sat_of_BProv_axs_context M G PA.pBot hPA hbot
    (scons M x e)).
  intros g hg.
  unfold G in hg. simpl in hg.
  destruct hg as [hg | []]. subst g. exact hsat.
Qed.

Theorem raw_lt_succ_cases : forall (M : RawPAModel),
  RawPASatisfies M ->
  forall z x : M,
    rawLt M z (raw_succ M x) ->
    rawLt M z x \/ z = x.
Proof.
  intros M hPA z x hlt.
  set (f := PA.Formula.ltTermAt
    (PA.tVar 0) (PA.tSucc (PA.tVar 1))).
  set (G := [f] : list PA.formula).
  assert (hass : PA.Formula.BProv PA.Formula.Ax_s G f).
  {
    apply PA.Formula.BProv_ass.
    unfold G. simpl. left. reflexivity.
  }
  pose proof (PA.Formula.BProv_Ax_s_ltTermAt_succ_right_cases
    G (PA.tVar 0) (PA.tVar 1) hass) as hcases.
  set (e := fun _ : nat => raw_zero M).
  assert (hsat : raw_formula_sat M
      (scons M z (scons M x e)) f).
  {
    unfold f, PA.Formula.ltTermAt, rawLt in *.
    simpl in *. exact hlt.
  }
  assert (hG : forall g, In g G ->
      raw_formula_sat M (scons M z (scons M x e)) g).
  {
    intros g hg.
    unfold G in hg. simpl in hg.
    destruct hg as [hg | []]. subst g. exact hsat.
  }
  pose proof (raw_sat_of_BProv_axs_context M G _ hPA hcases
    (scons M z (scons M x e)) hG) as hout.
  unfold PA.Formula.ltTermAt, rawLt in *.
  simpl in *. exact hout.
Qed.

Theorem raw_le_or_gt : forall (M : RawPAModel),
  RawPASatisfies M ->
  forall x y : M, rawLe M x y \/ rawLt M y x.
Proof.
  intros M hPA x y.
  set (e := fun _ : nat => raw_zero M).
  pose proof (raw_sat_of_BProv_axs M _ hPA
    (PA.Formula.BProv_Ax_s_leTermAt_or_gtTermAt []
      (PA.tVar 0) (PA.tVar 1))
    (scons M x (scons M y e))) as h.
  unfold PA.Formula.leTermAt, PA.Formula.ltTermAt,
    rawLe, rawLt in *.
  simpl in *. exact h.
Qed.

Theorem raw_le_antisymm : forall (M : RawPAModel),
  RawPASatisfies M ->
  forall x y : M,
    rawLe M x y -> rawLe M y x -> x = y.
Proof.
  intros M hPA x y hxy hyx.
  set (fxy := PA.Formula.leTermAt (PA.tVar 0) (PA.tVar 1)).
  set (fyx := PA.Formula.leTermAt (PA.tVar 1) (PA.tVar 0)).
  set (G := [fxy; fyx] : list PA.formula).
  assert (hassXY : PA.Formula.BProv PA.Formula.Ax_s G fxy).
  {
    apply PA.Formula.BProv_ass.
    unfold G. simpl. left. reflexivity.
  }
  assert (hassYX : PA.Formula.BProv PA.Formula.Ax_s G fyx).
  {
    apply PA.Formula.BProv_ass.
    unfold G. simpl. right. left. reflexivity.
  }
  pose proof (PA.Formula.BProv_Ax_s_eq_of_leTermAt_leTermAt
    G (PA.tVar 0) (PA.tVar 1) hassXY hassYX) as heq.
  set (e := fun _ : nat => raw_zero M).
  assert (hsatXY : raw_formula_sat M
      (scons M x (scons M y e)) fxy).
  {
    unfold fxy, PA.Formula.leTermAt, rawLe in *.
    simpl in *. exact hxy.
  }
  assert (hsatYX : raw_formula_sat M
      (scons M x (scons M y e)) fyx).
  {
    unfold fyx, PA.Formula.leTermAt, rawLe in *.
    simpl in *. exact hyx.
  }
  pose proof (raw_sat_of_BProv_axs_context M G _ hPA heq
    (scons M x (scons M y e))) as hsound.
  apply hsound.
  intros g hg.
  unfold G in hg. simpl in hg.
  destruct hg as [hg | [hg | []]]; subst g; assumption.
Qed.

Theorem raw_order_trichotomy : forall (M : RawPAModel),
  RawPASatisfies M -> RawLtTrichotomy M.
Proof.
  intros M hPA x y.
  destruct (raw_le_or_gt M hPA x y) as [hxy | hyx].
  - destruct (raw_le_or_gt M hPA y x) as [hyx' | hxy'].
    + left. exact (raw_le_antisymm M hPA x y hxy hyx').
    + right. left. exact hxy'.
  - right. right. exact hyx.
Qed.

Definition noSmallerFormula (body : PA.formula) : PA.formula :=
  PA.pAll (PA.pImp
    (PA.Formula.ltTermAt (PA.tVar 0) (PA.tVar 1))
    (PA.pImp (selectorProbeBody body) PA.pBot)).

Lemma raw_noSmallerFormula : forall (M : RawPAModel) body out e,
  raw_formula_sat M (scons M out e) (noSmallerFormula body) <->
  forall z, rawLt M z out ->
    ~ raw_formula_sat M (scons M z e) body.
Proof.
  intros M body out e.
  unfold noSmallerFormula. simpl.
  split.
  - intros h z hlt hz.
    apply (h z).
    + apply (proj2 (raw_sat_ltTermAt_vars M z out e)). exact hlt.
    + apply (proj2 (raw_selectorProbeBody M body e out z)). exact hz.
  - intros h z hlt hz.
    apply (h z).
    + apply (proj1 (raw_sat_ltTermAt_vars M z out e)). exact hlt.
    + apply (proj1 (raw_selectorProbeBody M body e out z)). exact hz.
Qed.

(** Global validity of a universal closure can be opened again at an
    arbitrary valuation by feeding it the values of that valuation. *)
Lemma raw_closeN_valid_inv : forall (M : RawPAModel) k phi,
  (forall e : nat -> M,
    raw_formula_sat M e (PA.Formula.closeN k phi)) ->
  forall e : nat -> M, raw_formula_sat M e phi.
Proof.
  intros M k.
  induction k as [|k IH]; intros phi hvalid e.
  - exact (hvalid e).
  - simpl in hvalid.
    pose proof (IH (PA.pAll phi) hvalid
      (fun n => e (S n))) as hall.
    simpl in hall.
    pose proof (hall (e 0)) as hphi.
    assert (henv : forall n,
        scons M (e 0) (fun n => e (S n)) n = e n).
    { intros [|n]; reflexivity. }
    apply (proj1 (raw_formula_sat_ext M phi
      (scons M (e 0) (fun n => e (S n))) e henv)).
    exact hphi.
Qed.

Lemma raw_sealPA_valid_inv : forall (M : RawPAModel) phi,
  (forall e : nat -> M,
    raw_formula_sat M e (PA.Formula.sealPA phi)) ->
  forall e : nat -> M, raw_formula_sat M e phi.
Proof.
  intros M phi hvalid.
  unfold PA.Formula.sealPA in hvalid.
  exact (raw_closeN_valid_inv M (PA.Formula.bound phi) phi hvalid).
Qed.

Lemma raw_sat_substZero : forall (M : RawPAModel) phi e,
  raw_formula_sat M e
      (PA.Formula.subst PA.Formula.substZero phi) <->
  raw_formula_sat M (scons M (raw_zero M) e) phi.
Proof.
  intros M phi e.
  rewrite raw_formula_sat_subst.
  apply raw_formula_sat_ext.
  intros [|n]; reflexivity.
Qed.

Lemma raw_sat_substSuccVar : forall (M : RawPAModel) phi e x,
  raw_formula_sat M (scons M x e)
      (PA.Formula.subst PA.Formula.substSuccVar phi) <->
  raw_formula_sat M (scons M (raw_succ M x) e) phi.
Proof.
  intros M phi e x.
  rewrite raw_formula_sat_subst.
  apply raw_formula_sat_ext.
  intros [|n]; reflexivity.
Qed.

Theorem raw_definable_induction : forall (M : RawPAModel),
  RawPASatisfies M ->
  forall phi e,
    raw_formula_sat M (scons M (raw_zero M) e) phi ->
    (forall x,
      raw_formula_sat M (scons M x e) phi ->
      raw_formula_sat M (scons M (raw_succ M x) e) phi) ->
    forall x, raw_formula_sat M (scons M x e) phi.
Proof.
  intros M hPA phi e hzero hsucc.
  assert (hsealed : forall v : nat -> M,
      raw_formula_sat M v
        (PA.Formula.sealPA (PA.Formula.inductionForm phi))).
  {
    intro v.
    exact (hPA _ (PA.Formula.Ax_s_induction phi) v).
  }
  pose proof (raw_sealPA_valid_inv M
    (PA.Formula.inductionForm phi) hsealed e) as hind.
  unfold PA.Formula.inductionForm in hind.
  simpl in hind.
  apply hind. split.
  - apply (proj2 (raw_sat_substZero M phi e)). exact hzero.
  - intros x hx.
    apply (proj2 (raw_sat_substSuccVar M phi e x)).
    exact (hsucc x hx).
Qed.

(** The usual least-number proof, carried out semantically with one genuine
    first-order PA induction instance for [noSmallerFormula body]. *)
Theorem raw_definable_least_witness : forall (M : RawPAModel),
  RawPASatisfies M ->
  forall body e,
    (exists d, raw_formula_sat M (scons M d e) body) ->
    exists out,
      raw_formula_sat M (scons M out e) body /\
      forall z, rawLt M z out ->
        ~ raw_formula_sat M (scons M z e) body.
Proof.
  intros M hPA body e hex.
  apply NNPP. intro hnone.
  assert (hNoSmallerAll : forall x,
      raw_formula_sat M (scons M x e) (noSmallerFormula body)).
  {
    apply (raw_definable_induction M hPA
      (noSmallerFormula body) e).
    - apply (proj2 (raw_noSmallerFormula M body (raw_zero M) e)).
      intros z hlt.
      exfalso. exact (raw_not_lt_zero M hPA z hlt).
    - intros x hx.
      pose proof (proj1 (raw_noSmallerFormula M body x e) hx) as hxNo.
      apply (proj2 (raw_noSmallerFormula M body (raw_succ M x) e)).
      intros z hzLt hzBody.
      destruct (raw_lt_succ_cases M hPA z x hzLt)
        as [hzLtX | hzx].
      + exact (hxNo z hzLtX hzBody).
      + subst z.
        apply hnone.
        exists x. split; [exact hzBody |].
        intros z hzLtX.
        exact (hxNo z hzLtX).
  }
  destruct hex as [d hd].
  apply hnone.
  exists d. split; [exact hd |].
  exact (proj1 (raw_noSmallerFormula M body d e)
    (hNoSmallerAll d)).
Qed.

Theorem raw_definable_least_number_of_pa : forall (M : RawPAModel),
  RawPASatisfies M -> RawDefinableLeastNumber M.
Proof.
  intros M hPA body e hex.
  exact (raw_definable_least_witness M hPA body e hex).
Qed.

Theorem rawCanonicalSelectorGraph_total_of_pa : forall (M : RawPAModel),
  RawPASatisfies M ->
  forall body e, exists out,
    rawCanonicalSelectorGraph M body e out.
Proof.
  intros M hPA.
  apply rawCanonicalSelectorGraph_total.
  exact (raw_definable_least_number_of_pa M hPA).
Qed.

Theorem rawCanonicalSelectorGraph_functional_of_pa :
  forall (M : RawPAModel),
    RawPASatisfies M ->
    forall body e x y,
      rawCanonicalSelectorGraph M body e x ->
      rawCanonicalSelectorGraph M body e y ->
      x = y.
Proof.
  intros M hPA.
  apply rawCanonicalSelectorGraph_functional.
  exact (raw_order_trichotomy M hPA).
Qed.

Corollary raw_canonicalSelectorFormula_exists_unique_of_pa :
  forall (M : RawPAModel),
    RawPASatisfies M ->
    forall body e, exists! out,
      raw_formula_sat M (scons M out e)
        (canonicalSelectorFormula body).
Proof.
  intros M hPA.
  apply raw_canonicalSelectorFormula_exists_unique.
  - exact (raw_definable_least_number_of_pa M hPA).
  - exact (raw_order_trichotomy M hPA).
Qed.

Corollary canonicalSkolemHull_satisfies_rank_fragment_of_pa :
  forall (M : RawPAModel) (seed : M) n,
    RawPASatisfies M ->
    RawModelSatisfies
      (skolemHullRawModel M seed (S (rankFragmentSyntaxRank n))
        (rawCanonicalSelector M))
      (PARankFragment n).
Proof.
  intros M seed n hPA.
  apply canonicalSkolemHull_satisfies_rank_fragment.
  - exact (raw_definable_least_number_of_pa M hPA).
  - exact hPA.
Qed.

(** --------------------------------------------------------------------
    Unconditional instance for the raw ordinal arithmetic extracted from an
    arbitrary first-order finite-adjunction model. *)

Definition fofamRawPAModel {V : Type}
    (M : FirstOrderFiniteAdjunctionModel V) : RawPAModel :=
  {| raw_carrier := FOFAMOrdinal M;
     raw_zero := fofamOrdinalZero M;
     raw_succ := fofamOrdinalSucc M;
     raw_add := fofamOrdinalAdd M;
     raw_mul := fofamOrdinalMul M |}.

Lemma raw_term_eval_fofam : forall (V : Type)
    (M : FirstOrderFiniteAdjunctionModel V)
    (e : nat -> FOFAMOrdinal M) t,
  raw_term_eval (fofamRawPAModel M) e t =
  fofamPATermEval M e t.
Proof.
  intros V M e t.
  induction t; simpl; try reflexivity.
  - now rewrite IHt.
  - now rewrite IHt1, IHt2.
  - now rewrite IHt1, IHt2.
Qed.

Lemma raw_formula_sat_fofam : forall (V : Type)
    (M : FirstOrderFiniteAdjunctionModel V)
    (e : nat -> FOFAMOrdinal M) phi,
  raw_formula_sat (fofamRawPAModel M) e phi <->
  fofamPAFormulaSat M e phi.
Proof.
  intros V M e phi.
  revert e.
  induction phi as [a b | | a IHa b IHb | a IHa b IHb |
      a IHa b IHb | a IHa | a IHa]; intro e; simpl.
  - rewrite !raw_term_eval_fofam. reflexivity.
  - reflexivity.
  - rewrite IHa, IHb. reflexivity.
  - rewrite IHa, IHb. reflexivity.
  - rewrite IHa, IHb. reflexivity.
  - split; intros h x.
    + apply (proj1 (IHa (scons _ x e))). exact (h x).
    + apply (proj2 (IHa (scons _ x e))). exact (h x).
  - split; intros [x hx]; exists x.
    + apply (proj1 (IHa (scons _ x e))). exact hx.
    + apply (proj2 (IHa (scons _ x e))). exact hx.
Qed.

Theorem fofam_raw_pa_satisfies : forall (V : Type)
    (M : FirstOrderFiniteAdjunctionModel V),
  RawPASatisfies (fofamRawPAModel M).
Proof.
  intros V M phi hphi e.
  apply (proj2 (raw_formula_sat_fofam V M e phi)).
  exact (fofam_PA_Ax_s_valid V M phi e hphi).
Qed.

Corollary fofam_raw_definable_least_number : forall (V : Type)
    (M : FirstOrderFiniteAdjunctionModel V),
  RawDefinableLeastNumber (fofamRawPAModel M).
Proof.
  intros V M.
  apply raw_definable_least_number_of_pa.
  apply fofam_raw_pa_satisfies.
Qed.

Corollary fofam_raw_order_trichotomy : forall (V : Type)
    (M : FirstOrderFiniteAdjunctionModel V),
  RawLtTrichotomy (fofamRawPAModel M).
Proof.
  intros V M.
  apply raw_order_trichotomy.
  apply fofam_raw_pa_satisfies.
Qed.

Definition fofamCanonicalSelector {V : Type}
    (M : FirstOrderFiniteAdjunctionModel V) :
    PA.formula -> (nat -> fofamRawPAModel M) -> fofamRawPAModel M :=
  rawCanonicalSelector (fofamRawPAModel M).

Theorem fofamCanonicalSelector_formula_exists_unique :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V) body e,
    exists! out,
      raw_formula_sat (fofamRawPAModel M) (scons _ out e)
        (canonicalSelectorFormula body).
Proof.
  intros V M body e.
  apply raw_canonicalSelectorFormula_exists_unique_of_pa.
  apply fofam_raw_pa_satisfies.
Qed.

Theorem fofamCanonicalSkolemHull_satisfies_rank_fragment :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V)
    (seed : fofamRawPAModel M) n,
    RawModelSatisfies
      (skolemHullRawModel (fofamRawPAModel M) seed
        (S (rankFragmentSyntaxRank n)) (fofamCanonicalSelector M))
      (PARankFragment n).
Proof.
  intros V M seed n.
  apply canonicalSkolemHull_satisfies_rank_fragment_of_pa.
  apply fofam_raw_pa_satisfies.
Qed.

End PACanonicalSelectorPA.
