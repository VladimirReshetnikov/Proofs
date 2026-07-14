(* ===================================================================== *)
(*  NonstandardHFFin.v                                                    *)
(*                                                                       *)
(*  A nonstandard finite-adjunction model from first-order compactness.   *)
(*                                                                       *)
(*  Quantifiers are relativized to the loop-free part of a structure.     *)
(*  One looped marker names a distinguished ordinal through membership.   *)
(*  Every finite part of the closed theory has a tagged standard          *)
(*  Ackermann-HF model; relative completeness then supplies an arbitrary  *)
(*  finite-adjunction model with an ordinal above every standard numeral. *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Lia List Classical_Prop.
From FirstOrder Require Import Fol Relativization Calculus Completeness.
From PAHF Require Import PAHF PAHFTermGraphFunctional
  PAHFRawSemantics PAHFRawSemanticsGraph.

Import ListNotations.

(* ===================== tagged standard structures ==================== *)

Definition Tagged : Type := unit + nat.

Definition tagMem (height : nat) (x y : Tagged) : Prop :=
  match x, y with
  | inl _, inl _ => True
  | inl _, inr y' => y' = ordinal_code height
  | inr _, inl _ => False
  | inr x', inr y' => hf_mem x' y'
  end.

Definition tagEnv (e : nat -> nat) : nat -> Tagged :=
  fun i => inr (e i).

Lemma tagMem_marker_marker : forall height,
  tagMem height (inl tt) (inl tt).
Proof. intro height. exact I. Qed.

Lemma tagMem_marker_ordinary : forall height y,
  tagMem height (inl tt) (inr y) <-> y = ordinal_code height.
Proof. intros height y. reflexivity. Qed.

Lemma tagMem_ordinary_marker : forall height x,
  ~ tagMem height (inr x) (inl tt).
Proof. intros height x. cbn [tagMem]. tauto. Qed.

Lemma tagMem_ordinary_ordinary : forall height x y,
  tagMem height (inr x) (inr y) <-> hf_mem x y.
Proof. intros height x y. reflexivity. Qed.

Lemma tag_loopFree_iff : forall height x,
  ~ tagMem height x x <-> exists n, x = inr n.
Proof.
  intros height [u | n].
  - destruct u. cbn [tagMem]. split.
    + intro h. exfalso. apply h. exact I.
    + intros [n h]. discriminate.
  - cbn [tagMem]. split.
    + intro h. exists n. reflexivity.
    + intros h. apply hf_not_mem_self.
Qed.

Lemma tagEnv_scons : forall d e i,
  tagEnv (scons nat d e) i =
    scons Tagged (inr d) (tagEnv e) i.
Proof. intros d e [|i]; reflexivity. Qed.

Theorem Sat_tag_relativize : forall height f e,
  Sat Tagged (tagMem height) (tagEnv e) (relativize f) <->
    Sat nat hf_mem e f.
Proof.
  intros height f.
  induction f as
      [i j | i j | | a IHa b IHb | a IHa b IHb | a IHa b IHb
      | a IHa | a IHa]; intro e; cbn [relativize Sat loopFreeAt tagEnv tagMem].
  - tauto.
  - split; intro h.
    + now injection h.
    + unfold tagEnv. f_equal. exact h.
  - tauto.
  - specialize (IHa e). specialize (IHb e). tauto.
  - specialize (IHa e). specialize (IHb e). tauto.
  - specialize (IHa e). specialize (IHb e). tauto.
  - split.
    + intros h d.
      apply (proj1 (IHa (scons nat d e))).
      apply (proj2 (Sat_ext Tagged (tagMem height) (relativize a)
        (tagEnv (scons nat d e))
        (scons Tagged (inr d) (tagEnv e))
        (tagEnv_scons d e))).
      apply h. apply hf_not_mem_self.
    + intros h d hd.
      destruct (proj1 (tag_loopFree_iff height d) hd) as [n ->].
      apply (proj1 (Sat_ext Tagged (tagMem height) (relativize a)
        (tagEnv (scons nat n e))
        (scons Tagged (inr n) (tagEnv e))
        (tagEnv_scons n e))).
      apply (proj2 (IHa (scons nat n e))). apply h.
  - split.
    + intros [d [hd ha]].
      destruct (proj1 (tag_loopFree_iff height d) hd) as [n ->].
      exists n. apply (proj1 (IHa (scons nat n e))).
      apply (proj2 (Sat_ext Tagged (tagMem height) (relativize a)
        (tagEnv (scons nat n e))
        (scons Tagged (inr n) (tagEnv e))
        (tagEnv_scons n e))).
      exact ha.
    + intros [n ha].
      exists (inr n). split; [apply hf_not_mem_self |].
      apply (proj1 (Sat_ext Tagged (tagMem height) (relativize a)
        (tagEnv (scons nat n e))
        (scons Tagged (inr n) (tagEnv e))
        (tagEnv_scons n e))).
      apply (proj2 (IHa (scons nat n e))). exact ha.
Qed.

(* ======================== the closed marker theory =================== *)

Definition candidateAt (c : nat) : form :=
  fAnd (loopFreeAt c)
    (fAnd
      (relativize (HF_ordinalLikeAt c))
      (fEx (fAnd (fMem 0 0) (fMem 0 (S c))))).

Definition candidateExists : form := fEx (candidateAt 0).

Definition standardLtFormula (n : nat) : form :=
  formulaAt (fun k => k)
    (PA.Formula.ltTermAt (PA.Term.numeral n) (PA.tVar 0)).

Definition starBound (n : nat) : form :=
  fAll (fImp (candidateAt 0) (relativize (standardLtFormula n))).

Lemma candidateAt_free : forall i c,
  Free i (candidateAt c) -> i = c.
Proof.
  intros i c h. unfold candidateAt in h. cbn [Free] in h.
  destruct h as [h | [h | h]].
  - apply (proj1 (Free_loopFreeAt i c)). exact h.
  - apply (proj1 (Free_relativize i (HF_ordinalLikeAt c))) in h.
    exact (HF_ordinalLikeAt_free i c h).
  - destruct h as [[h | h] | [h | h]]; lia.
Qed.

Lemma Sentence_candidateExists : Sentence candidateExists.
Proof.
  intros i h. unfold candidateExists in h. cbn [Free] in h.
  pose proof (candidateAt_free (S i) 0 h). lia.
Qed.

Lemma PA_numeral_not_free : forall n i,
  ~ PA.Term.Free i (PA.Term.numeral n).
Proof.
  induction n as [|n IH]; intro i; cbn [PA.Term.numeral PA.Term.Free].
  - tauto.
  - exact (IH i).
Qed.

Lemma PA_standardLtFormula_free : forall n i,
  PA.Formula.Free i
    (PA.Formula.ltTermAt (PA.Term.numeral n) (PA.tVar 0)) ->
  i = 0.
Proof.
  intros n i h.
  unfold PA.Formula.ltTermAt in h.
  cbn [PA.Formula.Free PA.Term.Free PA.Term.rename] in h.
  rewrite PA.Term.rename_numeral in h.
  destruct h as [[h | h] | h].
  - exfalso. exact (PA_numeral_not_free n (S i) h).
  - lia.
  - lia.
Qed.

Lemma standardLtFormula_free : forall n i,
  Free i (standardLtFormula n) -> i = 0.
Proof.
  intros n i h.
  unfold standardLtFormula in h.
  destruct (formulaAt_free
    (PA.Formula.ltTermAt (PA.Term.numeral n) (PA.tVar 0))
    (fun k => k) i h) as [k [hk hi]].
  pose proof (PA_standardLtFormula_free n k hk). lia.
Qed.

Lemma Sentence_starBound : forall n, Sentence (starBound n).
Proof.
  intros n i h. unfold starBound in h. cbn [Free] in h.
  destruct h as [h | h].
  - pose proof (candidateAt_free (S i) 0 h). lia.
  - apply (proj1 (Free_relativize (S i) (standardLtFormula n))) in h.
    pose proof (standardLtFormula_free n (S i) h). lia.
Qed.

Definition zeroHFEnv : nat -> nat := fun _ => ordinal_code 0.
Definition zeroPAEnv : nat -> nat := fun _ => 0.
Definition taggedZeroEnv : nat -> Tagged := tagEnv zeroHFEnv.

Lemma Sat_tag_candidateAt_iff : forall height c e,
  Sat Tagged (tagMem height) (tagEnv e) (candidateAt c) <->
    e c = ordinal_code height.
Proof.
  intros height c e. unfold candidateAt. cbn [Sat loopFreeAt].
  split.
  - intros [_ [_ [d [hloop hmem]]]].
    destruct d as [u | n].
    + destruct u. cbn [tagEnv tagMem] in hmem. exact hmem.
    + exfalso. cbn [tagEnv tagMem] in hloop.
      exact (hf_not_mem_self n hloop).
  - intro hc. split.
    + unfold tagEnv. apply hf_not_mem_self.
    + split.
      * apply (proj2 (Sat_tag_relativize height (HF_ordinalLikeAt c) e)).
        apply (proj2 (HF_ordinalLikeAt_spec nat hf_mem e c)).
        rewrite hc. apply OrdinalLike_of_hf_ordinal_like.
        apply ordinal_code_ordinal_like.
      * exists (inl tt). cbn [tagEnv tagMem]. split; [exact I | exact hc].
Qed.

Lemma Sat_tag_candidateExists : forall height,
  Sat Tagged (tagMem height) taggedZeroEnv candidateExists.
Proof.
  intro height. unfold candidateExists. cbn [Sat].
  exists (inr (ordinal_code height)).
  apply (proj2 (Sat_ext Tagged (tagMem height) (candidateAt 0)
    (tagEnv (scons nat (ordinal_code height) zeroHFEnv))
    (scons Tagged (inr (ordinal_code height)) taggedZeroEnv)
    (tagEnv_scons (ordinal_code height) zeroHFEnv))).
  apply (proj2 (Sat_tag_candidateAt_iff height 0
    (scons nat (ordinal_code height) zeroHFEnv))).
  reflexivity.
Qed.

Lemma Sat_standardLtFormula_exact : forall n height,
  Sat nat hf_mem
      (scons nat (ordinal_code height) zeroHFEnv)
      (standardLtFormula n) <->
    n < height.
Proof.
  intros n height. unfold standardLtFormula.
  rewrite (formulaAt_exact
    (PA.Formula.ltTermAt (PA.Term.numeral n) (PA.tVar 0))
    (fun k => k) (scons nat height zeroPAEnv)
    (scons nat (ordinal_code height) zeroHFEnv)).
  - rewrite PA.Formula.ltTermAt_nat.
    rewrite PA.Term.eval_numeral_natModel. reflexivity.
  - intros [|k]; reflexivity.
Qed.

Lemma Sat_tag_starBound_iff : forall height n,
  Sat Tagged (tagMem height) taggedZeroEnv (starBound n) <->
    n < height.
Proof.
  intros height n. unfold starBound. cbn [Sat]. split.
  - intro h.
    specialize (h (inr (ordinal_code height))).
    assert (hc : Sat Tagged (tagMem height)
        (scons Tagged (inr (ordinal_code height)) taggedZeroEnv)
        (candidateAt 0)).
    {
      apply (proj1 (Sat_ext Tagged (tagMem height) (candidateAt 0)
        (tagEnv (scons nat (ordinal_code height) zeroHFEnv))
        (scons Tagged (inr (ordinal_code height)) taggedZeroEnv)
        (tagEnv_scons (ordinal_code height) zeroHFEnv))).
      apply (proj2 (Sat_tag_candidateAt_iff height 0
        (scons nat (ordinal_code height) zeroHFEnv))). reflexivity.
    }
    specialize (h hc).
    apply (proj1 (Sat_standardLtFormula_exact n height)).
    apply (proj1 (Sat_tag_relativize height (standardLtFormula n)
      (scons nat (ordinal_code height) zeroHFEnv))).
    apply (proj2 (Sat_ext Tagged (tagMem height)
      (relativize (standardLtFormula n))
      (tagEnv (scons nat (ordinal_code height) zeroHFEnv))
      (scons Tagged (inr (ordinal_code height)) taggedZeroEnv)
      (tagEnv_scons (ordinal_code height) zeroHFEnv))).
    exact h.
  - intro hlt. intros d hc.
    assert (hd : ~ tagMem height d d).
    {
      unfold candidateAt in hc. cbn [Sat] in hc. exact (proj1 hc).
    }
    destruct (proj1 (tag_loopFree_iff height d) hd) as [c ->].
    assert (hc' : Sat Tagged (tagMem height)
        (tagEnv (scons nat c zeroHFEnv)) (candidateAt 0)).
    {
      apply (proj2 (Sat_ext Tagged (tagMem height) (candidateAt 0)
        (tagEnv (scons nat c zeroHFEnv))
        (scons Tagged (inr c) taggedZeroEnv)
        (tagEnv_scons c zeroHFEnv))). exact hc.
    }
    pose proof (proj1 (Sat_tag_candidateAt_iff height 0
      (scons nat c zeroHFEnv)) hc') as hcEq.
    cbn [scons] in hcEq. subst c.
    apply (proj1 (Sat_ext Tagged (tagMem height)
      (relativize (standardLtFormula n))
      (tagEnv (scons nat (ordinal_code height) zeroHFEnv))
      (scons Tagged (inr (ordinal_code height)) taggedZeroEnv)
      (tagEnv_scons (ordinal_code height) zeroHFEnv))).
    apply (proj2 (Sat_tag_relativize height (standardLtFormula n)
      (scons nat (ordinal_code height) zeroHFEnv))).
    apply (proj2 (Sat_standardLtFormula_exact n height)). exact hlt.
Qed.

Inductive NonstandardHFFinTheory : form -> Prop :=
| NSHF_HFFin : forall g,
    HFFinAx_s g -> NonstandardHFFinTheory (relativize g)
| NSHF_candidate : NonstandardHFFinTheory candidateExists
| NSHF_bound : forall n, NonstandardHFFinTheory (starBound n).

Lemma Sentences_NonstandardHFFinTheory :
  Sentences NonstandardHFFinTheory.
Proof.
  intros g hg. destruct hg as [g hg | | n].
  - apply Sentence_relativize. exact (Sentences_HFFin g hg).
  - exact Sentence_candidateExists.
  - apply Sentence_starBound.
Qed.

Lemma Sat_tag_relativized_HFFin : forall height g,
  HFFinAx_s g ->
  Sat Tagged (tagMem height) taggedZeroEnv (relativize g).
Proof.
  intros height g hg.
  apply (proj2 (Sat_tag_relativize height g zeroHFEnv)).
  exact (standard_sat_HFFin zeroHFEnv g hg).
Qed.

Lemma Sat_tag_theory_mono : forall low high g,
  low <= high ->
  NonstandardHFFinTheory g ->
  Sat Tagged (tagMem low) taggedZeroEnv g ->
  Sat Tagged (tagMem high) taggedZeroEnv g.
Proof.
  intros low high g hle hg hsat.
  destruct hg as [g hg | | n].
  - apply Sat_tag_relativized_HFFin. exact hg.
  - apply Sat_tag_candidateExists.
  - apply (proj2 (Sat_tag_starBound_iff high n)).
    apply Nat.lt_le_trans with low.
    + exact (proj1 (Sat_tag_starBound_iff low n) hsat).
    + exact hle.
Qed.

Lemma finite_NonstandardHFFinTheory_tag_model : forall L,
  (forall g, In g L -> NonstandardHFFinTheory g) ->
  exists height,
    forall g, In g L ->
      Sat Tagged (tagMem height) taggedZeroEnv g.
Proof.
  induction L as [|a L IH]; intro hL.
  - exists 0. intros g hg. contradiction.
  - assert (hTail : forall g, In g L -> NonstandardHFFinTheory g).
    { intros g hg. apply hL. now right. }
    destruct (IH hTail) as [height hSatTail].
    pose proof (hL a (or_introl eq_refl)) as ha.
    destruct ha as [g hg | | n].
    + exists height. intros x [hx | hx].
      * subst x. apply Sat_tag_relativized_HFFin. exact hg.
      * exact (hSatTail x hx).
    + exists height. intros x [hx | hx].
      * subst x. apply Sat_tag_candidateExists.
      * exact (hSatTail x hx).
    + exists (Nat.max height (S n)). intros x [hx | hx].
      * subst x. apply (proj2 (Sat_tag_starBound_iff (Nat.max height (S n)) n)).
        lia.
      * apply (Sat_tag_theory_mono height (Nat.max height (S n)) x).
        -- apply Nat.le_max_l.
        -- exact (hTail x hx).
        -- exact (hSatTail x hx).
Qed.

Theorem NonstandardHFFinTheory_consistent :
  BCon NonstandardHFFinTheory nil.
Proof.
  intros [Gb [hGb hp]]. rewrite app_nil_r in hp.
  destruct (finite_NonstandardHFFinTheory_tag_model Gb hGb)
    as [height hSat].
  exact (soundness Tagged (tagMem height) Gb fBot hp taggedZeroEnv hSat).
Qed.

Theorem NonstandardHFFinTheory_model :
  exists (V : Type) (mem : V -> V -> Prop) (v : nat -> V),
    forall g, NonstandardHFFinTheory g -> Sat V mem v g.
Proof.
  destruct (model_of_BCon NonstandardHFFinTheory nil
    Sentences_NonstandardHFFinTheory NonstandardHFFinTheory_consistent)
    as [V [mem [v [hTheory hNil]]]].
  exists V, mem, v. exact hTheory.
Qed.

(* ================= decoding the compactness model ==================== *)

Lemma Sat_ext_only_zero :
  forall (V : Type) (mem : V -> V -> Prop) f e1 e2,
  (forall i, Free i f -> i = 0) ->
  e1 0 = e2 0 ->
  (Sat V mem e1 f <-> Sat V mem e2 f).
Proof.
  intros V mem f e1 e2 hfree hzero.
  apply Sat_ext_free. intros i hi.
  rewrite (hfree i hi). exact hzero.
Qed.

Theorem nonstandardHFFin_fofam_exists :
  exists (V : Type) (M : FirstOrderFiniteAdjunctionModel V)
      (star : FOFAMOrdinal M),
    (forall n,
      Sat V (foam_mem V M) (fun _ => proj1_sig star)
        (standardLtFormula n)) /\
    (forall n,
      fofamPAFormulaSat M (fun _ => star)
        (PA.Formula.ltTermAt (PA.Term.numeral n) (PA.tVar 0))).
Proof.
  destruct NonstandardHFFinTheory_model as [A [mem [v hTheory]]].
  pose proof (hTheory candidateExists NSHF_candidate) as hCandidateExists.
  unfold candidateExists in hCandidateExists. cbn [Sat] in hCandidateExists.
  destruct hCandidateExists as [c hc].
  pose proof hc as hcFull.
  unfold candidateAt in hc. cbn [Sat loopFreeAt] in hc.
  destruct hc as [hcLoop [hcOrdinal hcMarker]].

  pose (starD := (exist _ c hcLoop : RelDomain mem)).
  pose (eD := (fun _ : nat => starD)).

  assert (hHF : forall g, HFFinAx_s g ->
      Sat (RelDomain mem) (relDomainMem mem) eD g).
  {
    intros g hg.
    apply (proj1 (Sat_relativize A mem g eD)).
    apply (proj1 (Sat_sentence_inv A mem (relativize g)
      (Sentence_relativize g (Sentences_HFFin g hg)) v
      (fun n => proj1_sig (eD n)))).
    apply hTheory. constructor. exact hg.
  }

  assert (hcOrdinalAmbient :
      Sat A mem (fun n => proj1_sig (eD n))
        (relativize (HF_ordinalLikeAt 0))).
  {
    assert (hfree : forall i,
        Free i (relativize (HF_ordinalLikeAt 0)) -> i = 0).
    {
      intros i hi.
      apply (proj1 (Free_relativize i (HF_ordinalLikeAt 0))) in hi.
      exact (HF_ordinalLikeAt_free i 0 hi).
    }
    apply (proj1 (Sat_ext_only_zero A mem
      (relativize (HF_ordinalLikeAt 0))
      (scons A c v) (fun n => proj1_sig (eD n))
      hfree eq_refl)).
    exact hcOrdinal.
  }
  pose proof (proj1 (Sat_relativize A mem (HF_ordinalLikeAt 0) eD)
    hcOrdinalAmbient) as hcOrdinalDomain.
  pose proof (proj1 (HF_ordinalLikeAt_spec
    (RelDomain mem) (relDomainMem mem) eD 0) hcOrdinalDomain)
    as hcOrdinalLike.
  change (OrdinalLike (relDomainMem mem) starD) in hcOrdinalLike.

  pose (M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s
    (RelDomain mem) (relDomainMem mem) eD hHF).
  assert (hcOrdinalM : OrdinalLike
      (foam_mem (RelDomain mem) M) starD).
  { exact hcOrdinalLike. }
  pose (star := (exist _ starD hcOrdinalM : FOFAMOrdinal M)).

  assert (hTranslated : forall n,
      Sat (RelDomain mem) (foam_mem (RelDomain mem) M)
        (fun _ => proj1_sig star) (standardLtFormula n)).
  {
    intro n.
    pose proof (hTheory (starBound n) (NSHF_bound n)) as hBound.
    unfold starBound in hBound. cbn [Sat] in hBound.
    pose proof (hBound c hcFull) as hBoundAtC.
    assert (hBoundAmbient :
        Sat A mem (fun k => proj1_sig (eD k))
          (relativize (standardLtFormula n))).
    {
      assert (hfree : forall i,
          Free i (relativize (standardLtFormula n)) -> i = 0).
      {
        intros i hi.
        apply (proj1 (Free_relativize i (standardLtFormula n))) in hi.
        exact (standardLtFormula_free n i hi).
      }
      apply (proj1 (Sat_ext_only_zero A mem
        (relativize (standardLtFormula n))
        (scons A c v) (fun k => proj1_sig (eD k))
        hfree eq_refl)).
      exact hBoundAtC.
    }
    pose proof (proj1 (Sat_relativize A mem
      (standardLtFormula n) eD) hBoundAmbient) as hBoundDomain.
    exact hBoundDomain.
  }

  assert (hRaw : forall n,
      fofamPAFormulaSat M (fun _ => star)
        (PA.Formula.ltTermAt (PA.Term.numeral n) (PA.tVar 0))).
  {
    intro n.
    apply (proj1 (formulaAt_iff_fofamPAFormulaSat
      (RelDomain mem) M (termGraphAt_outputs_eq (RelDomain mem) M)
      (PA.Formula.ltTermAt (PA.Term.numeral n) (PA.tVar 0))
      (fun k => k) (fun _ => proj1_sig star) (fun _ => star)
      (fun k hk => eq_refl))).
    exact (hTranslated n).
  }

  exists (RelDomain mem), M, star. split.
  - exact hTranslated.
  - exact hRaw.
Qed.

Corollary nonstandardHFFin_translated_bounds_exists :
  exists (V : Type) (M : FirstOrderFiniteAdjunctionModel V)
      (star : FOFAMOrdinal M),
    forall n,
      Sat V (foam_mem V M) (fun _ => proj1_sig star)
        (standardLtFormula n).
Proof.
  destruct nonstandardHFFin_fofam_exists as [V [M [star [h _]]]].
  exists V, M, star. exact h.
Qed.

Corollary nonstandardHFFin_raw_bounds_exists :
  exists (V : Type) (M : FirstOrderFiniteAdjunctionModel V)
      (star : FOFAMOrdinal M),
    forall n,
      fofamPAFormulaSat M (fun _ => star)
        (PA.Formula.ltTermAt (PA.Term.numeral n) (PA.tVar 0)).
Proof.
  destruct nonstandardHFFin_fofam_exists as [V [M [star [_ h]]]].
  exists V, M, star. exact h.
Qed.
