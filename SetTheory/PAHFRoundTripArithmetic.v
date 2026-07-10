(* ===================================================================== *)
(*  PAHFRoundTripArithmetic.v                                           *)
(*                                                                       *)
(*  Arithmetic-side reduction for the PA -> HF -> PA round trip.         *)
(*                                                                       *)
(*  The semantic composite identity in the standard model is already a  *)
(*  consequence of the two exactness theorems in PAHF.  The deductive    *)
(*  statement is reduced here, by a kernel-checked formula induction, to *)
(*  the equality atom and the two relativized quantifier constructors.   *)
(*  No semantic-completeness principle for true arithmetic is assumed.   *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Lia List.
From SetTheory Require Import Fol Calculus PAHF PAHFOrdinalCode
  PAHFOrdinalCodeTotalInduction PAHFDeductiveAssembly.

Import ListNotations.
Import PA PA.Term PA.Formula.

(** The PA-side composite, with an explicit map selecting the PA slots
    occupied by the intermediate HF values. *)
Definition paCompositeAt
    (codedMap : nat -> nat) (phi : PA.formula) : PA.formula :=
  hfFormulaAt codedMap (formulaAt (fun n : nat => n) phi).

Lemma paCompositeAt_id : forall phi,
  paCompositeAt (fun n : nat => n) phi =
    translateHFFormula (translateFormula phi).
Proof. reflexivity. Qed.

(** The semantic PA round trip is unconditional in the standard model.
    This is deliberately kept separate from the deductive theorem: PA's
    syntactic calculus has no (and cannot have) reflection principle for
    arbitrary standard-model truth. *)
Theorem PA_roundTrip_standard_semantic : forall phi,
  PA.Formula.Sentence phi ->
  forall e : nat -> nat,
    PA.Formula.Sat PA.natModel e
      (PA.Formula.iffForm phi
        (translateHFFormula (translateFormula phi))).
Proof.
  intros phi hphi e.
  apply (proj2 (PA.Formula.Sat_iffForm PA.natModel e
    phi (translateHFFormula (translateFormula phi)))).
  split; intro h.
  - apply (proj2 (translateHFFormula_exact (translateFormula phi) e)).
    apply (proj1 (Sat_sentence_inv nat hf_mem (translateFormula phi)
      (translateFormula_sentence_of_PA_sentence phi hphi)
      (fun n => ordinal_code (e n)) e)).
    apply (proj2 (translateFormula_exact phi e)).
    exact h.
  - apply (proj1 (translateFormula_exact phi e)).
    apply (proj2 (Sat_sentence_inv nat hf_mem (translateFormula phi)
      (translateFormula_sentence_of_PA_sentence phi hphi)
      (fun n => ordinal_code (e n)) e)).
    apply (proj1 (translateHFFormula_exact (translateFormula phi) e)).
    exact h.
Qed.

(** Provable equivalence is compositional for the propositional
    constructors.  These lemmas are theory-independent; they are stated in
    the PA calculus only because that is the target calculus of this file. *)
Lemma BProv_PA_iffForm_refl : forall
    (B : PA.formula -> Prop) (G : list PA.formula) a,
  PA.Formula.BProv B G (PA.Formula.iffForm a a).
Proof.
  intros B G a.
  assert (haa : PA.Formula.BProv B G (pImp a a)).
  {
    apply BProv_impI.
    apply BProv_ass.
    simpl. now left.
  }
  unfold iffForm.
  exact (BProv_andI B G (pImp a a) (pImp a a) haa haa).
Qed.

Lemma BProv_PA_iffForm_imp_congr : forall
    (B : PA.formula -> Prop) (G : list PA.formula)
    a a' b b',
  PA.Formula.BProv B G (iffForm a a') ->
  PA.Formula.BProv B G (iffForm b b') ->
  PA.Formula.BProv B G
    (iffForm (pImp a b) (pImp a' b')).
Proof.
  intros B G a a' b b' ha hb.
  assert (haa' : BProv B G (pImp a a')).
  { unfold iffForm in ha. exact (BProv_andE1 B G _ _ ha). }
  assert (ha'a : BProv B G (pImp a' a)).
  { unfold iffForm in ha. exact (BProv_andE2 B G _ _ ha). }
  assert (hbb' : BProv B G (pImp b b')).
  { unfold iffForm in hb. exact (BProv_andE1 B G _ _ hb). }
  assert (hb'b : BProv B G (pImp b' b)).
  { unfold iffForm in hb. exact (BProv_andE2 B G _ _ hb). }
  assert (hforward : BProv B G
      (pImp (pImp a b) (pImp a' b'))).
  {
    apply BProv_impI.
    apply BProv_impI.
    set (C := a' :: pImp a b :: G).
    assert (ha'C : BProv B C a').
    { apply BProv_ass. unfold C. simpl. now left. }
    assert (haC : BProv B C a).
    {
      exact (BProv_mp B C a' a
        (PA.Formula.BProv_context_cons B (pImp a b :: G) a' (pImp a' a)
          (PA.Formula.BProv_context_cons B G (pImp a b) (pImp a' a) ha'a)) ha'C).
    }
    assert (habC : BProv B C (pImp a b)).
    { apply BProv_ass. unfold C. simpl. tauto. }
    assert (hbC : BProv B C b).
    { exact (BProv_mp B C a b habC haC). }
    exact (BProv_mp B C b b'
      (PA.Formula.BProv_context_cons B (pImp a b :: G) a' (pImp b b')
        (PA.Formula.BProv_context_cons B G (pImp a b) (pImp b b') hbb')) hbC).
  }
  assert (hreverse : BProv B G
      (pImp (pImp a' b') (pImp a b))).
  {
    apply BProv_impI.
    apply BProv_impI.
    set (C := a :: pImp a' b' :: G).
    assert (haC : BProv B C a).
    { apply BProv_ass. unfold C. simpl. now left. }
    assert (ha'C : BProv B C a').
    {
      exact (BProv_mp B C a a'
        (PA.Formula.BProv_context_cons B (pImp a' b' :: G) a (pImp a a')
          (PA.Formula.BProv_context_cons B G (pImp a' b') (pImp a a') haa')) haC).
    }
    assert (ha'b'C : BProv B C (pImp a' b')).
    { apply BProv_ass. unfold C. simpl. tauto. }
    assert (hb'C : BProv B C b').
    { exact (BProv_mp B C a' b' ha'b'C ha'C). }
    exact (BProv_mp B C b' b
      (PA.Formula.BProv_context_cons B (pImp a' b' :: G) a (pImp b' b)
        (PA.Formula.BProv_context_cons B G (pImp a' b') (pImp b' b) hb'b)) hb'C).
  }
  unfold iffForm.
  exact (BProv_andI B G _ _ hforward hreverse).
Qed.

Lemma BProv_PA_iffForm_and_congr : forall
    (B : PA.formula -> Prop) (G : list PA.formula)
    a a' b b',
  PA.Formula.BProv B G (iffForm a a') ->
  PA.Formula.BProv B G (iffForm b b') ->
  PA.Formula.BProv B G
    (iffForm (pAnd a b) (pAnd a' b')).
Proof.
  intros B G a a' b b' ha hb.
  assert (haa' : BProv B G (pImp a a')).
  { unfold iffForm in ha. exact (BProv_andE1 B G _ _ ha). }
  assert (ha'a : BProv B G (pImp a' a)).
  { unfold iffForm in ha. exact (BProv_andE2 B G _ _ ha). }
  assert (hbb' : BProv B G (pImp b b')).
  { unfold iffForm in hb. exact (BProv_andE1 B G _ _ hb). }
  assert (hb'b : BProv B G (pImp b' b)).
  { unfold iffForm in hb. exact (BProv_andE2 B G _ _ hb). }
  assert (hforward : BProv B G
      (pImp (pAnd a b) (pAnd a' b'))).
  {
    apply BProv_impI.
    set (C := pAnd a b :: G).
    assert (hp : BProv B C (pAnd a b)).
    { apply BProv_ass. unfold C. simpl. now left. }
    assert (haC : BProv B C a).
    { exact (BProv_andE1 B C a b hp). }
    assert (hbC : BProv B C b).
    { exact (BProv_andE2 B C a b hp). }
    assert (ha'C : BProv B C a').
    { exact (BProv_mp B C a a'
        (PA.Formula.BProv_context_cons B G (pAnd a b) (pImp a a') haa') haC). }
    assert (hb'C : BProv B C b').
    { exact (BProv_mp B C b b'
        (PA.Formula.BProv_context_cons B G (pAnd a b) (pImp b b') hbb') hbC). }
    exact (BProv_andI B C a' b' ha'C hb'C).
  }
  assert (hreverse : BProv B G
      (pImp (pAnd a' b') (pAnd a b))).
  {
    apply BProv_impI.
    set (C := pAnd a' b' :: G).
    assert (hp : BProv B C (pAnd a' b')).
    { apply BProv_ass. unfold C. simpl. now left. }
    assert (ha'C : BProv B C a').
    { exact (BProv_andE1 B C a' b' hp). }
    assert (hb'C : BProv B C b').
    { exact (BProv_andE2 B C a' b' hp). }
    assert (haC : BProv B C a).
    { exact (BProv_mp B C a' a
        (PA.Formula.BProv_context_cons B G (pAnd a' b') (pImp a' a) ha'a) ha'C). }
    assert (hbC : BProv B C b).
    { exact (BProv_mp B C b' b
        (PA.Formula.BProv_context_cons B G (pAnd a' b') (pImp b' b) hb'b) hb'C). }
    exact (BProv_andI B C a b haC hbC).
  }
  unfold iffForm.
  exact (BProv_andI B G _ _ hforward hreverse).
Qed.

Lemma BProv_PA_iffForm_or_congr : forall
    (B : PA.formula -> Prop) (G : list PA.formula)
    a a' b b',
  PA.Formula.BProv B G (iffForm a a') ->
  PA.Formula.BProv B G (iffForm b b') ->
  PA.Formula.BProv B G
    (iffForm (pOr a b) (pOr a' b')).
Proof.
  intros B G a a' b b' ha hb.
  assert (haa' : BProv B G (pImp a a')).
  { unfold iffForm in ha. exact (BProv_andE1 B G _ _ ha). }
  assert (ha'a : BProv B G (pImp a' a)).
  { unfold iffForm in ha. exact (BProv_andE2 B G _ _ ha). }
  assert (hbb' : BProv B G (pImp b b')).
  { unfold iffForm in hb. exact (BProv_andE1 B G _ _ hb). }
  assert (hb'b : BProv B G (pImp b' b)).
  { unfold iffForm in hb. exact (BProv_andE2 B G _ _ hb). }
  assert (hforward : BProv B G
      (pImp (pOr a b) (pOr a' b'))).
  {
    apply BProv_impI.
    set (C := pOr a b :: G).
    assert (hor : BProv B C (pOr a b)).
    { apply BProv_ass. unfold C. simpl. now left. }
    assert (hleft : BProv B (a :: C) (pOr a' b')).
    {
      apply BProv_orI1.
      assert (haC : BProv B (a :: C) a).
      { apply BProv_ass. simpl. now left. }
      exact (BProv_mp B (a :: C) a a'
        (PA.Formula.BProv_context_cons B (pOr a b :: G) a (pImp a a')
          (PA.Formula.BProv_context_cons B G (pOr a b) (pImp a a') haa'))
        haC).
    }
    assert (hright : BProv B (b :: C) (pOr a' b')).
    {
      apply BProv_orI2.
      assert (hbC : BProv B (b :: C) b).
      { apply BProv_ass. simpl. now left. }
      exact (BProv_mp B (b :: C) b b'
        (PA.Formula.BProv_context_cons B (pOr a b :: G) b (pImp b b')
          (PA.Formula.BProv_context_cons B G (pOr a b) (pImp b b') hbb'))
        hbC).
    }
    exact (BProv_orE B C a b (pOr a' b') hor hleft hright).
  }
  assert (hreverse : BProv B G
      (pImp (pOr a' b') (pOr a b))).
  {
    apply BProv_impI.
    set (C := pOr a' b' :: G).
    assert (hor : BProv B C (pOr a' b')).
    { apply BProv_ass. unfold C. simpl. now left. }
    assert (hleft : BProv B (a' :: C) (pOr a b)).
    {
      apply BProv_orI1.
      assert (haC : BProv B (a' :: C) a').
      { apply BProv_ass. simpl. now left. }
      exact (BProv_mp B (a' :: C) a' a
        (PA.Formula.BProv_context_cons B (pOr a' b' :: G) a' (pImp a' a)
          (PA.Formula.BProv_context_cons B G (pOr a' b') (pImp a' a) ha'a))
        haC).
    }
    assert (hright : BProv B (b' :: C) (pOr a b)).
    {
      apply BProv_orI2.
      assert (hbC : BProv B (b' :: C) b').
      { apply BProv_ass. simpl. now left. }
      exact (BProv_mp B (b' :: C) b' b
        (PA.Formula.BProv_context_cons B (pOr a' b' :: G) b' (pImp b' b)
          (PA.Formula.BProv_context_cons B G (pOr a' b') (pImp b' b) hb'b))
        hbC).
    }
    exact (BProv_orE B C a' b' (pOr a b) hor hleft hright).
  }
  unfold iffForm.
  exact (BProv_andI B G _ _ hforward hreverse).
Qed.

(** The paired raw/code invariant used by the formula induction. *)
Definition PACompositeFormulaExact (phi : PA.formula) : Prop :=
  forall (G : list PA.formula) (rawMap codedMap : nat -> nat),
    (forall n, PA.Formula.Free n phi ->
      PA.Formula.BProv PA.Formula.Ax_s G
        (ordinalCodeGraphAt (rawMap n) (codedMap n))) ->
    PA.Formula.BProv PA.Formula.Ax_s G
      (PA.Formula.iffForm
        (PA.Formula.rename rawMap phi)
        (paCompositeAt codedMap phi)).

(** Constructor-local residual package.  Equality contains the actual term
    graph arithmetic.  The quantified fields contain precisely the domain
    totality/range bookkeeping needed when a fresh raw or coded witness is
    opened.  Propositional composition is discharged below. *)
Record PACompositeConstructorProofs : Prop := {
  pa_composite_eq_exact : forall left right,
    PACompositeFormulaExact (pEq left right);
  pa_composite_all_exact : forall phi,
    PACompositeFormulaExact phi ->
    PACompositeFormulaExact (pAll phi);
  pa_composite_ex_exact : forall phi,
    PACompositeFormulaExact phi ->
    PACompositeFormulaExact (pEx phi)
}.

Theorem PACompositeFormulaExact_of_constructorProofs :
  forall (P : PACompositeConstructorProofs) phi,
    PACompositeFormulaExact phi.
Proof.
  intros P phi.
  induction phi as [left right | | a IHa b IHb | a IHa b IHb |
      a IHa b IHb | a IHa | a IHa].
  - exact (pa_composite_eq_exact P left right).
  - intros G rawMap codedMap hcode.
    change (BProv Ax_s G (iffForm pBot pBot)).
    apply BProv_PA_iffForm_refl.
  - intros G rawMap codedMap hcode.
    change (BProv Ax_s G
      (iffForm
        (pImp (rename rawMap a) (rename rawMap b))
        (pImp (paCompositeAt codedMap a)
          (paCompositeAt codedMap b)))).
    apply BProv_PA_iffForm_imp_congr.
    + apply IHa. intros n hn. apply hcode. now left.
    + apply IHb. intros n hn. apply hcode. now right.
  - intros G rawMap codedMap hcode.
    change (BProv Ax_s G
      (iffForm
        (pAnd (rename rawMap a) (rename rawMap b))
        (pAnd (paCompositeAt codedMap a)
          (paCompositeAt codedMap b)))).
    apply BProv_PA_iffForm_and_congr.
    + apply IHa. intros n hn. apply hcode. now left.
    + apply IHb. intros n hn. apply hcode. now right.
  - intros G rawMap codedMap hcode.
    change (BProv Ax_s G
      (iffForm
        (pOr (rename rawMap a) (rename rawMap b))
        (pOr (paCompositeAt codedMap a)
          (paCompositeAt codedMap b)))).
    apply BProv_PA_iffForm_or_congr.
    + apply IHa. intros n hn. apply hcode. now left.
    + apply IHb. intros n hn. apply hcode. now right.
  - exact (pa_composite_all_exact P a IHa).
  - exact (pa_composite_ex_exact P a IHa).
Qed.

(** Constructor-local proofs suffice for the published PA deductive
    round-trip proposition. *)
Theorem PARoundTripProof_of_constructorProofs :
  PACompositeConstructorProofs -> PARoundTripProof.
Proof.
  intros P phi hphi.
  pose proof (PACompositeFormulaExact_of_constructorProofs P phi
    [] (fun n : nat => n) (fun n : nat => n)) as h.
  specialize (h (fun n hn => False_rect _ (hphi n hn))).
  rewrite PA.Formula.rename_id in h.
  rewrite paCompositeAt_id in h.
  exact h.
Qed.

(** The existing internal induction already supplies graph totality once
    Ackermann adjunction is available.  This endpoint records that totality
    is not one of the new constructor-level logical residuals. *)
Definition PAOrdinalCodeGraphTotalProof : Prop :=
  forall (G : list PA.formula) (raw : PA.term),
    PA.Formula.BProv PA.Formula.Ax_s G
      (pEx (ordinalCodeGraphTermAt
        (PA.Term.rename S raw) (tVar 0))).

Theorem PAOrdinalCodeGraphTotalProof_of_adjoinExistence :
  PAHFAdjoinExistence -> PAOrdinalCodeGraphTotalProof.
Proof.
  intros hadjoin G raw.
  exact (OrdinalCodeGraphProofs_total_of_adjoinExistence
    hadjoin G raw).
Qed.
