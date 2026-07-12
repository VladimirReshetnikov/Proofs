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
From FirstOrder Require Import Fol Calculus.
From PAHF Require Import PAHF PAHFOrdinalCode
  PAHFProofCalculus PAHFOrdinalCodeTotalInduction PAHFDeductiveAssembly.

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
