(**
  Standard-quotation adequacy for transparent coded formula operations.

  Formula renaming and single substitution are represented by occurrence
  traversals because the same syntactic subformula may occur under different
  binder depths.  This file first identifies the metatheoretic operation
  performed at each depth, then realizes a finite postorder occurrence table.
  The resulting theorem is deliberately restricted to ordinary quotations;
  the raw operation relation itself remains meaningful on nonstandard codes.
*)

From Stdlib Require Import List Arith Lia Logic.FunctionalExtensionality.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax RawCodedSyntaxConstructors RawCodedAssignment
  RawCodedFormulaRankStep RawCodedFormulaOperations
  RawCodedTermOperationsStandardAdequacy.

Import ListNotations.

Module PABoundedRawCodedFormulaOperationsStandardAdequacy.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFormulaRankStep.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedTermOperationsStandardAdequacy.

(** The renaming function induced by a cutoff/amount pair. *)
Definition standardShiftRenaming
    (cutoff amount index : nat) : nat :=
  if index <? cutoff then index else index + amount.

Lemma standardTermShift_as_rename : forall cutoff amount t,
  standardTermShift cutoff amount t =
  Term.rename (standardShiftRenaming cutoff amount) t.
Proof.
  intros cutoff amount t.
  induction t as [index | | child IH | lhs IHl rhs IHr |
      lhs IHl rhs IHr]; cbn [standardTermShift Term.rename].
  - unfold standardShiftRenaming.
    destruct (index <? cutoff); reflexivity.
  - reflexivity.
  - now rewrite IH.
  - now rewrite IHl, IHr.
  - now rewrite IHl, IHr.
Qed.

Lemma up_standardShiftRenaming : forall cutoff amount index,
  up (standardShiftRenaming cutoff amount) index =
  standardShiftRenaming (S cutoff) amount index.
Proof.
  intros cutoff amount [|index]; [reflexivity |].
  unfold up, standardShiftRenaming.
  destruct (index <? cutoff) eqn:hindex;
    destruct (S index <? S cutoff) eqn:hsucc.
  - reflexivity.
  - apply Nat.ltb_lt in hindex. apply Nat.ltb_ge in hsucc. lia.
  - apply Nat.ltb_ge in hindex. apply Nat.ltb_lt in hsucc. lia.
  - f_equal. lia.
Qed.

(** Formula shifting threads the cutoff through binders. *)
Fixpoint standardFormulaShift
    (cutoff amount : nat) (phi : formula) : formula :=
  match phi with
  | pEq lhs rhs =>
      pEq (standardTermShift cutoff amount lhs)
        (standardTermShift cutoff amount rhs)
  | pBot => pBot
  | pImp lhs rhs =>
      pImp (standardFormulaShift cutoff amount lhs)
        (standardFormulaShift cutoff amount rhs)
  | pAnd lhs rhs =>
      pAnd (standardFormulaShift cutoff amount lhs)
        (standardFormulaShift cutoff amount rhs)
  | pOr lhs rhs =>
      pOr (standardFormulaShift cutoff amount lhs)
        (standardFormulaShift cutoff amount rhs)
  | pAll child => pAll (standardFormulaShift (S cutoff) amount child)
  | pEx child => pEx (standardFormulaShift (S cutoff) amount child)
  end.

Lemma standardFormulaShift_as_rename : forall cutoff amount phi,
  standardFormulaShift cutoff amount phi =
  Formula.rename (standardShiftRenaming cutoff amount) phi.
Proof.
  intros cutoff amount phi. revert cutoff.
  induction phi as [lhs rhs | | lhs IHl rhs IHr | lhs IHl rhs IHr |
      lhs IHl rhs IHr | child IH | child IH]; intro cutoff;
    cbn [standardFormulaShift Formula.rename].
  - now rewrite !standardTermShift_as_rename.
  - reflexivity.
  - now rewrite IHl, IHr.
  - now rewrite IHl, IHr.
  - now rewrite IHl, IHr.
  - rewrite IH. f_equal.
    apply Formula.rename_ext. intro index.
    symmetry. apply up_standardShiftRenaming.
  - rewrite IH. f_equal.
    apply Formula.rename_ext. intro index.
    symmetry. apply up_standardShiftRenaming.
Qed.

Corollary standardFormulaShift_zero_one : forall phi,
  standardFormulaShift 0 1 phi = Formula.rename S phi.
Proof.
  intro phi. rewrite standardFormulaShift_as_rename.
  apply Formula.rename_ext. intro index.
  unfold standardShiftRenaming. cbn. lia.
Qed.

(** The capture-avoiding single substitution visible at one binder depth. *)
Definition standardSingleSubstitutionAt
    (replacement : term) (depth index : nat) : term :=
  if index <? depth then tVar index
  else if index =? depth then standardTermShift 0 depth replacement
  else tVar (Nat.pred index).

Lemma standardTermShift_zero_zero : forall t,
  standardTermShift 0 0 t = t.
Proof.
  induction t as [index | | child IH | lhs IHl rhs IHr |
      lhs IHl rhs IHr]; cbn [standardTermShift].
  - now rewrite Nat.add_0_r.
  - reflexivity.
  - now rewrite IH.
  - now rewrite IHl, IHr.
  - now rewrite IHl, IHr.
Qed.

Lemma standardTermShift_succ_amount : forall amount t,
  Term.rename S (standardTermShift 0 amount t) =
  standardTermShift 0 (S amount) t.
Proof.
  intros amount t.
  rewrite !standardTermShift_as_rename.
  induction t as [index | | child IH | lhs IHl rhs IHr |
      lhs IHl rhs IHr]; cbn [Term.rename].
  - unfold standardShiftRenaming. cbn. f_equal. lia.
  - reflexivity.
  - now rewrite IH.
  - now rewrite IHl, IHr.
  - now rewrite IHl, IHr.
Qed.

Lemma up_standardSingleSubstitutionAt : forall replacement depth,
  Term.upSubst (standardSingleSubstitutionAt replacement depth) =
  standardSingleSubstitutionAt replacement (S depth).
Proof.
  intros replacement depth.
  apply functional_extensionality. intros [|index].
  - reflexivity.
  - unfold Term.upSubst, standardSingleSubstitutionAt.
    destruct (index <? depth) eqn:hlow;
      destruct (S index <? S depth) eqn:hsucc.
    + reflexivity.
    + apply Nat.ltb_lt in hlow. apply Nat.ltb_ge in hsucc. lia.
    + apply Nat.ltb_ge in hlow. apply Nat.ltb_lt in hsucc. lia.
    + destruct (Nat.eq_dec index depth) as [-> | hneq].
      * rewrite !Nat.eqb_refl. apply standardTermShift_succ_amount.
      * assert (heq : (index =? depth) = false)
          by (apply Nat.eqb_neq; exact hneq).
        assert (heqSucc : (S index =? S depth) = false)
          by (apply Nat.eqb_neq; lia).
        rewrite heq, heqSucc.
        assert (hpositive : 0 < index) by
          (apply Nat.ltb_ge in hlow; lia).
        rewrite <- (Nat.succ_pred_pos index hpositive).
        reflexivity.
Qed.

Lemma standardSingleSubstitutionAt_zero : forall replacement,
  standardSingleSubstitutionAt replacement 0 =
  Formula.instTerm replacement.
Proof.
  intro replacement. apply functional_extensionality. intros [|index].
  - unfold standardSingleSubstitutionAt, Formula.instTerm. cbn.
    apply standardTermShift_zero_zero.
  - unfold standardSingleSubstitutionAt, Formula.instTerm. cbn.
    reflexivity.
Qed.

Lemma standardTermOpening_as_subst : forall depth replacement t,
  standardTermOpening depth (standardTermShift 0 depth replacement) t =
  Term.subst (standardSingleSubstitutionAt replacement depth) t.
Proof.
  intros depth replacement t.
  induction t as [index | | child IH | lhs IHl rhs IHr |
      lhs IHl rhs IHr]; cbn [standardTermOpening Term.subst].
  - unfold standardSingleSubstitutionAt. reflexivity.
  - reflexivity.
  - now rewrite IH.
  - now rewrite IHl, IHr.
  - now rewrite IHl, IHr.
Qed.

Fixpoint standardFormulaSingleSubstitution
    (replacement : term) (depth : nat) (phi : formula) : formula :=
  match phi with
  | pEq lhs rhs =>
      pEq
        (standardTermOpening depth
          (standardTermShift 0 depth replacement) lhs)
        (standardTermOpening depth
          (standardTermShift 0 depth replacement) rhs)
  | pBot => pBot
  | pImp lhs rhs =>
      pImp (standardFormulaSingleSubstitution replacement depth lhs)
        (standardFormulaSingleSubstitution replacement depth rhs)
  | pAnd lhs rhs =>
      pAnd (standardFormulaSingleSubstitution replacement depth lhs)
        (standardFormulaSingleSubstitution replacement depth rhs)
  | pOr lhs rhs =>
      pOr (standardFormulaSingleSubstitution replacement depth lhs)
        (standardFormulaSingleSubstitution replacement depth rhs)
  | pAll child =>
      pAll (standardFormulaSingleSubstitution replacement (S depth) child)
  | pEx child =>
      pEx (standardFormulaSingleSubstitution replacement (S depth) child)
  end.

Lemma standardFormulaSingleSubstitution_as_subst :
  forall replacement depth phi,
  standardFormulaSingleSubstitution replacement depth phi =
  Formula.subst (standardSingleSubstitutionAt replacement depth) phi.
Proof.
  intros replacement depth phi. revert depth.
  induction phi as [lhs rhs | | lhs IHl rhs IHr | lhs IHl rhs IHr |
      lhs IHl rhs IHr | child IH | child IH]; intro depth;
    cbn [standardFormulaSingleSubstitution Formula.subst].
  - now rewrite !standardTermOpening_as_subst.
  - reflexivity.
  - now rewrite IHl, IHr.
  - now rewrite IHl, IHr.
  - now rewrite IHl, IHr.
  - rewrite IH, up_standardSingleSubstitutionAt. reflexivity.
  - rewrite IH, up_standardSingleSubstitutionAt. reflexivity.
Qed.

Corollary standardFormulaSingleSubstitution_zero :
  forall replacement phi,
  standardFormulaSingleSubstitution replacement 0 phi =
  Formula.subst (Formula.instTerm replacement) phi.
Proof.
  intros replacement phi.
  rewrite standardFormulaSingleSubstitution_as_subst,
    standardSingleSubstitutionAt_zero. reflexivity.
Qed.

(** The two atomic obligations used by the later occurrence traversal. *)
Lemma raw_standardFormulaShift_atom : forall
    (M : RawPAModel), RawPASatisfies M -> forall amount depth t,
  RawCodedFormulaShiftAtom M
    (rawNumeralValue M amount) (rawNumeralValue M depth)
    (rawQuotedTermCode M t)
    (rawQuotedTermCode M (standardTermShift depth amount t)).
Proof.
  intros M hPA amount depth t.
  apply raw_codedTermShift_standard. exact hPA.
Qed.

Lemma raw_standardFormulaSubstitution_atom : forall
    (M : RawPAModel), RawPASatisfies M -> forall replacement depth t,
  RawCodedFormulaSubstitutionAtom M
    (rawQuotedTermCode M replacement) (rawNumeralValue M depth)
    (rawQuotedTermCode M t)
    (rawQuotedTermCode M
      (standardTermOpening depth
        (standardTermShift 0 depth replacement) t)).
Proof.
  intros M hPA replacement depth t.
  exists (rawQuotedTermCode M (standardTermShift 0 depth replacement)).
  split.
  - apply raw_codedTermShift_standard. exact hPA.
  - apply raw_codedTermOpening_standard. exact hPA.
Qed.

End PABoundedRawCodedFormulaOperationsStandardAdequacy.
