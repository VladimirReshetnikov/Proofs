(**
  Structural computability for the restricted-PA certificate checker.

  The decoder-heavy certificates are imported from
  [CodedCheckerComputability].  This second cache layer handles the much
  smaller syntax operations, structural equality tests, occurrence-rank
  calculation, and final Boolean conjunction used by the public checker.
*)

From Stdlib Require Import Arith Bool List Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From BoundedPAConsistency Require Import
  BoundedConsistency CodedSyntax CodedProof CodedCheckerComputability.

From Undecidability.L.Datatypes Require Import LBool LNat LProd LOptions.
From Undecidability.L.Datatypes.List Require Import List_basics.
From Undecidability.L.Tactics Require Import Computable.

Set Implicit Arguments.

Module PABoundedCodedCheckerStructuralComputability.

Import PA.
Import PABoundedConsistency.
Import PABoundedCodedSyntax.
Import PABoundedCodedProof.
Import PABoundedCodedDecoderComputability.

(** The proof endpoint computations use substitution and renaming. *)
#[export] Instance term_up : computable up.
Proof. extract. Qed.
#[export] Instance term_termRename : computable Term.rename.
Proof. extract. Qed.
#[export] Instance term_upSubst : computable Term.upSubst.
Proof. extract. Qed.
#[export] Instance term_termSubst : computable Term.subst.
Proof. extract. Qed.
#[export] Instance term_formulaRename : computable Formula.rename.
Proof.
  extract. Unshelve.
  - exact (enc (pAll (Formula.rename (up x0) f))).
  - exact (enc (pEx (Formula.rename (up x0) f))).
  - remember
      (@extApp' (nat -> nat) (nat -> nat)
        (!nat ~> !nat) (!nat ~> !nat) up x0 term_up
        (@Build_computable (nat -> nat) (!nat ~> !nat)
          x0 x0Int x0Ints)) as hcup.
    destruct hcup as [upInt upInts].
    destruct (IHP (up x0) upInt upInts f Logic.I Logic.I)
      as [v [hv hcomputes]].
    change (v = enc (Formula.rename (up x0) f)) in hcomputes.
    subst v. unfold L_facts.eval in *. destruct hv as [hv hlambda].
    split.
    + transitivity
        (L.app (ext pAll) (enc (Formula.rename (up x0) f))).
      * exact (L_facts.star_trans_r (ext pAll) hv).
      * Lsimpl. Lreflexivity.
    + Lproc.
  - remember
      (@extApp' (nat -> nat) (nat -> nat)
        (!nat ~> !nat) (!nat ~> !nat) up x0 term_up
        (@Build_computable (nat -> nat) (!nat ~> !nat)
          x0 x0Int x0Ints)) as hcup.
    destruct hcup as [upInt upInts].
    destruct (IHP (up x0) upInt upInts f Logic.I Logic.I)
      as [v [hv hcomputes]].
    change (v = enc (Formula.rename (up x0) f)) in hcomputes.
    subst v. unfold L_facts.eval in *. destruct hv as [hv hlambda].
    split.
    + transitivity
        (L.app (ext pEx) (enc (Formula.rename (up x0) f))).
      * exact (L_facts.star_trans_r (ext pEx) hv).
      * Lsimpl. Lreflexivity.
    + Lproc.
  - apply computesTyB.
  - apply computesTyB.
Qed.
#[export] Instance term_formulaSubst : computable Formula.subst.
Proof.
  extract. Unshelve.
  - exact (enc (pAll (Formula.subst (Term.upSubst x0) f))).
  - exact (enc (pEx (Formula.subst (Term.upSubst x0) f))).
  - remember
      (@extApp' (nat -> term) (nat -> term)
        (!nat ~> !term) (!nat ~> !term)
        Term.upSubst x0 term_upSubst
        (@Build_computable (nat -> term) (!nat ~> !term)
          x0 x0Int x0Ints)) as hcup.
    destruct hcup as [upInt upInts].
    destruct (IHP (Term.upSubst x0) upInt upInts f Logic.I Logic.I)
      as [v [hv hcomputes]].
    change (v = enc (Formula.subst (Term.upSubst x0) f)) in hcomputes.
    subst v. unfold L_facts.eval in *. destruct hv as [hv hlambda].
    split.
    + transitivity
        (L.app (ext pAll) (enc (Formula.subst (Term.upSubst x0) f))).
      * exact (L_facts.star_trans_r (ext pAll) hv).
      * Lsimpl. Lreflexivity.
    + Lproc.
  - remember
      (@extApp' (nat -> term) (nat -> term)
        (!nat ~> !term) (!nat ~> !term)
        Term.upSubst x0 term_upSubst
        (@Build_computable (nat -> term) (!nat ~> !term)
          x0 x0Int x0Ints)) as hcup.
    destruct hcup as [upInt upInts].
    destruct (IHP (Term.upSubst x0) upInt upInts f Logic.I Logic.I)
      as [v [hv hcomputes]].
    change (v = enc (Formula.subst (Term.upSubst x0) f)) in hcomputes.
    subst v. unfold L_facts.eval in *. destruct hv as [hv hlambda].
    split.
    + transitivity
        (L.app (ext pEx) (enc (Formula.subst (Term.upSubst x0) f))).
      * exact (L_facts.star_trans_r (ext pEx) hv).
      * Lsimpl. Lreflexivity.
    + Lproc.
  - apply computesTyB.
  - apply computesTyB.
Qed.
#[export] Instance term_instTerm : computable Formula.instTerm.
Proof. extract. Qed.

(** PA axiom witnesses include an arbitrary induction instance. *)
#[export] Instance term_termBound : computable Term.bound.
Proof. extract. Qed.
#[export] Instance term_formulaBound : computable Formula.bound.
Proof. extract. Qed.
#[export] Instance term_closeN : computable Formula.closeN.
Proof. extract. Qed.
#[export] Instance term_sealPA : computable Formula.sealPA.
Proof. extract. Qed.
#[export] Instance term_substZero : computable Formula.substZero.
Proof. extract. Qed.
#[export] Instance term_substSuccVar : computable Formula.substSuccVar.
Proof. extract. Qed.
#[export] Instance term_inductionForm : computable Formula.inductionForm.
Proof. extract. Qed.
#[export] Instance term_witnessedAxiom : computable witnessedAxiom.
Proof. extract. Qed.

(** Boolean structural equality is extensionally equal to the original
    transparent decidable-equality wrappers, but avoids extracting proof
    objects of [sumbool]. *)
Fixpoint termEqbC (a b : term) : bool :=
  match a, b with
  | tVar x, tVar y => Nat.eqb x y
  | tZero, tZero => true
  | tSucc x, tSucc y => termEqbC x y
  | tAdd a1 a2, tAdd b1 b2
  | tMul a1 a2, tMul b1 b2 => termEqbC a1 b1 && termEqbC a2 b2
  | _, _ => false
  end.

Fixpoint formulaEqbC (a b : formula) : bool :=
  match a, b with
  | pEq a1 a2, pEq b1 b2 => termEqbC a1 b1 && termEqbC a2 b2
  | pBot, pBot => true
  | pImp a1 a2, pImp b1 b2
  | pAnd a1 a2, pAnd b1 b2
  | pOr a1 a2, pOr b1 b2 => formulaEqbC a1 b1 && formulaEqbC a2 b2
  | pAll x, pAll y
  | pEx x, pEx y => formulaEqbC x y
  | _, _ => false
  end.

Fixpoint contextEqbC (G H : list formula) : bool :=
  match G, H with
  | [], [] => true
  | a :: G', b :: H' => formulaEqbC a b && contextEqbC G' H'
  | _, _ => false
  end.

Fixpoint formulaInbC (a : formula) (G : list formula) : bool :=
  match G with
  | [] => false
  | b :: G' => formulaEqbC a b || formulaInbC a G'
  end.

Lemma termEqbC_spec : forall a b, termEqbC a b = true <-> a = b.
Proof.
  induction a; destruct b; cbn; try (split; congruence).
  - rewrite Nat.eqb_eq. split; intro h; [now subst | now inversion h].
  - rewrite IHa. split; intro h; [now subst | now inversion h].
  - rewrite andb_true_iff, IHa1, IHa2.
    split.
    + intros [h1 h2]. now subst.
    + intro h. inversion h. subst. split; reflexivity.
  - rewrite andb_true_iff, IHa1, IHa2.
    split.
    + intros [h1 h2]. now subst.
    + intro h. inversion h. subst. split; reflexivity.
Qed.

Lemma formulaEqbC_spec : forall a b,
  formulaEqbC a b = true <-> a = b.
Proof.
  induction a; destruct b; cbn; try (split; congruence).
  - rewrite andb_true_iff, !termEqbC_spec.
    split.
    + intros [h1 h2]. now subst.
    + intro h. inversion h. subst. split; reflexivity.
  - rewrite andb_true_iff, IHa1, IHa2.
    split.
    + intros [h1 h2]. now subst.
    + intro h. inversion h. subst. split; reflexivity.
  - rewrite andb_true_iff, IHa1, IHa2.
    split.
    + intros [h1 h2]. now subst.
    + intro h. inversion h. subst. split; reflexivity.
  - rewrite andb_true_iff, IHa1, IHa2.
    split.
    + intros [h1 h2]. now subst.
    + intro h. inversion h. subst. split; reflexivity.
  - rewrite IHa. split; intro h; [now subst | now inversion h].
  - rewrite IHa. split; intro h; [now subst | now inversion h].
Qed.

Lemma contextEqbC_spec : forall G H,
  contextEqbC G H = true <-> G = H.
Proof.
  induction G as [|a G IH]; destruct H as [|b H]; cbn;
    try (split; congruence).
  rewrite andb_true_iff, formulaEqbC_spec, IH.
  split.
  - intros [h1 h2]. now subst.
  - intro h. inversion h. subst. split; reflexivity.
Qed.

Lemma formulaInbC_spec : forall a G,
  formulaInbC a G = true <-> In a G.
Proof.
  intros a G. induction G as [|b G IH]; cbn.
  - split; intro h; [discriminate | contradiction].
  - rewrite orb_true_iff, formulaEqbC_spec, IH.
    split; intros [h | h].
    + left. symmetry. exact h.
    + right. exact h.
    + left. symmetry. exact h.
    + right. exact h.
Qed.

#[export] Instance term_termEqbC : computable termEqbC.
Proof. extract. Qed.
#[export] Instance term_formulaEqbC : computable formulaEqbC.
Proof. extract. Qed.
#[export] Instance term_contextEqbC : computable contextEqbC.
Proof. extract. Qed.
#[export] Instance term_formulaInbC : computable formulaInbC.
Proof. extract. Qed.

#[export] Instance term_formulaEqb : computable formulaEqb.
Proof.
  apply computableExt with (x := formulaEqbC).
  intros a b. apply Bool.eq_true_iff_eq.
  rewrite formulaEqbC_spec, formulaEqb_spec. reflexivity.
  typeclasses eauto.
Qed.

#[export] Instance term_contextEqb : computable contextEqb.
Proof.
  apply computableExt with (x := contextEqbC).
  intros G H. apply Bool.eq_true_iff_eq.
  rewrite contextEqbC_spec, contextEqb_spec. reflexivity.
  typeclasses eauto.
Qed.

#[export] Instance term_formulaInb : computable formulaInb.
Proof.
  apply computableExt with (x := formulaInbC).
  intros a G. apply Bool.eq_true_iff_eq.
  rewrite formulaInbC_spec, formulaInb_spec. reflexivity.
  typeclasses eauto.
Qed.

(** Rule validation and endpoint computation. *)
#[export] Instance term_rawContext : computable rawContext.
Proof. extract. Qed.
#[export] Instance term_rawConclusion : computable rawConclusion.
Proof. extract. Qed.
#[export] Instance term_rawProofValidb : computable rawProofValidb.
Proof. extract. Qed.

(** This cache boundary ends immediately before the occurrence-rank
    recursion, so later rank/formula iterations do not re-extract rule
    validation or the substitution machinery. *)
End PABoundedCodedCheckerStructuralComputability.
