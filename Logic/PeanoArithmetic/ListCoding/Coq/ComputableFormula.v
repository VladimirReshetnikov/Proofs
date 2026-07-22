(* ===================================================================== *)
(*  ComputableFormula.v                                                  *)
(*                                                                       *)
(*  From extracted total functions to formulas of PA.  The constructive  *)
(*  part of the file has the following shape:                            *)
(*                                                                       *)
(*    extraction [computable f]                                          *)
(*      -> [L_computable_closed] for the graph of f                      *)
(*      -> [Diophantine'] through the checked model-equivalence cycle    *)
(*      -> existence of a PA graph formula.                              *)
(*                                                                       *)
(*  The final [chosenGraphFormula] definition uses classical epsilon to   *)
(*  select an actual formula from that Prop-level existence.  This is the *)
(*  only choice step in this file; the preceding existence theorems do    *)
(*  not eliminate a proposition into [Type].                             *)
(* ===================================================================== *)

From Stdlib Require Import Arith List Vector Program.Equality.
From Stdlib Require Import Logic.ClassicalEpsilon.

From PAHF Require Import PAHF.
From PAListCoding Require Import DiophantineFormula.

From Undecidability Require Import L.L.
From Undecidability.L.Tactics Require Import Computable.
From Undecidability.L.Datatypes Require Import LNat.
From Undecidability.L.Util Require Import ClosedLAdmissible.
From Undecidability.Synthetic Require Import Models_Equivalent.
From Undecidability.H10.Util Require Import Diophantine.

Set Implicit Arguments.

(* The model-equivalence theorem is stated as a cycle of individual
   simulations.  Starting at closed L, the path used here is

     closed L -> MMA -> TM -> BSM -> MM -> FRACTRAN -> Diophantine'. *)
Theorem L_computable_closed_to_Diophantine' {k}
    (R : Vector.t nat k -> nat -> Prop) :
  L_computable_closed R -> Diophantine' R.
Proof.
  pose proof (equivalence R) as
    [Htm_bsm [Hbsm_mm [Hmm_fractran [Hfractran_dio [Hdio_murec
    [Hmurec_mm [Hmm_mma [Hmma_l [Hl_mma Hmma_tm]]]]]]]]].
  intro HL.
  exact (proj1 (Hfractran_dio
    (Hmm_fractran (Hbsm_mm (Htm_bsm (Hmma_tm (Hl_mma HL))))))).
Qed.

Definition unaryGraph (f : nat -> nat)
    (v : Vector.t nat 1) (y : nat) : Prop :=
  y = f (Vector.nth v Fin.F1).

Definition binaryGraph (f : nat -> nat -> nat)
    (v : Vector.t nat 2) (z : nat) : Prop :=
  z = f (Vector.nth v Fin.F1) (Vector.nth v (Fin.FS Fin.F1)).

Lemma nat_enc_lambda (n : nat) : L_facts.lambda (L.nat_enc n).
Proof. destruct n; eexists; reflexivity. Qed.

(* [computes] uses the reflexive-transitive closure of weak call-by-value
   reduction, whereas [L_computable] uses the inductive big-step [L.eval].
   [L_facts.eval_iff] is the checked bridge between those presentations. *)
Lemma extracted_unary_eval (f : nat -> nat) (Hf : computable f) (x : nat) :
  L.eval
    (L.app (@ext _ (!nat ~> !nat) f Hf) (L.nat_enc x))
    (L.nat_enc (f x)).
Proof.
  pose proof (@extCorrect _ (!nat ~> !nat) f Hf) as Hcorrect.
  cbn in Hcorrect.
  destruct Hcorrect as [_ Hcorrect].
  specialize (Hcorrect x (L.nat_enc x) eq_refl).
  destruct Hcorrect as [v [Hred Hv]].
  cbn in Hv. subst v.
  apply L_facts.eval_iff.
  split; [exact Hred | apply nat_enc_lambda].
Qed.

Lemma extracted_binary_eval
    (f : nat -> nat -> nat) (Hf : computable f) (x y : nat) :
  L.eval
    (L.app
      (L.app (@ext _ (!nat ~> !nat ~> !nat) f Hf) (L.nat_enc x))
      (L.nat_enc y))
    (L.nat_enc (f x y)).
Proof.
  pose proof (@extCorrect _ (!nat ~> !nat ~> !nat) f Hf) as Hcorrect.
  cbn in Hcorrect.
  destruct Hcorrect as [_ Hcorrect].
  specialize (Hcorrect x (L.nat_enc x) eq_refl).
  destruct Hcorrect as [vx [Hredx Hcorrectx]].
  cbn in Hcorrectx.
  destruct Hcorrectx as [_ Hcorrectx].
  specialize (Hcorrectx y (L.nat_enc y) eq_refl).
  destruct Hcorrectx as [vy [Hredy Hvy]].
  cbn in Hvy. subst vy.
  apply L_facts.eval_iff.
  split.
  - etransitivity.
    + apply L_facts.star_trans_l. exact Hredx.
    + exact Hredy.
  - apply nat_enc_lambda.
Qed.

(* The extracted program itself need not be syntactically closed in the
   presentation used by [computable].  [L_computable_can_closed] performs
   the upstream, semantics-preserving closure conversion. *)
Theorem computable_unary_graph_L_computable_closed
    (f : nat -> nat) (Hf : computable f) :
  L_computable_closed (unaryGraph f).
Proof.
  apply (proj2 (L_computable_can_closed (unaryGraph f))).
  exists (@ext _ (!nat ~> !nat) f Hf).
  intro v.
  dependent destruction v. rename h into x.
  dependent destruction v.
  cbn [unaryGraph Vector.fold_left Vector.nth].
  split.
  - intro y. split.
    + intros ->. apply extracted_unary_eval.
    + intro Heval.
      pose proof (extracted_unary_eval Hf x) as Hcorrect.
      apply (proj1 (L_facts.eval_iff _ _)) in Heval.
      apply (proj1 (L_facts.eval_iff _ _)) in Hcorrect.
      pose proof (L_facts.eval_unique Heval Hcorrect) as Heq.
      exact (nat_enc_inj Heq).
  - intros o Heval.
    exists (f x).
    apply (proj1 (L_facts.eval_iff _ _)) in Heval.
    pose proof (extracted_unary_eval Hf x) as Hcorrect.
    apply (proj1 (L_facts.eval_iff _ _)) in Hcorrect.
    exact (L_facts.eval_unique Heval Hcorrect).
Qed.

Theorem computable_binary_graph_L_computable_closed
    (f : nat -> nat -> nat) (Hf : computable f) :
  L_computable_closed (binaryGraph f).
Proof.
  apply (proj2 (L_computable_can_closed (binaryGraph f))).
  exists (@ext _ (!nat ~> !nat ~> !nat) f Hf).
  intro v.
  dependent destruction v. rename h into x.
  dependent destruction v. rename h into y.
  dependent destruction v.
  cbn [binaryGraph Vector.fold_left Vector.nth].
  split.
  - intro z. split.
    + intros ->. apply extracted_binary_eval.
    + intro Heval.
      pose proof (extracted_binary_eval Hf x y) as Hcorrect.
      apply (proj1 (L_facts.eval_iff _ _)) in Heval.
      apply (proj1 (L_facts.eval_iff _ _)) in Hcorrect.
      pose proof (L_facts.eval_unique Heval Hcorrect) as Heq.
      exact (nat_enc_inj Heq).
  - intros o Heval.
    exists (f x y).
    apply (proj1 (L_facts.eval_iff _ _)) in Heval.
    pose proof (extracted_binary_eval Hf x y) as Hcorrect.
    apply (proj1 (L_facts.eval_iff _ _)) in Hcorrect.
    exact (L_facts.eval_unique Heval Hcorrect).
Qed.

Corollary computable_unary_graph_Diophantine'
    (f : nat -> nat) (Hf : computable f) :
  Diophantine' (unaryGraph f).
Proof.
  apply L_computable_closed_to_Diophantine'.
  exact (computable_unary_graph_L_computable_closed Hf).
Qed.

Corollary computable_binary_graph_Diophantine'
    (f : nat -> nat -> nat) (Hf : computable f) :
  Diophantine' (binaryGraph f).
Proof.
  apply L_computable_closed_to_Diophantine'.
  exact (computable_binary_graph_L_computable_closed Hf).
Qed.

Theorem computable_unary_graph_has_PA_formula
    (f : nat -> nat) (Hf : computable f) :
  exists phi : PA.formula, forall v y,
    PA.Formula.Sat PA.natModel (graphEnv v y) phi <-> unaryGraph f v y.
Proof.
  apply Diophantine'_has_PA_formula.
  exact (computable_unary_graph_Diophantine' Hf).
Qed.

Theorem computable_binary_graph_has_PA_formula
    (f : nat -> nat -> nat) (Hf : computable f) :
  exists phi : PA.formula, forall v z,
    PA.Formula.Sat PA.natModel (graphEnv v z) phi <-> binaryGraph f v z.
Proof.
  apply Diophantine'_has_PA_formula.
  exact (computable_binary_graph_Diophantine' Hf).
Qed.

(* [Diophantine'_has_PA_formula] returns its formula in Prop.  Classical
   epsilon lets clients name one such formula.  It does not give an
   executable extraction of the polynomial witness hidden in a proof of
   [Diophantine']; clients needing computational content should retain the
   explicit polynomial API from DiophantineFormula.v instead. *)
Definition chosenGraphFormula {k}
    (R : Vector.t nat k -> nat -> Prop) : PA.formula :=
  epsilon (inhabits PA.pBot)
    (fun phi => forall v y,
      PA.Formula.Sat PA.natModel (graphEnv v y) phi <-> R v y).

Theorem chosenGraphFormula_correct {k}
    (R : Vector.t nat k -> nat -> Prop) :
  Diophantine' R -> forall v y,
    PA.Formula.Sat PA.natModel (graphEnv v y) (chosenGraphFormula R)
      <-> R v y.
Proof.
  intro HR.
  unfold chosenGraphFormula.
  apply epsilon_spec.
  now apply Diophantine'_has_PA_formula.
Qed.

Definition unaryGraphFormula (f : nat -> nat) : PA.formula :=
  chosenGraphFormula (unaryGraph f).

Definition binaryGraphFormula (f : nat -> nat -> nat) : PA.formula :=
  chosenGraphFormula (binaryGraph f).

Theorem unaryGraphFormula_correct
    (f : nat -> nat) (Hf : computable f) : forall v y,
  PA.Formula.Sat PA.natModel (graphEnv v y) (unaryGraphFormula f)
    <-> unaryGraph f v y.
Proof.
  apply chosenGraphFormula_correct.
  exact (computable_unary_graph_Diophantine' Hf).
Qed.

Theorem binaryGraphFormula_correct
    (f : nat -> nat -> nat) (Hf : computable f) : forall v z,
  PA.Formula.Sat PA.natModel (graphEnv v z) (binaryGraphFormula f)
    <-> binaryGraph f v z.
Proof.
  apply chosenGraphFormula_correct.
  exact (computable_binary_graph_Diophantine' Hf).
Qed.

(* Concrete input vectors and specialized specifications.  By the
   [graphEnv] convention proved in DiophantineFormula.v, the environments
   below are output-first: index 0 is the result, followed by the inputs. *)
Definition unaryInputs (x : nat) : Vector.t nat 1 :=
  Vector.cons nat x 0 (Vector.nil nat).

Definition binaryInputs (x y : nat) : Vector.t nat 2 :=
  Vector.cons nat x 1 (Vector.cons nat y 0 (Vector.nil nat)).

Corollary unaryGraphFormula_output_first
    (f : nat -> nat) (Hf : computable f) (x y : nat) :
  PA.Formula.Sat PA.natModel (graphEnv (unaryInputs x) y)
    (unaryGraphFormula f) <-> y = f x.
Proof.
  rewrite unaryGraphFormula_correct by exact Hf.
  reflexivity.
Qed.

Corollary binaryGraphFormula_output_first
    (f : nat -> nat -> nat) (Hf : computable f) (x y z : nat) :
  PA.Formula.Sat PA.natModel (graphEnv (binaryInputs x y) z)
    (binaryGraphFormula f) <-> z = f x y.
Proof.
  rewrite binaryGraphFormula_correct by exact Hf.
  reflexivity.
Qed.
