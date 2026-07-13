(* Monotonicity of intuitionistic and classical entailment. *)

From Stdlib Require Import List.
From NaturalDeduction Require Import Calculus.
Import ListNotations.
Import NaturalDeduction.

Set Implicit Arguments.

Module Monotonicity.

Definition included {A : Type} (Gamma Delta : context A) : Prop :=
  forall p, In p Gamma -> In p Delta.

Lemma included_cons : forall A (Gamma Delta : context A) p,
    included Gamma Delta -> included (p :: Gamma) (p :: Delta).
Proof.
  intros A Gamma Delta p Hsub q Hq.
  destruct Hq as [Heq | Hq].
  - left. exact Heq.
  - right. exact (Hsub q Hq).
Qed.

Lemma included_into_cons : forall A (Gamma : context A) p,
    included Gamma (p :: Gamma).
Proof.
  intros A Gamma p q Hq. right. exact Hq.
Qed.

(** General weakening: a derivation remains valid in every larger context. *)
Theorem derives_weaken : forall A (axiom : formula A -> Prop) Gamma p,
    derives axiom Gamma p ->
    forall Delta, included Gamma Delta -> derives axiom Delta p.
Proof.
  intros A axiom Gamma p H.
  induction H as
    [ Gamma p Hp
    | Gamma p Hp
    | Gamma p Hfalse IHfalse
    | Gamma p q Hp IHp Hq IHq
    | Gamma p q Hpq IHpq
    | Gamma p q Hpq IHpq
    | Gamma p q Hp IHp
    | Gamma p q Hq IHq
    | Gamma p q r Hpq IHpq Hp IHp Hq IHq
    | Gamma p q Hq IHq
    | Gamma p q Hpq IHpq Hp IHp ];
    intros Delta Hsub.
  - apply D_assumption. exact (Hsub p Hp).
  - apply D_axiom. exact Hp.
  - apply D_falseElim. exact (IHfalse Delta Hsub).
  - apply D_andIntro.
    + exact (IHp Delta Hsub).
    + exact (IHq Delta Hsub).
  - apply D_andElimLeft with (q := q). exact (IHpq Delta Hsub).
  - apply D_andElimRight with (p := p). exact (IHpq Delta Hsub).
  - apply D_orIntroLeft. exact (IHp Delta Hsub).
  - apply D_orIntroRight. exact (IHq Delta Hsub).
  - apply D_orElim with (p := p) (q := q).
    + exact (IHpq Delta Hsub).
    + apply IHp. apply included_cons. exact Hsub.
    + apply IHq. apply included_cons. exact Hsub.
  - apply D_impIntro. apply IHq. apply included_cons. exact Hsub.
  - apply D_impElim with (p := p).
    + exact (IHpq Delta Hsub).
    + exact (IHp Delta Hsub).
Qed.

(** The displayed rule [Gamma |- C / Gamma,A |- C]. *)
Theorem derives_add_assumption : forall A (axiom : formula A -> Prop) Gamma p a,
    derives axiom Gamma p -> derives axiom (a :: Gamma) p.
Proof.
  intros A axiom Gamma p a H.
  apply (derives_weaken H).
  apply included_into_cons.
Qed.

Theorem intuitionistic_monotonicity : forall A (Gamma Delta : context A) p,
    included Gamma Delta ->
    intuitionistically_derives Gamma p ->
    intuitionistically_derives Delta p.
Proof.
  intros A Gamma Delta p Hsub H.
  exact (@derives_weaken A (fun _ => False) Gamma p H Delta Hsub).
Qed.

Theorem intuitionistic_weakening : forall A (Gamma : context A) p a,
    intuitionistically_derives Gamma p ->
    intuitionistically_derives (a :: Gamma) p.
Proof.
  intros A Gamma p a H.
  exact (@derives_add_assumption A (fun _ => False) Gamma p a H).
Qed.

Theorem classical_monotonicity : forall A (Gamma Delta : context A) p,
    included Gamma Delta ->
    classically_derives Gamma p ->
    classically_derives Delta p.
Proof.
  intros A Gamma Delta p Hsub H.
  exact (@derives_weaken A classical_axiom Gamma p H Delta Hsub).
Qed.

Theorem classical_weakening : forall A (Gamma : context A) p a,
    classically_derives Gamma p ->
    classically_derives (a :: Gamma) p.
Proof.
  intros A Gamma p a H.
  exact (@derives_add_assumption A classical_axiom Gamma p a H).
Qed.

End Monotonicity.
