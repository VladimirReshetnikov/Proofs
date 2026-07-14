(*
  Shared propositional natural deduction for the structural-logic examples.

  The calculus is parameterized by additional zero-premise axioms.
  Intuitionistic logic supplies none; classical logic supplies excluded
  middle.  Falsity elimination is an intuitionistic rule here, distinguishing
  this calculus from minimal logic.
*)

From Stdlib Require Import List.
Import ListNotations.

Set Implicit Arguments.

Module NaturalDeduction.

Inductive formula (A : Type) : Type :=
| FAtom : A -> formula A
| Falsum : formula A
| Conj : formula A -> formula A -> formula A
| Disj : formula A -> formula A -> formula A
| Impl : formula A -> formula A -> formula A.

Arguments FAtom {A} _.
Arguments Falsum {A}.
Arguments Conj {A} _ _.
Arguments Disj {A} _ _.
Arguments Impl {A} _ _.

Definition Neg {A : Type} (p : formula A) : formula A := Impl p Falsum.

Definition context (A : Type) := list (formula A).

Inductive derives {A : Type} (axiom : formula A -> Prop) :
    context A -> formula A -> Prop :=
| D_assumption : forall Gamma p, In p Gamma -> derives axiom Gamma p
| D_axiom : forall Gamma p, axiom p -> derives axiom Gamma p
| D_falseElim : forall Gamma p,
    derives axiom Gamma Falsum -> derives axiom Gamma p
| D_andIntro : forall Gamma p q,
    derives axiom Gamma p -> derives axiom Gamma q ->
    derives axiom Gamma (Conj p q)
| D_andElimLeft : forall Gamma p q,
    derives axiom Gamma (Conj p q) -> derives axiom Gamma p
| D_andElimRight : forall Gamma p q,
    derives axiom Gamma (Conj p q) -> derives axiom Gamma q
| D_orIntroLeft : forall Gamma p q,
    derives axiom Gamma p -> derives axiom Gamma (Disj p q)
| D_orIntroRight : forall Gamma p q,
    derives axiom Gamma q -> derives axiom Gamma (Disj p q)
| D_orElim : forall Gamma p q r,
    derives axiom Gamma (Disj p q) ->
    derives axiom (p :: Gamma) r ->
    derives axiom (q :: Gamma) r ->
    derives axiom Gamma r
| D_impIntro : forall Gamma p q,
    derives axiom (p :: Gamma) q -> derives axiom Gamma (Impl p q)
| D_impElim : forall Gamma p q,
    derives axiom Gamma (Impl p q) ->
    derives axiom Gamma p -> derives axiom Gamma q.

Definition intuitionistically_derives {A : Type}
    (Gamma : context A) (p : formula A) : Prop :=
  derives (fun _ => False) Gamma p.

Definition classical_axiom {A : Type} (p : formula A) : Prop :=
  exists q, p = Disj q (Neg q).

Definition classically_derives {A : Type}
    (Gamma : context A) (p : formula A) : Prop :=
  derives classical_axiom Gamma p.

Theorem derives_map_axioms : forall A
    (axiom1 axiom2 : formula A -> Prop),
    (forall p, axiom1 p -> axiom2 p) ->
    forall Gamma p, derives axiom1 Gamma p -> derives axiom2 Gamma p.
Proof.
  intros A axiom1 axiom2 Hax Gamma p H.
  induction H.
  - apply D_assumption. exact H.
  - apply D_axiom. exact (Hax p H).
  - apply D_falseElim. exact IHderives.
  - apply D_andIntro; assumption.
  - apply D_andElimLeft with (q := q). exact IHderives.
  - apply D_andElimRight with (p := p). exact IHderives.
  - apply D_orIntroLeft. exact IHderives.
  - apply D_orIntroRight. exact IHderives.
  - apply D_orElim with (p := p) (q := q); assumption.
  - apply D_impIntro. exact IHderives.
  - apply D_impElim with (p := p); assumption.
Qed.

Theorem classical_excluded_middle : forall A (Gamma : context A) p,
    classically_derives Gamma (Disj p (Neg p)).
Proof.
  intros A Gamma p. apply D_axiom. exists p. reflexivity.
Qed.

Theorem intuitionistic_to_classical : forall A (Gamma : context A) p,
    intuitionistically_derives Gamma p -> classically_derives Gamma p.
Proof.
  intros A Gamma p H.
  unfold intuitionistically_derives in H.
  unfold classically_derives.
  eapply (@derives_map_axioms A (fun _ => False) classical_axiom).
  - intros q Hfalse. contradiction.
  - exact H.
Qed.

End NaturalDeduction.

