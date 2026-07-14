(* ===================================================================== *)
(*  Lambda.v                                                            *)
(*                                                                       *)
(*  Intrinsically scoped untyped lambda terms.  A body uses [option V]:   *)
(*  [None] is its bound variable and [Some v] is an outer free variable.  *)
(*  Reduction is weak contextual beta reduction: both children of an      *)
(*  application reduce, while lambda bodies are not reduced in place.     *)
(* ===================================================================== *)

From CombinatoryLogic Require Import Reduction.

Set Implicit Arguments.

Module UntypedLambda.

Inductive term (V : Type) : Type :=
| var : V -> term V
| app : term V -> term V -> term V
| lam : term (option V) -> term V.

Arguments var {V} _.
Arguments app {V} _ _.
Arguments lam {V} _.

Definition option_map {A B : Type} (f : A -> B) (x : option A) : option B :=
  match x with
  | None => None
  | Some a => Some (f a)
  end.

Fixpoint map {A B : Type} (f : A -> B) (t : term A) : term B :=
  match t with
  | var x => var (f x)
  | app lhs rhs => app (map f lhs) (map f rhs)
  | lam body => lam (map (option_map f) body)
  end.

Definition liftSubst {A B : Type} (sigma : A -> term B)
    (x : option A) : term (option B) :=
  match x with
  | None => var None
  | Some a => map (@Some B) (sigma a)
  end.

Fixpoint bind {A B : Type} (sigma : A -> term B) (t : term A) : term B :=
  match t with
  | var x => sigma x
  | app lhs rhs => app (bind sigma lhs) (bind sigma rhs)
  | lam body => lam (bind (liftSubst sigma) body)
  end.

Definition subst0 {A : Type} (argument : term A)
    (body : term (option A)) : term A :=
  bind
    (fun x =>
      match x with
      | None => argument
      | Some a => var a
      end)
    body.

(* Standard renaming and substitution laws for the intrinsically scoped   *)
(* representation.  Keeping these laws at the lambda-calculus layer makes *)
(* later semantic encodings independent of de Bruijn bookkeeping.         *)
Lemma map_ext : forall (A B : Type) (f g : A -> B) t,
  (forall x, f x = g x) -> map f t = map g t.
Proof.
  intros A B f g t.
  revert B f g.
  induction t as [V x | V lhs IHlhs rhs IHrhs | V body IHbody];
    intros B f g hext; cbn [map].
  - now rewrite hext.
  - now rewrite (IHlhs B f g hext), (IHrhs B f g hext).
  - f_equal.
    apply IHbody.
    intros [x | ]; cbn [option_map].
    + now rewrite hext.
    + reflexivity.
Qed.

Lemma map_comp : forall (A B C : Type) (f : A -> B) (g : B -> C) t,
  map g (map f t) = map (fun x => g (f x)) t.
Proof.
  intros A B C f g t.
  revert B C f g.
  induction t as [V x | V lhs IHlhs rhs IHrhs | V body IHbody];
    intros B C f g; cbn [map].
  - reflexivity.
  - now rewrite IHlhs, IHrhs.
  - f_equal.
    rewrite IHbody.
    apply map_ext.
    intros [x | ]; reflexivity.
Qed.

Lemma bind_ext : forall (A B : Type) (sigma tau : A -> term B) t,
  (forall x, sigma x = tau x) -> bind sigma t = bind tau t.
Proof.
  intros A B sigma tau t.
  revert B sigma tau.
  induction t as [V x | V lhs IHlhs rhs IHrhs | V body IHbody];
    intros B sigma tau hext; cbn [bind].
  - apply hext.
  - now rewrite (IHlhs B sigma tau hext), (IHrhs B sigma tau hext).
  - f_equal.
    apply IHbody.
    intros [x | ]; cbn [liftSubst].
    + now rewrite hext.
    + reflexivity.
Qed.

Lemma bind_var : forall (V : Type) (t : term V),
  bind (@var V) t = t.
Proof.
  intros V t.
  induction t as [V x | V lhs IHlhs rhs IHrhs | V body IHbody];
    cbn [bind].
  - reflexivity.
  - now rewrite IHlhs, IHrhs.
  - f_equal.
    transitivity (bind (@var (option V)) body).
    + apply bind_ext.
      intros [x | ]; reflexivity.
    + exact IHbody.
Qed.

Lemma bind_map : forall (A B C : Type) (f : A -> B)
    (sigma : B -> term C) t,
  bind sigma (map f t) = bind (fun x => sigma (f x)) t.
Proof.
  intros A B C f sigma t.
  revert B C f sigma.
  induction t as [V x | V lhs IHlhs rhs IHrhs | V body IHbody];
    intros B C f sigma; cbn [map bind].
  - reflexivity.
  - now rewrite IHlhs, IHrhs.
  - f_equal.
    rewrite IHbody.
    apply bind_ext.
    intros [x | ]; reflexivity.
Qed.

Lemma map_bind : forall (A B C : Type) (sigma : A -> term B)
    (f : B -> C) t,
  map f (bind sigma t) = bind (fun x => map f (sigma x)) t.
Proof.
  intros A B C sigma f t.
  revert B C sigma f.
  induction t as [V x | V lhs IHlhs rhs IHrhs | V body IHbody];
    intros B C sigma f; cbn [map bind].
  - reflexivity.
  - now rewrite IHlhs, IHrhs.
  - f_equal.
    rewrite IHbody.
    apply bind_ext.
    intros [x | ]; cbn [liftSubst].
    + rewrite !map_comp.
      apply map_ext.
      intro y. reflexivity.
    + reflexivity.
Qed.

Lemma subst0_map_some : forall (V : Type) (argument t : term V),
  subst0 argument (map (@Some V) t) = t.
Proof.
  intros V argument t.
  unfold subst0.
  rewrite bind_map.
  transitivity (bind (@var V) t).
  - apply bind_ext.
    intro x. reflexivity.
  - apply bind_var.
Qed.

Inductive step {V : Type} : term V -> term V -> Prop :=
| step_beta : forall body argument,
    step (app (lam body) argument) (subst0 argument body)
| step_app_left : forall lhs lhs' rhs,
    step lhs lhs' -> step (app lhs rhs) (app lhs' rhs)
| step_app_right : forall lhs rhs rhs',
    step rhs rhs' -> step (app lhs rhs) (app lhs rhs').

Definition reaches {V : Type} : term V -> term V -> Prop :=
  Reduction.star step.

Definition progresses {V : Type} : term V -> term V -> Prop :=
  Reduction.plus step.

Lemma reaches_refl : forall (V : Type) (t : term V), reaches t t.
Proof. intros V t; apply Reduction.star_refl. Qed.

Lemma reaches_trans : forall (V : Type) (x y z : term V),
  reaches x y -> reaches y z -> reaches x z.
Proof. intros V x y z; apply Reduction.star_trans. Qed.

Lemma reaches_app_left : forall (V : Type) (x x' y : term V),
  reaches x x' -> reaches (app x y) (app x' y).
Proof.
  intros V x x' y h.
  eapply Reduction.star_map with (f := fun t => app t y) in h.
  - exact h.
  - intros a b hab. now apply step_app_left.
Qed.

Lemma reaches_app_right : forall (V : Type) (x y y' : term V),
  reaches y y' -> reaches (app x y) (app x y').
Proof.
  intros V x y y' h.
  eapply Reduction.star_map with (f := fun t => app x t) in h.
  - exact h.
  - intros a b hab. now apply step_app_right.
Qed.

Lemma progresses_app_left : forall (V : Type) (x x' y : term V),
  progresses x x' -> progresses (app x y) (app x' y).
Proof.
  intros V x x' y h.
  eapply Reduction.plus_map with (f := fun t => app t y) in h.
  - exact h.
  - intros a b hab. now apply step_app_left.
Qed.

Lemma progresses_app_right : forall (V : Type) (x y y' : term V),
  progresses y y' -> progresses (app x y) (app x y').
Proof.
  intros V x y y' h.
  eapply Reduction.plus_map with (f := fun t => app x t) in h.
  - exact h.
  - intros a b hab. now apply step_app_right.
Qed.

Fixpoint size {V : Type} (t : term V) : nat :=
  match t with
  | var _ => 1
  | app lhs rhs => 1 + size lhs + size rhs
  | lam body => 1 + size body
  end.

Definition delta : term Empty_set :=
  lam (app (var None) (var None)).

Definition omega : term Empty_set := app delta delta.

Theorem omega_step : step omega omega.
Proof.
  change (step (app delta delta)
    (subst0 delta (app (var None) (var None)))).
  apply step_beta.
Qed.

Theorem omega_positive_cycle : progresses omega omega.
Proof.
  apply Reduction.plus_one.
  exact omega_step.
Qed.

End UntypedLambda.
