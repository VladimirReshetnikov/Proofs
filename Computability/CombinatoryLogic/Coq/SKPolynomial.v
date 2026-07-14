(* ===================================================================== *)
(*  SKPolynomial.v                                                      *)
(*                                                                       *)
(*  S-K applicative polynomials with inert variables.  The occurs-aware  *)
(*  bracket abstraction is essential: a polynomial independent of the    *)
(*  newly bound variable is abstracted as [K p] directly.  This makes     *)
(*  abstraction commute syntactically with lifted substitutions.          *)
(* ===================================================================== *)

From CombinatoryLogic Require Import Reduction.

Set Implicit Arguments.

Module SKPolynomial.

Inductive term (V : Type) : Type :=
| var : V -> term V
| konst : term V
| scomb : term V
| app : term V -> term V -> term V.

Arguments var {V} _.
Arguments konst {V}.
Arguments scomb {V}.
Arguments app {V} _ _.

Fixpoint map {A B : Type} (f : A -> B) (t : term A) : term B :=
  match t with
  | var x => var (f x)
  | konst => konst
  | scomb => scomb
  | app lhs rhs => app (map f lhs) (map f rhs)
  end.

Fixpoint bind {A B : Type} (sigma : A -> term B) (t : term A) : term B :=
  match t with
  | var x => sigma x
  | konst => konst
  | scomb => scomb
  | app lhs rhs => app (bind sigma lhs) (bind sigma rhs)
  end.

Lemma bind_ext : forall (A B : Type) (sigma tau : A -> term B) t,
  (forall x, sigma x = tau x) -> bind sigma t = bind tau t.
Proof.
  intros A B sigma tau t hext.
  induction t as [x | | |lhs IHlhs rhs IHrhs]; cbn [bind].
  - apply hext.
  - reflexivity.
  - reflexivity.
  - now rewrite IHlhs, IHrhs.
Qed.

Lemma map_as_bind : forall (A B : Type) (f : A -> B) t,
  map f t = bind (fun x => var (f x)) t.
Proof.
  intros A B f t.
  induction t as [x | | |lhs IHlhs rhs IHrhs]; cbn [map bind].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - now rewrite IHlhs, IHrhs.
Qed.

Definition liftSubst {A B : Type} (sigma : A -> term B)
    (x : option A) : term (option B) :=
  match x with
  | None => var None
  | Some a => map (@Some B) (sigma a)
  end.

Definition option_map {A B : Type} (f : A -> B) (x : option A) : option B :=
  match x with
  | None => None
  | Some a => Some (f a)
  end.

(* Remove the newest variable if it is absent. *)
Fixpoint lower {V : Type} (t : term (option V)) : option (term V) :=
  match t with
  | var None => None
  | var (Some x) => Some (var x)
  | konst => Some konst
  | scomb => Some scomb
  | app lhs rhs =>
      match lower lhs, lower rhs with
      | Some lhs', Some rhs' => Some (app lhs' rhs')
      | _, _ => None
      end
  end.

Lemma lower_map_some : forall (V : Type) (t : term V),
  lower (map (@Some V) t) = Some t.
Proof.
  intros V t.
  induction t as [x | | |lhs IHlhs rhs IHrhs]; cbn [map lower].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - now rewrite IHlhs, IHrhs.
Qed.

Lemma lower_bind_lift : forall (A B : Type) (sigma : A -> term B)
    (t : term (option A)),
  lower (bind (liftSubst sigma) t) = option_map (bind sigma) (lower t).
Proof.
  intros A B sigma t.
  induction t as [x | | |lhs IHlhs rhs IHrhs].
  - destruct x as [a | ]; cbn [bind liftSubst lower option_map].
    + apply lower_map_some.
    + reflexivity.
  - reflexivity.
  - reflexivity.
  - cbn [bind lower].
    rewrite IHlhs, IHrhs.
    destruct (lower lhs) as [lhs' | ];
      destruct (lower rhs) as [rhs' | ]; reflexivity.
Qed.

Definition subst0 {V : Type} (argument : term V)
    (body : term (option V)) : term V :=
  bind
    (fun x =>
      match x with
      | None => argument
      | Some v => var v
      end)
    body.

Lemma lower_sound : forall (V : Type) (body : term (option V)) lowered,
  lower body = Some lowered ->
  forall argument, subst0 argument body = lowered.
Proof.
  intros V body.
  induction body as [x | | |lhs IHlhs rhs IHrhs]; intros lowered hlower argument.
  - destruct x as [v | ]; cbn [lower] in hlower.
    + injection hlower as heq. subst lowered. reflexivity.
    + discriminate.
  - injection hlower as heq. subst lowered. reflexivity.
  - injection hlower as heq. subst lowered. reflexivity.
  - cbn [lower] in hlower.
    destruct (lower lhs) as [lhs' | ] eqn:hlhs; try discriminate.
    destruct (lower rhs) as [rhs' | ] eqn:hrhs; try discriminate.
    injection hlower as heq. subst lowered.
    change (app (subst0 argument lhs) (subst0 argument rhs) =
      app lhs' rhs').
    now rewrite (IHlhs lhs' eq_refl argument),
      (IHrhs rhs' eq_refl argument).
Qed.

Inductive step {V : Type} : term V -> term V -> Prop :=
| step_konst : forall x y,
    step (app (app konst x) y) x
| step_scomb : forall x y z,
    step (app (app (app scomb x) y) z)
      (app (app x z) (app y z))
| step_app_left : forall x x' y,
    step x x' -> step (app x y) (app x' y)
| step_app_right : forall x y y',
    step y y' -> step (app x y) (app x y').

Definition reaches {V : Type} : term V -> term V -> Prop :=
  Reduction.star step.

Definition progresses {V : Type} : term V -> term V -> Prop :=
  Reduction.plus step.

Lemma reaches_refl : forall (V : Type) (t : term V), reaches t t.
Proof. intros V t; apply Reduction.star_refl. Qed.

Lemma reaches_one : forall (V : Type) (x y : term V),
  step x y -> reaches x y.
Proof. intros V x y h; exact (@Reduction.star_one (term V) step x y h). Qed.

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

Definition ident {V : Type} : term V := app (app scomb konst) konst.

Theorem ident_correct : forall (V : Type) (x : term V),
  reaches (app ident x) x.
Proof.
  intros V x.
  unfold ident.
  eapply Reduction.star_step.
  - apply step_scomb.
  - eapply Reduction.star_step.
    + apply step_konst.
    + apply Reduction.star_refl.
Qed.

Theorem ident_correct_positive : forall (V : Type) (x : term V),
  progresses (app ident x) x.
Proof.
  intros V x.
  unfold progresses, ident.
  eapply Reduction.plus_step.
  - apply step_scomb.
  - eapply Reduction.star_step.
    + apply step_konst.
    + apply Reduction.star_refl.
Qed.

(* Occurs-aware bracket abstraction. *)
Fixpoint abstract {V : Type} (body : term (option V)) : term V :=
  match lower body with
  | Some lowered => app konst lowered
  | None =>
      match body with
      | var _ => ident
      | app lhs rhs => app (app scomb (abstract lhs)) (abstract rhs)
      | konst | scomb => ident (* unreachable: [lower] is [Some] *)
      end
  end.

Lemma abstract_equation : forall (V : Type) (body : term (option V)),
  abstract body =
    match lower body with
    | Some lowered => app konst lowered
    | None =>
        match body with
        | var _ => ident
        | app lhs rhs => app (app scomb (abstract lhs)) (abstract rhs)
        | konst | scomb => ident
        end
    end.
Proof.
  intros V body.
  destruct body; reflexivity.
Qed.

Lemma abstract_map_some : forall (V : Type) (body : term V),
  abstract (map (@Some V) body) = app konst body.
Proof.
  intros V body.
  destruct body as [x | | |lhs rhs]; cbn [map].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold abstract.
    cbn [lower].
    now rewrite !lower_map_some.
Qed.

Theorem abstract_correct : forall (V : Type) (body : term (option V)) argument,
  reaches (app (abstract body) argument) (subst0 argument body).
Proof.
  intros V body.
  induction body as [x | | |lhs IHlhs rhs IHrhs]; intro argument;
    unfold abstract; fold (@abstract V); destruct (lower _) as [lowered | ] eqn:hlower.
  - apply lower_sound with (argument := argument) in hlower.
    rewrite hlower. apply reaches_one. apply step_konst.
  - destruct x as [v | ]; cbn [lower] in hlower.
    + discriminate.
    + apply ident_correct.
  - apply lower_sound with (argument := argument) in hlower.
    rewrite hlower. apply reaches_one. apply step_konst.
  - cbn [lower] in hlower. discriminate.
  - apply lower_sound with (argument := argument) in hlower.
    rewrite hlower. apply reaches_one. apply step_konst.
  - cbn [lower] in hlower. discriminate.
  - apply lower_sound with (argument := argument) in hlower.
    rewrite hlower. apply reaches_one. apply step_konst.
  - eapply reaches_trans.
    + apply reaches_one. apply step_scomb.
    + eapply reaches_trans.
      * apply reaches_app_left. apply IHlhs.
      * apply reaches_app_right. apply IHrhs.
Qed.

Theorem abstract_correct_positive :
  forall (V : Type) (body : term (option V)) argument,
  progresses (app (abstract body) argument) (subst0 argument body).
Proof.
  intros V body.
  induction body as [x | | |lhs IHlhs rhs IHrhs]; intro argument;
    unfold abstract; fold (@abstract V); destruct (lower _) as [lowered | ] eqn:hlower.
  - apply lower_sound with (argument := argument) in hlower.
    rewrite hlower. apply Reduction.plus_one. apply step_konst.
  - destruct x as [v | ]; cbn [lower] in hlower.
    + discriminate.
    + apply ident_correct_positive.
  - apply lower_sound with (argument := argument) in hlower.
    rewrite hlower. apply Reduction.plus_one. apply step_konst.
  - cbn [lower] in hlower. discriminate.
  - apply lower_sound with (argument := argument) in hlower.
    rewrite hlower. apply Reduction.plus_one. apply step_konst.
  - cbn [lower] in hlower. discriminate.
  - apply lower_sound with (argument := argument) in hlower.
    rewrite hlower. apply Reduction.plus_one. apply step_konst.
  - eapply Reduction.plus_step.
    + apply step_scomb.
    + eapply reaches_trans.
      * apply reaches_app_left. apply abstract_correct.
      * apply reaches_app_right. apply abstract_correct.
Qed.

Theorem abstract_natural : forall (A B : Type) (sigma : A -> term B)
    (body : term (option A)),
  abstract (bind (liftSubst sigma) body) = bind sigma (abstract body).
Proof.
  intros A B sigma body.
  induction body as [x | | |lhs IHlhs rhs IHrhs].
  - destruct x as [a | ].
    + cbn [bind liftSubst].
      change (abstract (map (@Some B) (sigma a)) = app konst (sigma a)).
      apply abstract_map_some.
    + reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite (abstract_equation (bind (liftSubst sigma) (app lhs rhs))).
    rewrite lower_bind_lift.
    rewrite (abstract_equation (app lhs rhs)).
    destruct (lower (app lhs rhs)) as [lowered | ] eqn:hlower;
      cbn [option_map bind].
    + reflexivity.
    + now rewrite IHlhs, IHrhs.
Qed.

Theorem abstract_map : forall (A B : Type) (f : A -> B)
    (body : term (option A)),
  abstract (map (option_map f) body) = map f (abstract body).
Proof.
  intros A B f body.
  rewrite !map_as_bind.
  transitivity
    (abstract (bind (liftSubst (fun x => var (f x))) body)).
  - f_equal.
    apply bind_ext.
    intros [x | ]; reflexivity.
  - apply abstract_natural.
Qed.

End SKPolynomial.
