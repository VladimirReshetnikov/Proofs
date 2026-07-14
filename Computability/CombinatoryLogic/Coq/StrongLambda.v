(* ===================================================================== *)
(*  StrongLambda.v                                                      *)
(*                                                                       *)
(*  Full contextual beta reduction and canonical closed Church numerals. *)
(*  Unlike the weak relation in [Lambda], [strong_step] also reduces      *)
(*  below lambda binders.                                                 *)
(* ===================================================================== *)

From CombinatoryLogic Require Import Reduction Lambda.

Set Implicit Arguments.

Module StrongUntypedLambda.

Import UntypedLambda.

(* The variable context is an index rather than a fixed parameter because
   the lambda-body constructor recursively reduces at [option V]. *)
Inductive strong_step : forall V : Type, term V -> term V -> Prop :=
| strong_step_beta : forall (V : Type) (body : term (option V))
    (argument : term V),
    @strong_step V (app (lam body) argument) (subst0 argument body)
| strong_step_app_left : forall (V : Type) (lhs lhs' rhs : term V),
    @strong_step V lhs lhs' ->
    @strong_step V (app lhs rhs) (app lhs' rhs)
| strong_step_app_right : forall (V : Type) (lhs rhs rhs' : term V),
    @strong_step V rhs rhs' ->
    @strong_step V (app lhs rhs) (app lhs rhs')
| strong_step_lam_body : forall (V : Type)
    (body body' : term (option V)),
    @strong_step (option V) body body' ->
    @strong_step V (lam body) (lam body').

Arguments strong_step {V} _ _.
Arguments strong_step_beta {V} body argument.
Arguments strong_step_app_left {V} lhs lhs' rhs _.
Arguments strong_step_app_right {V} lhs rhs rhs' _.
Arguments strong_step_lam_body {V} body body' _.

Definition strong_reaches {V : Type} : term V -> term V -> Prop :=
  Reduction.star (@strong_step V).

Definition strong_progresses {V : Type} : term V -> term V -> Prop :=
  Reduction.plus (@strong_step V).

Lemma strong_progresses_to_reaches : forall (V : Type) (x y : term V),
  strong_progresses x y -> strong_reaches x y.
Proof.
  intros V x y h.
  exact (Reduction.plus_to_star h).
Qed.

Lemma step_to_strong_step : forall (V : Type) (x y : term V),
  step x y -> strong_step x y.
Proof.
  intros V x y h.
  induction h as
      [body argument
      | lhs lhs' rhs lhsStep ih
      | lhs rhs rhs' rhsStep ih].
  - apply strong_step_beta.
  - now apply strong_step_app_left.
  - now apply strong_step_app_right.
Qed.

Lemma reaches_to_strong_reaches : forall (V : Type) (x y : term V),
  reaches x y -> strong_reaches x y.
Proof.
  intros V x y h.
  apply (@Reduction.star_map (term V) (term V) (@step V)
    (@strong_step V) (fun t => t)).
  - intros a b stepAB. now apply step_to_strong_step.
  - exact h.
Qed.

Lemma progresses_to_strong_progresses : forall (V : Type) (x y : term V),
  progresses x y -> strong_progresses x y.
Proof.
  intros V x y h.
  apply (@Reduction.plus_map (term V) (term V) (@step V)
    (@strong_step V) (fun t => t)).
  - intros a b stepAB. now apply step_to_strong_step.
  - exact h.
Qed.

Definition strong_normal {V : Type} (t : term V) : Prop :=
  forall next : term V, ~ strong_step t next.

Definition strong_normalizes {V : Type} (t : term V) : Prop :=
  exists normal : term V,
    strong_reaches t normal /\ strong_normal normal.

(* A structural presentation of full beta normal forms.  At an application,
   the function must not itself be a lambda and both children must be normal. *)
Fixpoint strong_normal_shape {V : Type} (t : term V) : Prop :=
  match t with
  | var _ => True
  | app function argument =>
      match function with
      | lam _ => False
      | _ => strong_normal_shape function /\ strong_normal_shape argument
      end
  | lam body => strong_normal_shape body
  end.

Lemma strong_normal_shape_app_left : forall (V : Type)
    (function argument : term V),
  strong_normal_shape (app function argument) ->
  strong_normal_shape function.
Proof.
  intros V function argument h.
  destruct function; cbn [strong_normal_shape] in *.
  - exact I.
  - exact (proj1 h).
  - contradiction.
Qed.

Lemma strong_normal_shape_app_right : forall (V : Type)
    (function argument : term V),
  strong_normal_shape (app function argument) ->
  strong_normal_shape argument.
Proof.
  intros V function argument h.
  destruct function; cbn [strong_normal_shape] in *.
  - exact (proj2 h).
  - exact (proj2 h).
  - contradiction.
Qed.

Lemma strong_normal_shape_no_step : forall (V : Type) (source target : term V),
  strong_step source target -> strong_normal_shape source -> False.
Proof.
  intros V source target hStep.
  induction hStep as
      [V body argument
      | V lhs lhs' rhs lhsStep ih
      | V lhs rhs rhs' rhsStep ih
      | V body body' bodyStep ih]; intro hNormal.
  - exact hNormal.
  - apply ih.
    now apply strong_normal_shape_app_left with (argument := rhs).
  - apply ih.
    now apply strong_normal_shape_app_right with (function := lhs).
  - apply ih.
    exact hNormal.
Qed.

Lemma strong_normal_shape_sound : forall (V : Type) (t : term V),
  strong_normal_shape t -> strong_normal t.
Proof.
  intros V t hShape next hStep.
  exact (strong_normal_shape_no_step hStep hShape).
Qed.

Lemma strong_normal_shape_complete : forall (V : Type) (t : term V),
  strong_normal t -> strong_normal_shape t.
Proof.
  intros V t.
  induction t as [V x | V lhs IHlhs rhs IHrhs | V body IHbody];
    intro hNormal; cbn [strong_normal_shape].
  - exact I.
  - assert (hLeft : strong_normal lhs).
    { intros lhs' lhsStep.
      apply (hNormal (app lhs' rhs)).
      now apply strong_step_app_left. }
    assert (hRight : strong_normal rhs).
    { intros rhs' rhsStep.
      apply (hNormal (app lhs rhs')).
      now apply strong_step_app_right. }
    specialize (IHlhs hLeft).
    specialize (IHrhs hRight).
    destruct lhs as [xLeft | lhsFunction lhsArgument | lhsBody];
      cbn [strong_normal_shape] in *.
    + exact (conj I IHrhs).
    + exact (conj IHlhs IHrhs).
    + apply (hNormal (subst0 rhs lhsBody)).
      apply strong_step_beta.
  - apply IHbody.
    intros body' bodyStep.
    apply (hNormal (lam body')).
    now apply strong_step_lam_body.
Qed.

Theorem strong_normal_iff_shape : forall (V : Type) (t : term V),
  strong_normal t <-> strong_normal_shape t.
Proof.
  intros V t.
  split.
  - apply strong_normal_shape_complete.
  - apply strong_normal_shape_sound.
Qed.

Fixpoint apply_many {V : Type} (head : term V)
    (arguments : list (term V)) : term V :=
  match arguments with
  | nil => head
  | cons argument rest => apply_many (app head argument) rest
  end.

Fixpoint iter_app {V : Type} (function : term V) (count : nat)
    (argument : term V) : term V :=
  match count with
  | O => argument
  | S previous => app function (iter_app function previous argument)
  end.

(* In the twice-extended empty context, [None] is [x] and [Some None] is
   [f]. *)
Fixpoint church_body (count : nat) : term (option (option Empty_set)) :=
  match count with
  | O => var None
  | S previous => app (var (Some None)) (church_body previous)
  end.

Definition church (count : nat) : term Empty_set :=
  lam (lam (church_body count)).

Lemma church_body_eq_iter_app : forall count,
  church_body count = iter_app (var (Some None)) count (var None).
Proof.
  induction count as [|count ih]; cbn [church_body iter_app].
  - reflexivity.
  - now rewrite ih.
Qed.

Lemma var_strong_normal : forall (V : Type) (x : V),
  strong_normal (var x).
Proof.
  intros V x.
  apply strong_normal_shape_sound.
  exact I.
Qed.

Lemma app_var_strong_normal : forall (V : Type) (x : V) (argument : term V),
  strong_normal argument -> strong_normal (app (var x) argument).
Proof.
  intros V x argument hArgument.
  apply strong_normal_shape_sound.
  cbn [strong_normal_shape].
  split.
  - exact I.
  - now apply strong_normal_shape_complete.
Qed.

Lemma lam_strong_normal : forall (V : Type) (body : term (option V)),
  strong_normal body -> strong_normal (lam body).
Proof.
  intros V body hBody.
  apply strong_normal_shape_sound.
  cbn [strong_normal_shape].
  now apply strong_normal_shape_complete.
Qed.

Lemma church_body_strong_normal : forall count,
  strong_normal (church_body count).
Proof.
  induction count as [|count ih]; cbn [church_body].
  - apply var_strong_normal.
  - now apply app_var_strong_normal.
Qed.

Theorem church_strong_normal : forall count,
  strong_normal (church count).
Proof.
  intro count.
  apply lam_strong_normal.
  apply lam_strong_normal.
  apply church_body_strong_normal.
Qed.

Theorem church_strong_normalizes : forall count,
  strong_normalizes (church count).
Proof.
  intro count.
  exists (church count).
  split.
  - apply Reduction.star_refl.
  - apply church_strong_normal.
Qed.

Lemma church_body_injective : forall left right,
  church_body left = church_body right -> left = right.
Proof.
  induction left as [|left ih]; destruct right as [|right]; intro equality.
  - reflexivity.
  - discriminate equality.
  - discriminate equality.
  - injection equality as bodyEquality.
    f_equal.
    now apply ih.
Qed.

Theorem church_injective : forall left right,
  church left = church right -> left = right.
Proof.
  intros left right equality.
  injection equality as bodyEquality.
  now apply church_body_injective.
Qed.

End StrongUntypedLambda.
