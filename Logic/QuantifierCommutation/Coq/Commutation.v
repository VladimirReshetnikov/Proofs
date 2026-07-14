(*
  Constructive commutation laws for adjacent quantifiers.

  Universal quantifiers commute, as do existential quantifiers.  The
  definitions at the end make the two nonstandard nested quantifiers used by
  the counterexamples completely explicit: [no_exists] is intuitionistic
  negation of an existential, and [exists_unique] uses Rocq's standard
  [exists!] semantics.
*)

Set Implicit Arguments.

Module QuantifierLaws.

(** Adjacent universal quantifiers commute over arbitrary types. *)
Theorem forall_forall_commute : forall (X Y : Type) (R : X -> Y -> Prop),
    (forall x, forall y, R x y) <->
    (forall y, forall x, R x y).
Proof.
  intros X Y R. split.
  - intros H y x. exact (H x y).
  - intros H x y. exact (H y x).
Qed.

(** Adjacent existential quantifiers commute over arbitrary types. *)
Theorem exists_exists_commute : forall (X Y : Type) (R : X -> Y -> Prop),
    (exists x, exists y, R x y) <->
    (exists y, exists x, R x y).
Proof.
  intros X Y R. split.
  - intros [x [y Hxy]]. exists y, x. exact Hxy.
  - intros [y [x Hxy]]. exists x, y. exact Hxy.
Qed.

(** [no_exists P] is precisely [not (exists x, P x)]. *)
Definition no_exists {A : Type} (P : A -> Prop) : Prop :=
  ~ exists x, P x.

Definition nested_no_exists_xy {X Y : Type} (R : X -> Y -> Prop) : Prop :=
  no_exists (fun x => no_exists (fun y => R x y)).

Definition nested_no_exists_yx {X Y : Type} (R : X -> Y -> Prop) : Prop :=
  no_exists (fun y => no_exists (fun x => R x y)).

(** These names expose Rocq's standard [exists!] interpretation explicitly. *)
Definition nested_exists_unique_xy {X Y : Type}
    (R : X -> Y -> Prop) : Prop :=
  exists! x, exists! y, R x y.

Definition nested_exists_unique_yx {X Y : Type}
    (R : X -> Y -> Prop) : Prop :=
  exists! y, exists! x, R x y.

End QuantifierLaws.
