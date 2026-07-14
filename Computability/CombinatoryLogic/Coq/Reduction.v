(* ===================================================================== *)
(*  Reduction.v                                                         *)
(*                                                                       *)
(*  Small, theory-independent infrastructure for reflexive-transitive   *)
(*  closures.  The development deliberately keeps this relation local   *)
(*  rather than depending on a computability library.                    *)
(* ===================================================================== *)

Set Implicit Arguments.

Module Reduction.

Inductive star {A : Type} (step : A -> A -> Prop) : A -> A -> Prop :=
| star_refl : forall x, star step x x
| star_step : forall x y z, step x y -> star step y z -> star step x z.

Inductive plus {A : Type} (step : A -> A -> Prop) : A -> A -> Prop :=
| plus_step : forall x y z, step x y -> star step y z -> plus step x z.

Arguments star_refl {A step x}.
Arguments star_step {A step x y z} _ _.
Arguments plus_step {A step x y z} _ _.

Lemma star_one : forall (A : Type) (step : A -> A -> Prop) x y,
  step x y -> star step x y.
Proof.
  intros A step x y h.
  eapply star_step; [exact h | apply star_refl].
Qed.

Lemma star_trans : forall (A : Type) (step : A -> A -> Prop) x y z,
  star step x y -> star step y z -> star step x z.
Proof.
  intros A step x y z hxy.
  revert z.
  induction hxy as [x | x y middle hxy hymiddle IH]; intros z hyz.
  - exact hyz.
  - eapply star_step; [exact hxy | exact (IH z hyz)].
Qed.

Lemma star_map : forall (A B : Type)
    (stepA : A -> A -> Prop) (stepB : B -> B -> Prop)
    (f : A -> B),
  (forall x y, stepA x y -> stepB (f x) (f y)) ->
  forall x y, star stepA x y -> star stepB (f x) (f y).
Proof.
  intros A B stepA stepB f hmap x y hsteps.
  induction hsteps as [x | x y z hxy hyz IH].
  - apply star_refl.
  - eapply star_step.
    + exact (hmap x y hxy).
    + exact IH.
Qed.

Lemma plus_one : forall (A : Type) (step : A -> A -> Prop) x y,
  step x y -> plus step x y.
Proof.
  intros A step x y h.
  eapply plus_step; [exact h | apply star_refl].
Qed.

Lemma plus_to_star : forall (A : Type) (step : A -> A -> Prop) x y,
  plus step x y -> star step x y.
Proof.
  intros A step x y hplus.
  destruct hplus as [source middle target hstep hstar].
  eapply star_step.
  - exact hstep.
  - exact hstar.
Qed.

Lemma plus_star_trans : forall (A : Type) (step : A -> A -> Prop) x y z,
  plus step x y -> star step y z -> plus step x z.
Proof.
  intros A step x y z hplus hyz.
  destruct hplus as [source middle target hstep hstar].
  eapply plus_step.
  - exact hstep.
  - eapply star_trans.
    + exact hstar.
    + exact hyz.
Qed.

Lemma plus_map : forall (A B : Type)
    (stepA : A -> A -> Prop) (stepB : B -> B -> Prop)
    (f : A -> B),
  (forall x y, stepA x y -> stepB (f x) (f y)) ->
  forall x y, plus stepA x y -> plus stepB (f x) (f y).
Proof.
  intros A B stepA stepB f hmap x y hplus.
  destruct hplus as [source middle target hstep hstar].
  eapply plus_step.
  - exact (hmap source middle hstep).
  - exact (@star_map A B stepA stepB f hmap middle target hstar).
Qed.

End Reduction.
