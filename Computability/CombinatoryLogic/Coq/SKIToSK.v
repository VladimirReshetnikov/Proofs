(* ===================================================================== *)
(*  SKIToSK.v                                                           *)
(*                                                                       *)
(*  Operational translations between SKI and its S-K subcalculus.        *)
(*  Eliminating I by I = S K K is semantics preserving, but the obvious  *)
(*  homomorphic compiler is intentionally not called injective: the SKI   *)
(*  primitive I and the SKI source tree S K K have identical images.      *)
(*  Conversely, the structural inclusion SK -> SKI is injective.          *)
(* ===================================================================== *)

From Stdlib Require Import Lia.
From CombinatoryLogic Require Import Reduction SKI SK.

Set Implicit Arguments.

Module SKIToSK.

Fixpoint compile (source : SKI.term) : SK.term :=
  match source with
  | SKI.ident => SK.ident
  | SKI.konst => SK.konst
  | SKI.scomb => SK.scomb
  | SKI.app lhs rhs => SK.app (compile lhs) (compile rhs)
  end.

Theorem compile_step_positive : forall source target,
  SKI.step source target -> SK.progresses (compile source) (compile target).
Proof.
  intros source target hstep.
  induction hstep as
    [x | x y | x y z | x x' y hxx' IH | x y y' hyy' IH].
  - cbn [compile].
    apply SK.ident_correct_positive.
  - unfold SK.progresses.
    apply Reduction.plus_one.
    apply SK.step_konst.
  - unfold SK.progresses.
    apply Reduction.plus_one.
    apply SK.step_scomb.
  - cbn [compile].
    now apply SK.progresses_app_left.
  - cbn [compile].
    now apply SK.progresses_app_right.
Qed.

Theorem compile_step : forall source target,
  SKI.step source target -> SK.reaches (compile source) (compile target).
Proof.
  intros source target hstep.
  apply Reduction.plus_to_star.
  exact (compile_step_positive hstep).
Qed.

Theorem compile_steps : forall source target,
  SKI.reaches source target -> SK.reaches (compile source) (compile target).
Proof.
  intros source target hsteps.
  induction hsteps as [source | source middle target hstep hsteps IH].
  - apply SK.reaches_refl.
  - eapply SK.reaches_trans.
    + exact (compile_step hstep).
    + exact IH.
Qed.

Theorem compile_progresses : forall source target,
  SKI.progresses source target ->
  SK.progresses (compile source) (compile target).
Proof.
  intros source target hprogress.
  destruct hprogress as [source middle target hstep hsteps].
  unfold SK.progresses, SK.reaches in *.
  eapply Reduction.plus_star_trans.
  - exact (compile_step_positive hstep).
  - exact (compile_steps hsteps).
Qed.

Theorem compile_size_linear : forall source,
  SK.size (compile source) <= 5 * SKI.size source.
Proof.
  induction source as [| | |lhs IHlhs rhs IHrhs]; cbn [compile SKI.size SK.size].
  - reflexivity.
  - lia.
  - lia.
  - lia.
Qed.

Definition identExpansion : SKI.term :=
  SKI.app (SKI.app SKI.scomb SKI.konst) SKI.konst.

Theorem compile_ident_collision :
  compile SKI.ident = compile identExpansion.
Proof. reflexivity. Qed.

Theorem ident_ne_identExpansion : SKI.ident <> identExpansion.
Proof. discriminate. Qed.

Theorem compile_not_injective :
  ~ (forall x y, compile x = compile y -> x = y).
Proof.
  intro hinjective.
  apply ident_ne_identExpansion.
  apply hinjective.
  exact compile_ident_collision.
Qed.

Fixpoint include (source : SK.term) : SKI.term :=
  match source with
  | SK.konst => SKI.konst
  | SK.scomb => SKI.scomb
  | SK.app lhs rhs => SKI.app (include lhs) (include rhs)
  end.

Theorem include_injective : forall x y,
  include x = include y -> x = y.
Proof.
  induction x as [| |xl IHxl xr IHxr]; intros y heq;
    destruct y as [| |yl yr]; cbn [include] in heq;
    try reflexivity; try discriminate.
  injection heq as hleft hright.
  f_equal.
  - now apply IHxl.
  - now apply IHxr.
Qed.

Theorem include_step_positive : forall source target,
  SK.step source target ->
  SKI.progresses (include source) (include target).
Proof.
  intros source target hstep.
  induction hstep as
    [x y | x y z | x x' y hxx' IH | x y y' hyy' IH].
  - unfold SKI.progresses.
    apply Reduction.plus_one.
    apply SKI.step_konst.
  - unfold SKI.progresses.
    apply Reduction.plus_one.
    apply SKI.step_scomb.
  - cbn [include].
    now apply SKI.progresses_app_left.
  - cbn [include].
    now apply SKI.progresses_app_right.
Qed.

Theorem include_step : forall source target,
  SK.step source target -> SKI.reaches (include source) (include target).
Proof.
  intros source target hstep.
  apply Reduction.plus_to_star.
  exact (include_step_positive hstep).
Qed.

Theorem include_steps : forall source target,
  SK.reaches source target -> SKI.reaches (include source) (include target).
Proof.
  intros source target hsteps.
  induction hsteps as [source | source middle target hstep hsteps IH].
  - apply SKI.reaches_refl.
  - eapply SKI.reaches_trans.
    + exact (include_step hstep).
    + exact IH.
Qed.

Theorem include_progresses : forall source target,
  SK.progresses source target ->
  SKI.progresses (include source) (include target).
Proof.
  intros source target hprogress.
  destruct hprogress as [source middle target hstep hsteps].
  unfold SKI.progresses, SKI.reaches in *.
  eapply Reduction.plus_star_trans.
  - exact (include_step_positive hstep).
  - exact (include_steps hsteps).
Qed.

Theorem include_size : forall source,
  SKI.size (include source) = SK.size source.
Proof.
  induction source as [| |lhs IHlhs rhs IHrhs]; cbn [include SKI.size SK.size].
  - reflexivity.
  - reflexivity.
  - now rewrite IHlhs, IHrhs.
Qed.

(* [include] is a genuine section of I-elimination on pure SK terms. *)
Theorem compile_include : forall source,
  compile (include source) = source.
Proof.
  induction source as [| |lhs IHlhs rhs IHrhs]; cbn [compile include].
  - reflexivity.
  - reflexivity.
  - now rewrite IHlhs, IHrhs.
Qed.

Theorem compile_ski_omega : compile SKI.omega = SK.omega.
Proof. reflexivity. Qed.

Theorem compiled_ski_omega_positive_cycle :
  SK.progresses (compile SKI.omega) (compile SKI.omega).
Proof.
  apply compile_progresses.
  apply SKI.omega_positive_cycle.
Qed.

Theorem included_sk_omega_positive_cycle :
  SKI.progresses (include SK.omega) (include SK.omega).
Proof.
  apply include_progresses.
  apply SK.omega_positive_cycle.
Qed.

End SKIToSK.
