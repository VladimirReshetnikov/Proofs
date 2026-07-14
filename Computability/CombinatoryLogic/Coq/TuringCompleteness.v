(* ===================================================================== *)
(*  TuringCompleteness.v                                                *)
(*                                                                       *)
(*  This file proves a faithful, injective embedding of SKI into Iota.     *)
(*  The separate [LambdaToSK] module supplies the project's conventional   *)
(*  Turing-completeness boundary by compiling weak untyped lambda terms.   *)
(*                                                                       *)
(*  The compiler is Barker's mapping:                                    *)
(*                                                                       *)
(*      I   |--> iota iota                                               *)
(*      K   |--> iota (iota (iota iota))                                 *)
(*      S   |--> iota (iota (iota (iota iota)))                          *)
(*      p q |--> compile p (compile q).                                  *)
(* ===================================================================== *)

From Stdlib Require Import Lia.
From CombinatoryLogic Require Import Reduction SKI Iota.

Set Implicit Arguments.

Module IotaTuringCompleteness.

Fixpoint compile (source : SKI.term) : Iota.term :=
  match source with
  | SKI.ident => Iota.identCode
  | SKI.konst => Iota.konstCode
  | SKI.scomb => Iota.scombCode
  | SKI.app lhs rhs => Iota.app (compile lhs) (compile rhs)
  end.

(* Every compiled source term is an application.  This distinguishes an   *)
(* encoded source subtree from the bare-Iota left child that tags each of  *)
(* the three encoded primitive combinators.                                *)
Lemma compile_not_iota : forall source, compile source <> Iota.iota.
Proof.
  intros [| | |lhs rhs]; discriminate.
Qed.

Lemma compile_app_ne_root_iota : forall lhs rhs tail,
  compile (SKI.app lhs rhs) <> Iota.app Iota.iota tail.
Proof.
  intros lhs rhs tail heq.
  cbn [compile] in heq.
  injection heq as hleft _.
  exact (compile_not_iota lhs hleft).
Qed.

Theorem compile_injective : forall x y,
  compile x = compile y -> x = y.
Proof.
  induction x as [| | |xl IHxl xr IHxr]; intros y heq;
    destruct y as [| | |yl yr]; cbn [compile] in heq;
    try reflexivity; try discriminate.
  - exfalso.
    apply (compile_app_ne_root_iota
      (lhs := yl) (rhs := yr) (tail := Iota.iota)).
    symmetry. exact heq.
  - exfalso.
    apply (compile_app_ne_root_iota
      (lhs := yl) (rhs := yr)
      (tail := Iota.app Iota.iota Iota.identCode)).
    symmetry. exact heq.
  - exfalso.
    apply (compile_app_ne_root_iota
      (lhs := yl) (rhs := yr)
      (tail := Iota.app Iota.iota (Iota.app Iota.iota Iota.identCode))).
    symmetry. exact heq.
  - exfalso.
    apply (compile_app_ne_root_iota
      (lhs := xl) (rhs := xr) (tail := Iota.iota)).
    exact heq.
  - exfalso.
    apply (compile_app_ne_root_iota
      (lhs := xl) (rhs := xr)
      (tail := Iota.app Iota.iota Iota.identCode)).
    exact heq.
  - exfalso.
    apply (compile_app_ne_root_iota
      (lhs := xl) (rhs := xr)
      (tail := Iota.app Iota.iota (Iota.app Iota.iota Iota.identCode))).
    exact heq.
  - injection heq as hleft hright.
    f_equal.
    + now apply IHxl.
    + now apply IHxr.
Qed.

Theorem compile_runtime_pure : forall source,
  IotaRuntime.pure (Iota.embed (compile source)).
Proof.
  intro source.
  apply Iota.embed_pure.
Qed.

Lemma identCode_size : Iota.size Iota.identCode = 3.
Proof. reflexivity. Qed.

Lemma konstCode_size : Iota.size Iota.konstCode = 7.
Proof. reflexivity. Qed.

Lemma scombCode_size : Iota.size Iota.scombCode = 9.
Proof. reflexivity. Qed.

Theorem compile_size_linear : forall source,
  Iota.size (compile source) <= 9 * SKI.size source.
Proof.
  induction source as [| | |lhs IHlhs rhs IHrhs];
    cbn [compile SKI.size].
  - rewrite identCode_size. lia.
  - rewrite konstCode_size. lia.
  - rewrite scombCode_size. lia.
  - change (1 + Iota.size (compile lhs) + Iota.size (compile rhs) <=
      9 * (1 + SKI.size lhs + SKI.size rhs)).
    lia.
Qed.

(* A single SKI contraction, including contractions below an application,  *)
(* is simulated by a finite Iota-runtime derivation whose endpoints remain *)
(* pure Iota programs.                                                     *)
Theorem compile_step : forall source target,
  SKI.step source target -> Iota.reaches (compile source) (compile target).
Proof.
  intros source target hstep.
  induction hstep as
    [x | x y | x y z | x x' y hxx' IH | x y y' hyy' IH].
  - change (IotaRuntime.reaches
      (IotaRuntime.app (Iota.embed Iota.identCode) (Iota.embed (compile x)))
      (Iota.embed (compile x))).
    apply Iota.identCode_correct.
  - change (IotaRuntime.reaches
      (IotaRuntime.app
        (IotaRuntime.app (Iota.embed Iota.konstCode) (Iota.embed (compile x)))
        (Iota.embed (compile y)))
      (Iota.embed (compile x))).
    apply Iota.konstCode_correct.
  - change (IotaRuntime.reaches
      (IotaRuntime.app
        (IotaRuntime.app
          (IotaRuntime.app (Iota.embed Iota.scombCode)
            (Iota.embed (compile x)))
          (Iota.embed (compile y)))
        (Iota.embed (compile z)))
      (IotaRuntime.app
        (IotaRuntime.app (Iota.embed (compile x)) (Iota.embed (compile z)))
        (IotaRuntime.app (Iota.embed (compile y)) (Iota.embed (compile z))))).
    apply Iota.scombCode_correct.
  - unfold Iota.reaches in *.
    cbn [compile Iota.embed].
    now apply IotaRuntime.reaches_app_left.
  - unfold Iota.reaches in *.
    cbn [compile Iota.embed].
    now apply IotaRuntime.reaches_app_right.
Qed.

(* Stronger non-vacuity form: one source contraction is implemented by at  *)
(* least one runtime contraction, rather than merely by a reflexive closure. *)
Theorem compile_step_positive : forall source target,
  SKI.step source target ->
  Iota.progresses (compile source) (compile target).
Proof.
  intros source target hstep.
  induction hstep as
    [x | x y | x y z | x x' y hxx' IH | x y y' hyy' IH].
  - change (IotaRuntime.progresses
      (IotaRuntime.app (Iota.embed Iota.identCode) (Iota.embed (compile x)))
      (Iota.embed (compile x))).
    apply Iota.identCode_correct_positive.
  - change (IotaRuntime.progresses
      (IotaRuntime.app
        (IotaRuntime.app (Iota.embed Iota.konstCode) (Iota.embed (compile x)))
        (Iota.embed (compile y)))
      (Iota.embed (compile x))).
    apply Iota.konstCode_correct_positive.
  - change (IotaRuntime.progresses
      (IotaRuntime.app
        (IotaRuntime.app
          (IotaRuntime.app (Iota.embed Iota.scombCode)
            (Iota.embed (compile x)))
          (Iota.embed (compile y)))
        (Iota.embed (compile z)))
      (IotaRuntime.app
        (IotaRuntime.app (Iota.embed (compile x)) (Iota.embed (compile z)))
        (IotaRuntime.app (Iota.embed (compile y)) (Iota.embed (compile z))))).
    apply Iota.scombCode_correct_positive.
  - unfold Iota.progresses in *.
    cbn [compile Iota.embed].
    now apply IotaRuntime.progresses_app_left.
  - unfold Iota.progresses in *.
    cbn [compile Iota.embed].
    now apply IotaRuntime.progresses_app_right.
Qed.

Theorem compile_steps : forall source target,
  SKI.reaches source target -> Iota.reaches (compile source) (compile target).
Proof.
  intros source target hsteps.
  induction hsteps as [source | source middle target hstep hsteps IH].
  - apply Iota.reaches_refl.
  - eapply Iota.reaches_trans.
    + exact (compile_step hstep).
    + exact IH.
Qed.

Theorem compile_progresses : forall source target,
  SKI.progresses source target ->
  Iota.progresses (compile source) (compile target).
Proof.
  intros source target hprogress.
  destruct hprogress as [source middle target hstep hsteps].
  unfold Iota.progresses, Iota.reaches in *.
  eapply Reduction.plus_star_trans.
  - exact (compile_step_positive hstep).
  - exact (compile_steps hsteps).
Qed.

Theorem compiled_omega_positive_cycle :
  Iota.progresses (compile SKI.omega) (compile SKI.omega).
Proof.
  apply compile_progresses.
  apply SKI.omega_positive_cycle.
Qed.

Definition FaithfulSKIEmbedding {A : Type}
    (target_reaches : A -> A -> Prop) (encode : SKI.term -> A) : Prop :=
  (forall x y, encode x = encode y -> x = y) /\
  (forall source target,
    SKI.reaches source target -> target_reaches (encode source) (encode target)).

Definition SKIEmbeddable (A : Type)
    (target_reaches : A -> A -> Prop) : Prop :=
  exists encode : SKI.term -> A,
    FaithfulSKIEmbedding target_reaches encode.

Arguments SKIEmbeddable A target_reaches : clear implicits.

Theorem iota_faithfully_embeds_ski :
  FaithfulSKIEmbedding Iota.reaches compile.
Proof.
  split.
  - exact compile_injective.
  - exact compile_steps.
Qed.

Theorem faithful_ski_embedding :
  SKIEmbeddable Iota.term Iota.reaches.
Proof.
  exists compile.
  exact iota_faithfully_embeds_ski.
Qed.

End IotaTuringCompleteness.
