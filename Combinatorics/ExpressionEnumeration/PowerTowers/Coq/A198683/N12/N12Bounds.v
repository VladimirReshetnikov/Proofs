(*
  Coq port of the unconditional endgame bounds from
  PowerTowers/A198683/N12/N12Symbolic.lean.

  The Lean module certifies the numeric separation facts for the n = 12
  probe classes of A198683 through a long hand-propagated cascade of
  rational boxes.  The quantities involved are all real expressions
  built from exp / sin / cos of expressions rooted at pi, obtained by
  splitting the complex principal powers `i^z` into real and imaginary
  parts:

      i^z = exp(-(pi/2) * Im z) * (cos((pi/2) * Re z)
                                   + i sin((pi/2) * Re z)).

  Rocq's standard library has no complex numbers, so this port states
  every bound through the real/imaginary parts directly and certifies
  each box in one shot with the coq-interval `interval` tactic, which
  replaces the Lean file's ~1900-line rational-box propagation.

  Ported unconditional theorems (Lean name -> Coq name):
    rho_bounds                -> rho_bounds
    theta_box                 -> theta_box
    sin_cos_theta_bounds_of_endpoint_bounds (conclusion, made
                                unconditional) -> sin_cos_theta_bounds
    nearOne1404_norm_lt_one   -> nearOne1404_norm_lt_one
  plus the box cascade for the `idx = 25` near-one representative,
  culminating in `nearOne25_norm_gt_one` and the norm separation
  `nearOne1404_norm_lt_nearOne25_norm` that underlies the Lean
  distinctness theorem `nearOne25_ne_nearOne1404_of_endpoint_bounds`.
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Psatz.
From Interval Require Import Tactic.

Open Scope R_scope.

Module LeanProofs.
Module A198683N12Bounds.

(* ------------------------------------------------------------------ *)
(* Base constants.                                                     *)
(* ------------------------------------------------------------------ *)

(* rho = |i^i| = exp(-pi/2). *)
Definition rho : R := exp (- (PI / 2)).

(* theta = (pi/2) * rho, the angle of u = i^(i^i). *)
Definition theta : R := PI / 2 * rho.

(* sigma = exp((pi/2) * exp(pi/2)), the positive real value of the
   subtree (i^((i^i)^i))^(i^((i^i)^i)). *)
Definition sigma : R := exp (PI / 2 * exp (PI / 2)).

(* tau = exp(-(pi/2) * sigma), the tiny positive real value of the
   subtree (i^i)^nearProbeR. *)
Definition tau : R := exp (- (PI / 2) * sigma).

(* ‖nearOne1404‖ = ‖(i^i)^nearProbeS‖ = exp(-(pi/2) * tau). *)
Definition nearOne1404_norm : R := exp (- (PI / 2) * tau).

(* ------------------------------------------------------------------ *)
(* Real/imaginary parts of the idx = 25 tower layers.                  *)
(*                                                                     *)
(* v = i^(i^(i^i)); the seed is (i^((i^i)^i))^v = (-i)^v; the levels   *)
(* are successive principal powers i^(...) above the seed.             *)
(* ------------------------------------------------------------------ *)

Definition v_re : R :=
  exp (- (PI / 2) * sin theta) * cos (PI / 2 * cos theta).

Definition v_im : R :=
  exp (- (PI / 2) * sin theta) * sin (PI / 2 * cos theta).

Definition seed_re : R := exp (PI / 2 * v_im) * cos (PI / 2 * v_re).

Definition seed_im : R := - (exp (PI / 2 * v_im) * sin (PI / 2 * v_re)).

Definition level1_re : R :=
  exp (- (PI / 2) * seed_im) * cos (PI / 2 * seed_re).

Definition level1_im : R :=
  exp (- (PI / 2) * seed_im) * sin (PI / 2 * seed_re).

Definition level2_re : R :=
  exp (- (PI / 2) * level1_im) * cos (PI / 2 * level1_re).

Definition level2_im : R :=
  exp (- (PI / 2) * level1_im) * sin (PI / 2 * level1_re).

Definition level3_re : R :=
  exp (- (PI / 2) * level2_im) * cos (PI / 2 * level2_re).

Definition level3_im : R :=
  exp (- (PI / 2) * level2_im) * sin (PI / 2 * level2_re).

(* Imaginary part of nearOne25Base = i^level3. *)
Definition base_im : R :=
  exp (- (PI / 2) * level3_im) * sin (PI / 2 * level3_re).

(* ‖nearOne25‖ = ‖i^nearOne25Base‖ = exp(-(pi/2) * Im nearOne25Base). *)
Definition nearOne25_norm : R := exp (- (PI / 2) * base_im).

(* ------------------------------------------------------------------ *)
(* Certified boxes.                                                    *)
(* ------------------------------------------------------------------ *)

(* Lean: `rho_bounds`. *)
Theorem rho_bounds :
    207879576350 / 1000000000000 < rho /\
    rho < 207879576351 / 1000000000000.
Proof.
  unfold rho; split; interval with (i_prec 60).
Qed.

(* Lean: `theta_box`. *)
Theorem theta_box :
    326536474946 / 1000000000000 < theta /\
    theta < 326536474949 / 1000000000000.
Proof.
  unfold theta, rho; split; interval with (i_prec 60).
Qed.

(* Lean: the conclusion of `sin_cos_theta_bounds_of_endpoint_bounds`,
   here with the four endpoint estimates discharged. *)
Theorem sin_cos_theta_bounds :
    320764449975 / 1000000000000 < sin theta /\
    sin theta < 320764449985 / 1000000000000 /\
    947158998071 / 1000000000000 < cos theta /\
    cos theta < 947158998073 / 1000000000000.
Proof.
  unfold theta, rho; repeat split; interval with (i_prec 60).
Qed.

(* Lean: the `v` box fed to `nearOne25Seed_box_of_v_box_and_endpoint_bounds`. *)
Theorem v_box :
    50092236 / 1000000000 < v_re /\
    v_re < 50092237 / 1000000000 /\
    602116527 / 1000000000 < v_im /\
    v_im < 602116528 / 1000000000.
Proof.
  unfold v_re, v_im, theta, rho; repeat split; interval with (i_prec 60).
Qed.

(* Lean: the seed box certified by
   `nearOne25Seed_box_of_v_box_and_endpoint_bounds`. *)
Theorem nearOne25Seed_box :
    25669119 / 10000000 < seed_re /\
    seed_re < 320864 / 125000 /\
    - (404790 / 2000000) < seed_im /\
    seed_im < - (404789 / 2000000).
Proof.
  unfold seed_re, seed_im, v_re, v_im, theta, rho;
    repeat split; interval with (i_prec 60).
Qed.

(* Lean: the private level-3 real-part range
   (-766, -765) used by `nearOne25Base_im_neg_of_level3_re_bounds`. *)
Theorem level3_re_bounds : -766 < level3_re /\ level3_re < -765.
Proof.
  unfold level3_re, level2_re, level2_im, level1_re, level1_im,
    seed_re, seed_im, v_re, v_im, theta, rho;
    split; interval with (i_prec 80).
Qed.

(* Lean: `nearOne25Base_im_neg_of_level3_re_bounds`, made unconditional. *)
Theorem base_im_neg : base_im < 0.
Proof.
  unfold base_im, level3_re, level3_im, level2_re, level2_im,
    level1_re, level1_im, seed_re, seed_im, v_re, v_im, theta, rho.
  interval with (i_prec 80).
Qed.

(* ------------------------------------------------------------------ *)
(* Norm separation of the retained near-one representatives.           *)
(* ------------------------------------------------------------------ *)

Lemma tau_pos : 0 < tau.
Proof. apply exp_pos. Qed.

(* Lean: `nearOne1404_norm_lt_one`. *)
Theorem nearOne1404_norm_lt_one : nearOne1404_norm < 1.
Proof.
  unfold nearOne1404_norm.
  rewrite <- exp_0.
  apply exp_increasing.
  pose proof PI_RGT_0.
  pose proof tau_pos.
  nra.
Qed.

(* Lean: `nearOne25_norm_gt_one_of_base_im_neg`, made unconditional. *)
Theorem nearOne25_norm_gt_one : 1 < nearOne25_norm.
Proof.
  unfold nearOne25_norm.
  rewrite <- exp_0.
  apply exp_increasing.
  pose proof PI_RGT_0.
  pose proof base_im_neg.
  nra.
Qed.

(* The real content of the Lean distinctness theorem
   `nearOne25_ne_nearOne1404_of_endpoint_bounds`: the two retained
   near-one representatives have strictly separated moduli. *)
Theorem nearOne1404_norm_lt_nearOne25_norm :
    nearOne1404_norm < nearOne25_norm.
Proof.
  pose proof nearOne1404_norm_lt_one.
  pose proof nearOne25_norm_gt_one.
  lra.
Qed.

End A198683N12Bounds.
End LeanProofs.
