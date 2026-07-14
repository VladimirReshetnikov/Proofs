(*
  Coq port of the final certification layer from
  the Lean module ExponentialIdentities.TinyExponentTower.

  The Lean module proves the hard analytic estimates on logarithms and
  exponentials, then finishes by converting two tiny exponential-increment
  bounds into the stated floor identity.  This Coq port proves that final
  conversion generically, and specializes it to the concrete tower.  The
  conditional layer keeps the analytic input bounds as explicit
  hypotheses; the unconditional layer at the end of the file discharges
  them with the coq-interval `interval` tactic and the same first-order
  remainder analysis as the Lean original, yielding the unconditional
  theorems `floor_tinyExponentTower_sub` and
  `floor_expanded_tinyExponentTower_sub`.
*)

From Stdlib Require Import Reals.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Psatz Field.
From Interval Require Import Tactic.

Open Scope R_scope.

Module LeanProofs.
Module TinyExponentTower.

Section GenericTower.

Variable k : Z.

Definition L : R := ln 10.

Definition towerBase : R := Rpower 10 (IZR k).

Definition towerBaseInt : Z := (10 ^ k)%Z.

Definition t : R := / towerBase.

Definition bottom : R := Rpower 10 (- IZR k).

Definition u : R := Rpower 10 t.

Definition v : R := Rpower 10 u.

Definition c : R := Rpower 10 v.

Definition tinyExponentTowerAt : R := Rpower 10 c.

Definition expandedTinyExponentTowerAt : R :=
  Rpower 10 (Rpower 10 (Rpower 10 (Rpower 10 bottom))).

Definition x : R := L * (c - IZR k).

Lemma IZR_pow10_Rpower (hk : (0 <= k)%Z) :
    IZR towerBaseInt = towerBase.
Proof.
  unfold towerBaseInt, towerBase.
  replace k with (Z.of_nat (Z.to_nat k)) by (apply Z2Nat.id; exact hk).
  rewrite <- pow_IZR.
  rewrite <- INR_IZR_INZ.
  rewrite Rpower_pow by lra.
  reflexivity.
Qed.

Lemma towerBase_pos : 0 < towerBase.
Proof.
  unfold towerBase, Rpower.
  apply exp_pos.
Qed.

Lemma towerBase_mul_t : towerBase * t = 1.
Proof.
  unfold t.
  field.
  exact (Rgt_not_eq towerBase 0 towerBase_pos).
Qed.

Lemma bottom_eq_t : bottom = t.
Proof.
  unfold bottom, t, towerBase.
  rewrite Rpower_Ropp.
  reflexivity.
Qed.

Lemma expandedTinyExponentTowerAt_eq :
    expandedTinyExponentTowerAt = tinyExponentTowerAt.
Proof.
  unfold expandedTinyExponentTowerAt, tinyExponentTowerAt, c, v, u.
  rewrite bottom_eq_t.
  reflexivity.
Qed.

Lemma tinyExponentTowerAt_eq_base_mul_exp :
    tinyExponentTowerAt = towerBase * exp x.
Proof.
  unfold tinyExponentTowerAt, x, L.
  replace c with (IZR k + (c - IZR k)) by ring.
  rewrite Rpower_plus.
  fold towerBase.
  unfold Rpower.
  replace (ln 10 * (IZR k + (c - IZR k) - IZR k))
    with ((c - IZR k) * ln 10) by ring.
  reflexivity.
Qed.

Theorem floor_from_exp_bounds (m : Z)
    (hk : (0 <= k)%Z)
    (hexp_lower : 1 + IZR m * t <= exp x)
    (hexp_upper : exp x < 1 + (IZR m + 1) * t) :
    Zfloor tinyExponentTowerAt = (towerBaseInt + m)%Z.
Proof.
  apply Zfloor_eq.
  rewrite tinyExponentTowerAt_eq_base_mul_exp.
  split.
  - rewrite plus_IZR, IZR_pow10_Rpower by exact hk.
    replace (towerBase + IZR m) with (towerBase * (1 + IZR m * t)).
    + apply Rmult_le_compat_l.
      * left. exact towerBase_pos.
      * exact hexp_lower.
    + rewrite Rmult_plus_distr_l, Rmult_1_r.
      replace (towerBase * (IZR m * t)) with (IZR m * (towerBase * t)) by ring.
      rewrite towerBase_mul_t.
      ring.
  - rewrite plus_IZR, IZR_pow10_Rpower by exact hk.
    replace (towerBase + IZR m + 1) with
      (towerBase * (1 + (IZR m + 1) * t)).
    + apply Rmult_lt_compat_l.
      * exact towerBase_pos.
      * exact hexp_upper.
    + rewrite Rmult_plus_distr_l, Rmult_1_r.
      replace (towerBase * ((IZR m + 1) * t)) with
        ((IZR m + 1) * (towerBase * t)) by ring.
      rewrite towerBase_mul_t.
      ring.
Qed.

Theorem floor_from_log_bounds (m : Z)
    (hk : (0 <= k)%Z)
    (hlog_lower : IZR m * t <= x)
    (hlog_quad_upper : x + x ^ 2 < (IZR m + 1) * t)
    (hexp_quad_upper : exp x <= 1 + x + x ^ 2) :
    Zfloor tinyExponentTowerAt = (towerBaseInt + m)%Z.
Proof.
  apply floor_from_exp_bounds.
  - exact hk.
  - pose proof (exp_ineq1_le x).
    nra.
  - nra.
Qed.

Theorem floor_from_log_remainder_bounds (m : Z)
    (hk : (0 <= k)%Z)
    (hlog_lower : IZR m * t <= x)
    (hlog_quad_upper : x + x ^ 2 < (IZR m + 1) * t)
    (hexp_remainder_upper : exp x - 1 - x <= x ^ 2) :
    Zfloor tinyExponentTowerAt = (towerBaseInt + m)%Z.
Proof.
  apply floor_from_log_bounds.
  - exact hk.
  - exact hlog_lower.
  - exact hlog_quad_upper.
  - nra.
Qed.

Theorem floor_sub_from_exp_bounds (m : Z)
    (hk : (0 <= k)%Z)
    (hexp_lower : 1 + IZR m * t <= exp x)
    (hexp_upper : exp x < 1 + (IZR m + 1) * t) :
    (Zfloor tinyExponentTowerAt - towerBaseInt = m)%Z.
Proof.
  rewrite (floor_from_exp_bounds m hk hexp_lower hexp_upper).
  ring.
Qed.

Theorem floor_sub_from_log_remainder_bounds (m : Z)
    (hk : (0 <= k)%Z)
    (hlog_lower : IZR m * t <= x)
    (hlog_quad_upper : x + x ^ 2 < (IZR m + 1) * t)
    (hexp_remainder_upper : exp x - 1 - x <= x ^ 2) :
    (Zfloor tinyExponentTowerAt - towerBaseInt = m)%Z.
Proof.
  rewrite (floor_from_log_remainder_bounds
    m hk hlog_lower hlog_quad_upper hexp_remainder_upper).
  ring.
Qed.

End GenericTower.

Definition N : Z := 10000000000%Z.

Definition M : Z := 2811012357389%Z.

Definition tinyExponentTower : R := tinyExponentTowerAt N.

Definition expandedTinyExponentTower : R := expandedTinyExponentTowerAt N.

Theorem floor_tinyExponentTower_from_exp_bounds
    (hexp_lower : 1 + IZR M * t N <= exp (x N))
    (hexp_upper : exp (x N) < 1 + (IZR M + 1) * t N) :
    Zfloor tinyExponentTower = (towerBaseInt N + M)%Z.
Proof.
  unfold tinyExponentTower.
  apply floor_from_exp_bounds; try assumption.
  unfold N. lia.
Qed.

Theorem floor_tinyExponentTower_sub_from_exp_bounds
    (hexp_lower : 1 + IZR M * t N <= exp (x N))
    (hexp_upper : exp (x N) < 1 + (IZR M + 1) * t N) :
    (Zfloor tinyExponentTower - towerBaseInt N = M)%Z.
Proof.
  apply floor_sub_from_exp_bounds; try assumption.
  unfold N. lia.
Qed.

Theorem floor_tinyExponentTower_sub_from_log_remainder_bounds
    (hlog_lower : IZR M * t N <= x N)
    (hlog_quad_upper : x N + x N ^ 2 < (IZR M + 1) * t N)
    (hexp_remainder_upper : exp (x N) - 1 - x N <= x N ^ 2) :
    (Zfloor tinyExponentTower - towerBaseInt N = M)%Z.
Proof.
  apply floor_sub_from_log_remainder_bounds; try assumption.
  unfold N. lia.
Qed.

Theorem floor_expanded_tinyExponentTower_sub_from_log_remainder_bounds
    (hlog_lower : IZR M * t N <= x N)
    (hlog_quad_upper : x N + x N ^ 2 < (IZR M + 1) * t N)
    (hexp_remainder_upper : exp (x N) - 1 - x N <= x N ^ 2) :
    (Zfloor expandedTinyExponentTower - towerBaseInt N = M)%Z.
Proof.
  unfold expandedTinyExponentTower.
  rewrite expandedTinyExponentTowerAt_eq.
  apply floor_sub_from_log_remainder_bounds; try assumption.
  unfold N. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Unconditional layer.                                                *)
(*                                                                     *)
(* The analytic hypotheses of the conditional theorems above are now   *)
(* discharged, mirroring the interval-bound section of                 *)
(* ExponentialIdentities.TinyExponentTower.  The hard numerical inputs *)
(* are a twenty-digit enclosure of 10^11 * (ln 10)^4 and the tininess  *)
(* t = 10^(-10^10)) are certified by the coq-interval `interval`       *)
(* tactic; the remainder analysis for the three stacked exponentials   *)
(* is the same first-order expansion as in the Lean original.          *)
(* ------------------------------------------------------------------ *)

(* Uniform quadratic remainder bound for exp on [0, 1].  The interval
   tactic cannot prove it directly (the bound touches at 0), so we use
   exp (y/2) <= /(1 - y/2) on [0, 1/4] and interval arithmetic with
   bisection on [1/4, 1]. *)
Lemma exp_quad_remainder_upper :
    forall y, 0 <= y <= 1 -> exp y - 1 - y <= y ^ 2.
Proof.
  intros y [h0 h1].
  destruct (Rle_lt_dec y (1/4)) as [hsmall | hbig].
  - assert (hhalf_pos : 0 < 1 - y / 2) by lra.
    assert (hexp_pos : 0 < exp (y / 2)) by apply exp_pos.
    assert (hlow : 1 - y / 2 <= exp (- (y / 2))).
    { pose proof (exp_ineq1_le (- (y / 2))). lra. }
    assert (hmul : exp (y / 2) * exp (- (y / 2)) = 1).
    { rewrite <- exp_plus. replace (y / 2 + - (y / 2)) with 0 by ring.
      apply exp_0. }
    assert (hprod : exp (y / 2) * (1 - y / 2) <= 1) by nra.
    assert (hp0 : 0 <= exp (y / 2) * (1 - y / 2)) by nra.
    assert (hA : (exp (y / 2) * (1 - y / 2)) * (exp (y / 2) * (1 - y / 2)) <= 1)
      by nra.
    assert (hq : 0 <= 1 - 3 * y + y ^ 2) by nra.
    assert (hB : 1 <= (1 + y + y ^ 2) * ((1 - y / 2) * (1 - y / 2))) by nra.
    assert (hfin : exp (y / 2) * exp (y / 2) <= 1 + y + y ^ 2).
    { apply (Rmult_le_reg_r ((1 - y / 2) * (1 - y / 2))); nra. }
    assert (hy_eq : exp y = exp (y / 2) * exp (y / 2)).
    { rewrite <- exp_plus. f_equal. field. }
    rewrite hy_eq. lra.
  - assert (hgoal : exp y - 1 - y - y ^ 2 <= 0).
    { interval with (i_bisect y, i_taylor y, i_prec 40). }
    lra.
Qed.

Lemma L_lo : 0 <= L.
Proof. unfold L. interval. Qed.

Lemma L_hi : L <= 3.
Proof. unfold L. interval. Qed.

(* The sharp enclosure of the first-derivative term 10^11 * (ln 10)^4,
   the Coq counterpart of `main_derivative_bounds` in the Lean file. *)
Lemma main_term_bounds :
    2811012357389 + 2/5 < 100000000000 * L ^ 4 < 2811012357389 + 1/2.
Proof. unfold L; split; interval with (i_prec 90). Qed.

Lemma t_N_pos : 0 < t N.
Proof.
  unfold t. apply Rinv_0_lt_compat. apply towerBase_pos.
Qed.

Lemma t_N_small : t N <= 1 / 1000000000000000000000000000000.
Proof.
  unfold t, towerBase, N. interval with (i_prec 40).
Qed.

(* The full first-order expansion of the tower increment: the Coq
   counterpart of `log_increment_bounds` in the Lean file, plus the
   crude 0 <= x <= 1 range needed for the exponential remainder. *)
Lemma x_N_estimates :
    IZR M * t N <= x N /\
    x N + x N ^ 2 < (IZR M + 1) * t N /\
    0 <= x N <= 1.
Proof.
  set (tau := t N).
  set (r1 := exp (L * tau) - 1 - L * tau).
  set (r2 := exp (L * (u N - 1)) - 1 - L * (u N - 1)).
  set (r3 := exp (L * (v N - 10)) - 1 - L * (v N - 10)).
  assert (htau0 : 0 < tau) by apply t_N_pos.
  assert (htauS : tau <= 1 / 1000000000000000000000000000000)
    by apply t_N_small.
  assert (hL0 : 0 <= L) by apply L_lo.
  assert (hL3 : L <= 3) by apply L_hi.
  destruct main_term_bounds as [hmain_lo4 hmain_hi4].
  (* Structural equalities for the three stacked exponentials. *)
  assert (hu_eq : u N = 1 + L * tau + r1).
  { unfold u, Rpower.
    rewrite (Rmult_comm (t N) (ln 10)).
    fold L. fold tau.
    unfold r1. ring. }
  assert (hv_eq : v N = 10 * (1 + L * (u N - 1) + r2)).
  { unfold v, Rpower.
    replace (u N * ln 10) with (ln 10 + ln 10 * (u N - 1)) by ring.
    rewrite exp_plus.
    rewrite exp_ln by lra.
    fold L. unfold r2. ring. }
  assert (hbase : exp (10 * ln 10) = 10000000000).
  { assert (hln : ln (10 ^ 10) = 10 * ln 10).
    { rewrite ln_pow by lra. replace (INR 10) with 10 by (simpl; lra).
      reflexivity. }
    rewrite <- hln. rewrite exp_ln; [| apply pow_lt; lra].
    rewrite pow_IZR. reflexivity. }
  assert (hc_eq : c N = 10000000000 * (1 + L * (v N - 10) + r3)).
  { unfold c, Rpower.
    replace (v N * ln 10) with (10 * ln 10 + ln 10 * (v N - 10)) by ring.
    rewrite exp_plus, hbase.
    fold L. unfold r3. ring. }
  assert (hNlit : IZR N = 10000000000) by reflexivity.
  assert (hu_subeq : u N - 1 = L * tau + r1) by lra.
  assert (hv_subeq : v N - 10 = 10 * (L * (u N - 1) + r2)) by lra.
  assert (hx_eq : x N = 100000000000 * L ^ 4 * tau
      + 100000000000 * L ^ 3 * r1 + 100000000000 * L ^ 2 * r2
      + 10000000000 * L * r3).
  { unfold x. fold tau.
    rewrite hNlit, hc_eq, hv_subeq, hu_subeq. ring. }
  (* Smallness bookkeeping.  Each arithmetic step clears the context
     down to the exact hypotheses it needs, so that nra's product
     search stays small. *)
  assert (ht2_0 : 0 <= tau ^ 2) by (clear - htau0; nra).
  assert (htau2_le : tau ^ 2 <= 1 / 1000000000000000000000000000000 * tau)
    by (clear - htau0 htauS; nra).
  assert (hL2 : L ^ 2 <= 9) by (clear - hL0 hL3; nra).
  assert (hL3p : L ^ 3 <= 27) by (clear - hL0 hL3; nra).
  assert (hL2_0 : 0 <= L ^ 2) by (apply pow_le; lra).
  assert (hL3p_0 : 0 <= L ^ 3) by (apply pow_le; lra).
  (* First exponential. *)
  assert (hLt0 : 0 <= L * tau) by (clear - hL0 htau0; nra).
  assert (hLt1 : L * tau <= 1) by (clear - hL0 hL3 htau0 htauS; nra).
  assert (hr1_0 : 0 <= r1).
  { unfold r1. pose proof (exp_ineq1_le (L * tau)). lra. }
  assert (hr1_sq : r1 <= (L * tau) ^ 2).
  { unfold r1. apply exp_quad_remainder_upper. split; assumption. }
  assert (hr1_9t2 : r1 <= 9 * tau ^ 2)
    by (clear - hr1_sq hL0 hL2 ht2_0; nra).
  assert (hr1_t : r1 <= tau) by (clear - hr1_9t2 htau0 htauS; nra).
  (* Second exponential. *)
  assert (hu1_0 : 0 <= u N - 1) by (clear - hu_eq hLt0 hr1_0; lra).
  assert (hu1_le : u N - 1 <= 4 * tau)
    by (clear - hu_eq hL0 hL3 htau0 hr1_t; nra).
  assert (hx2_0 : 0 <= L * (u N - 1)) by (clear - hL0 hu1_0; nra).
  assert (hx2_le : L * (u N - 1) <= 12 * tau)
    by (clear - hL0 hL3 hu1_0 hu1_le; nra).
  assert (hx2_1 : L * (u N - 1) <= 1)
    by (clear - hx2_le htau0 htauS; lra).
  assert (hr2_0 : 0 <= r2).
  { unfold r2. pose proof (exp_ineq1_le (L * (u N - 1))). lra. }
  assert (hr2_sq : r2 <= (L * (u N - 1)) ^ 2).
  { unfold r2. apply exp_quad_remainder_upper. split; assumption. }
  assert (haux2 : 0 <= 12 * tau + L * (u N - 1))
    by (clear - htau0 hx2_0; lra).
  assert (hr2_144 : r2 <= 144 * tau ^ 2)
    by (clear - hr2_sq hx2_le haux2; nra).
  assert (hr2_8t : r2 <= 8 * tau)
    by (clear - hr2_144 htau0 htauS; nra).
  (* Third exponential. *)
  assert (hv10_0 : 0 <= v N - 10) by (clear - hv_eq hx2_0 hr2_0; lra).
  assert (hv10_le : v N - 10 <= 200 * tau)
    by (clear - hv_eq hx2_le hr2_8t; lra).
  assert (hx3_0 : 0 <= L * (v N - 10)) by (clear - hL0 hv10_0; nra).
  assert (hx3_le : L * (v N - 10) <= 600 * tau)
    by (clear - hL0 hL3 hv10_0 hv10_le; nra).
  assert (hx3_1 : L * (v N - 10) <= 1)
    by (clear - hx3_le htau0 htauS; lra).
  assert (hr3_0 : 0 <= r3).
  { unfold r3. pose proof (exp_ineq1_le (L * (v N - 10))). lra. }
  assert (hr3_sq : r3 <= (L * (v N - 10)) ^ 2).
  { unfold r3. apply exp_quad_remainder_upper. split; assumption. }
  assert (haux3 : 0 <= 600 * tau + L * (v N - 10))
    by (clear - htau0 hx3_0; lra).
  assert (hr3_360k : r3 <= 360000 * tau ^ 2)
    by (clear - hr3_sq hx3_le haux3; nra).
  (* Error-term products. *)
  assert (hq1 : 0 <= L ^ 3 * r1) by (clear - hL3p_0 hr1_0; nra).
  assert (hq2 : 0 <= L ^ 2 * r2) by (clear - hL2_0 hr2_0; nra).
  assert (hq3 : 0 <= L * r3) by (clear - hL0 hr3_0; nra).
  assert (hp1 : L ^ 3 * r1 <= 243 * tau ^ 2)
    by (clear - hL3p hL3p_0 hr1_0 hr1_9t2 ht2_0; nra).
  assert (hp2 : L ^ 2 * r2 <= 1296 * tau ^ 2)
    by (clear - hL2 hL2_0 hr2_0 hr2_144 ht2_0; nra).
  assert (hp3 : L * r3 <= 1080000 * tau ^ 2)
    by (clear - hL0 hL3 hr3_0 hr3_360k ht2_0; nra).
  (* Main term scaled by tau. *)
  assert (hmain_lo : 2811012357389 * tau <= 100000000000 * L ^ 4 * tau)
    by (clear - hmain_lo4 htau0; nra).
  assert (hmain_hi :
      100000000000 * L ^ 4 * tau <= (2811012357389 + 1/2) * tau)
    by (clear - hmain_hi4 htau0; nra).
  (* Bounds on x. *)
  assert (hx_lo : 2811012357389 * tau <= x N)
    by (clear - hx_eq hmain_lo hq1 hq2 hq3; lra).
  assert (hx_hi : x N <= (2811012357389 + 501/1000) * tau)
    by (clear - hx_eq hmain_hi hp1 hp2 hp3 htau2_le ht2_0; lra).
  assert (hx_0 : 0 <= x N) by (clear - hx_lo htau0; lra).
  assert (hx_1 : x N <= 1) by (clear - hx_hi htau0 htauS; lra).
  assert (haux_x : 0 <= (2811012357389 + 501/1000) * tau + x N)
    by (clear - htau0 hx_0; lra).
  assert (hx_sq : x N ^ 2 <= 1/1000 * tau)
    by (clear - hx_hi hx_0 haux_x htau2_le htau0; nra).
  replace (IZR M) with 2811012357389 by reflexivity.
  clear - htau0 hx_lo hx_hi hx_sq hx_0 hx_1.
  repeat split; lra.
Qed.

(* The unconditional floor identities, mirroring the Lean theorems
   `floor_tinyExponentTower_sub` and
   `floor_expanded_tinyExponentTower_sub`. *)

Theorem floor_tinyExponentTower_sub :
    (Zfloor tinyExponentTower - towerBaseInt N = M)%Z.
Proof.
  destruct x_N_estimates as [hlo [hquad hx01]].
  apply floor_tinyExponentTower_sub_from_log_remainder_bounds;
    try assumption.
  apply exp_quad_remainder_upper. exact hx01.
Qed.

Theorem floor_expanded_tinyExponentTower_sub :
    (Zfloor expandedTinyExponentTower - towerBaseInt N = M)%Z.
Proof.
  destruct x_N_estimates as [hlo [hquad hx01]].
  apply floor_expanded_tinyExponentTower_sub_from_log_remainder_bounds;
    try assumption.
  apply exp_quad_remainder_upper. exact hx01.
Qed.

Theorem floor_tinyExponentTower_value :
    Zfloor tinyExponentTower = (towerBaseInt N + M)%Z.
Proof.
  pose proof floor_tinyExponentTower_sub. lia.
Qed.

End TinyExponentTower.
End LeanProofs.
