(*
  Coq port of the final certification layer from
  LeanProofs/TinyExponentTower.lean.

  The Lean module proves the hard analytic estimates on logarithms and
  exponentials, then finishes by converting two tiny exponential-increment
  bounds into the stated floor identity.  This Coq port proves that final
  conversion generically, and specializes it to the concrete tower.  The
  long interval proof of the input bounds is left as explicit hypotheses.
*)

From Stdlib Require Import Reals.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Psatz Field.

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

Lemma towerBaseInt_cast (hk : (0 <= k)%Z) :
    IZR towerBaseInt = towerBase.
Proof.
  exact (IZR_pow10_Rpower hk).
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
  - rewrite plus_IZR, towerBaseInt_cast by exact hk.
    replace (towerBase + IZR m) with (towerBase * (1 + IZR m * t)).
    + apply Rmult_le_compat_l.
      * left. exact towerBase_pos.
      * exact hexp_lower.
    + rewrite Rmult_plus_distr_l, Rmult_1_r.
      replace (towerBase * (IZR m * t)) with (IZR m * (towerBase * t)) by ring.
      rewrite towerBase_mul_t.
      ring.
  - rewrite plus_IZR, towerBaseInt_cast by exact hk.
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

End TinyExponentTower.
End LeanProofs.
