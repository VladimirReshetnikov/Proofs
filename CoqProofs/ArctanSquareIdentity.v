(*
  Coq port of LeanProofs/ArctanSquareIdentity.lean.

  The proof is Coq-idiomatic: all rational arctangent additions are derived
  from the standard-library inverse/tangent theorem atan_sub_correct.
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Ratan Machin.
From Stdlib Require Import Psatz Field Ring.

Open Scope R_scope.

Module LeanProofs.
Module ArctanSquareIdentity.

Definition u : R := PI / 4.
Definition a : R := atan (/ 2).
Definition b : R := atan (2 / 3).
Definition c : R := atan (/ 4).

Lemma pi_div_two_eq_two_mul_u : PI / 2 = 2 * u.
Proof. unfold u; field. Qed.

Lemma atan_pos (x : R) : 0 < x -> 0 < atan x.
Proof.
  intro hx.
  rewrite <- atan_0.
  now apply atan_increasing.
Qed.

Lemma atan_sub_correct_pos (x y : R) :
    0 < x -> 0 < y -> atan x = atan y + atan (atan_sub x y).
Proof.
  intros hx hy.
  apply atan_sub_correct.
  - nra.
  - pose proof (atan_bound x) as bx.
    pose proof (atan_bound y) as bnd_y.
    pose proof (atan_pos x hx) as px.
    pose proof (atan_pos y hy) as py.
    lra.
  - apply atan_bound.
Qed.

Lemma atan_add_pos (x y z : R) :
    0 < x -> 0 < y -> atan_sub x y = z -> atan x = atan y + atan z.
Proof.
  intros hx hy hz.
  rewrite <- hz.
  now apply atan_sub_correct_pos.
Qed.

Ltac atan_add_rational :=
  eapply atan_add_pos; try lra; unfold atan_sub; field; lra.

Lemma arctan_two : atan 2 = 2 * u - a.
Proof.
  pose proof (atan_inv 2) as h.
  assert (hpos : 0 < 2) by lra.
  specialize (h hpos).
  change (atan (/ 2)) with a in h.
  pose proof pi_div_two_eq_two_mul_u as hpi.
  lra.
Qed.

Lemma arctan_three : atan 3 = u + a.
Proof.
  unfold u, a.
  rewrite <- atan_1.
  symmetry.
  rewrite (atan_add_pos 3 1 (/2)).
  - rewrite atan_1. reflexivity.
  - lra.
  - lra.
  - unfold atan_sub; field; lra.
Qed.

Lemma arctan_four : atan 4 = 2 * u - c.
Proof.
  pose proof (atan_inv 4) as h.
  assert (hpos : 0 < 4) by lra.
  specialize (h hpos).
  change (atan (/ 4)) with c in h.
  pose proof pi_div_two_eq_two_mul_u as hpi.
  lra.
Qed.

Lemma arctan_five : atan 5 = u + b.
Proof.
  unfold u, b.
  rewrite <- atan_1.
  symmetry.
  rewrite (atan_add_pos 5 1 (2/3)).
  - rewrite atan_1. reflexivity.
  - lra.
  - lra.
  - unfold atan_sub; field; lra.
Qed.

Lemma atan_inv_two_split : 2 * a = u + atan (/ 7).
Proof.
  assert (h13 : atan (/ 2) = atan (/ 7) + atan (/ 3)).
  { rewrite (atan_add_pos (/2) (/7) (/3)); try lra.
    unfold atan_sub; field; lra. }
  unfold a, u.
  rewrite Machin_2_3.
  lra.
Qed.

Lemma arctan_seven : atan 7 = 3 * u - 2 * a.
Proof.
  pose proof (atan_inv 7) as h.
  assert (hpos : 0 < 7) by lra.
  specialize (h hpos).
  pose proof atan_inv_two_split as hsplit.
  pose proof pi_div_two_eq_two_mul_u as hpi.
  lra.
Qed.

Lemma arctan_eight : atan 8 = 2 * u + a - b.
Proof.
  assert (hsum : a + atan (/ 8) = b).
  { unfold a, b.
    symmetry.
    apply atan_add_pos; try lra.
    unfold atan_sub; field; lra. }
  pose proof (atan_inv 8) as h.
  assert (hpos : 0 < 8) by lra.
  specialize (h hpos).
  pose proof pi_div_two_eq_two_mul_u as hpi.
  lra.
Qed.

Lemma arctan_thirteen : atan 13 = u + a + c.
Proof.
  assert (hsum : atan 13 = atan 3 + c).
  { unfold c.
    apply atan_add_pos; try lra.
    unfold atan_sub; field; lra. }
  rewrite hsum, arctan_three.
  ring.
Qed.

Lemma two_mul_arctan_inv_four : 2 * c = atan (8 / 15).
Proof.
  unfold c.
  replace (2 * atan (/ 4)) with (atan (/ 4) + atan (/ 4)) by ring.
  symmetry.
  apply atan_add_pos; try lra.
  unfold atan_sub; field; lra.
Qed.

Lemma two_mul_arctan_inv_two : 2 * a = atan (4 / 3).
Proof.
  unfold a.
  replace (2 * atan (/ 2)) with (atan (/ 2) + atan (/ 2)) by ring.
  symmetry.
  apply atan_add_pos; try lra.
  unfold atan_sub; field; lra.
Qed.

Lemma arctan_eighteen : atan 18 = 2 * a + b.
Proof.
  rewrite two_mul_arctan_inv_two.
  unfold b.
  apply atan_add_pos; try lra.
  unfold atan_sub; field; lra.
Qed.

Lemma arctan_twenty_one : atan 21 = 3 * u - b - c.
Proof.
  assert (hbc : b + c = atan (11 / 10)).
  { unfold b, c.
    symmetry.
    apply atan_add_pos; try lra.
    unfold atan_sub; field; lra. }
  assert (huinv : u + atan (/21) = atan (11 / 10)).
  { unfold u.
    rewrite <- atan_1.
    symmetry.
    apply atan_add_pos; try lra.
    unfold atan_sub; field; lra. }
  pose proof (atan_inv 21) as h.
  assert (hpos : 0 < 21) by lra.
  specialize (h hpos).
  pose proof pi_div_two_eq_two_mul_u as hpi.
  lra.
Qed.

Lemma arctan_thirty_eight : atan 38 = 2 * u + a - 2 * c.
Proof.
  assert (hsum : a + atan (/38) = atan (8 / 15)).
  { unfold a.
    symmetry.
    apply atan_add_pos; try lra.
    unfold atan_sub; field; lra. }
  pose proof (atan_inv 38) as h.
  assert (hpos : 0 < 38) by lra.
  specialize (h hpos).
  pose proof two_mul_arctan_inv_four as h2c.
  pose proof pi_div_two_eq_two_mul_u as hpi.
  lra.
Qed.

Lemma arctan_forty_seven : atan 47 = 3 * u - a - b + c.
Proof.
  assert (hab : a + b = atan (7 / 4)).
  { unfold a, b.
    symmetry.
    apply atan_add_pos; try lra.
    unfold atan_sub; field; lra. }
  assert (huc : u + c = atan (5 / 3)).
  { unfold u, c.
    rewrite <- atan_1.
    symmetry.
    apply atan_add_pos; try lra.
    unfold atan_sub; field; lra. }
  assert (hsum : atan (5 / 3) + atan (/47) = atan (7 / 4)).
  { symmetry.
    apply atan_add_pos; try lra.
    unfold atan_sub; field; lra. }
  pose proof (atan_inv 47) as h.
  assert (hpos : 0 < 47) by lra.
  specialize (h hpos).
  pose proof pi_div_two_eq_two_mul_u as hpi.
  lra.
Qed.

Theorem arctan_square_identity :
    2939 * atan 2 ^ 2 -
      1250 * atan 3 ^ 2 -
      252 * atan 4 ^ 2 -
      360 * atan 5 ^ 2 -
      870 * atan 7 ^ 2 +
      450 * atan 8 ^ 2 +
      84 * atan 13 ^ 2 +
      330 * atan 18 ^ 2 -
      210 * atan 21 ^ 2 +
      147 * atan 38 ^ 2 -
      210 * atan 47 ^ 2 = 0.
Proof.
  rewrite arctan_two, arctan_three, arctan_four, arctan_five.
  rewrite arctan_seven, arctan_eight, arctan_thirteen, arctan_eighteen.
  rewrite arctan_twenty_one, arctan_thirty_eight, arctan_forty_seven.
  ring.
Qed.

End ArctanSquareIdentity.
End LeanProofs.
