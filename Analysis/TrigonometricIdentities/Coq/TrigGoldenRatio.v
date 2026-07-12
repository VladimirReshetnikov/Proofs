(*
  Coq port of the Lean module TrigonometricIdentities.TrigGoldenRatio.

  Coq's standard library has the elementary sum-to-product and pi/4, pi/6
  trigonometric facts used by the Lean proof, but not the exact value of
  cos(pi/5).  We derive that value here from the triple-angle formula and
  the quadratic it gives for c = cos(pi/5).
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Psatz Field Ring.

Open Scope R_scope.

Module LeanProofs.
Module TrigGoldenRatio.

Definition goldenRatio : R := (1 + sqrt 5) / 2.

Lemma cos_triple (x : R) : cos (3 * x) = 4 * cos x ^ 3 - 3 * cos x.
Proof.
  replace (3 * x) with (2 * x + x) by ring.
  rewrite cos_plus, cos_2a_cos, sin_2a.
  replace (cos x ^ 3) with (cos x * cos x * cos x) by ring.
  replace (2 * sin x * cos x * sin x)
    with (2 * (sin x * sin x) * cos x) by ring.
  pose proof (sin2_cos2 x) as h.
  unfold Rsqr in h.
  replace (sin x * sin x) with (1 - cos x * cos x) by lra.
  ring.
Qed.

Lemma cos_pi_div_five_quadratic :
    let c := cos (PI / 5) in 4 * c ^ 2 - 2 * c - 1 = 0.
Proof.
  set (c := cos (PI / 5)).
  assert (hcpos : 0 < c).
  { unfold c. apply cos_gt_0; pose proof PI_RGT_0; lra. }
  assert (h3 : cos (3 * (PI / 5)) = 4 * c ^ 3 - 3 * c).
  { unfold c. apply cos_triple. }
  assert (h2 : cos (2 * (PI / 5)) = 2 * c * c - 1).
  { unfold c. rewrite cos_2a_cos. ring. }
  assert (hrel : cos (3 * (PI / 5)) = - cos (2 * (PI / 5))).
  { replace (3 * (PI / 5)) with (PI - 2 * (PI / 5)) by field.
    rewrite Rtrigo_facts.cos_pi_minus. reflexivity. }
  assert (hpoly : 4 * c ^ 3 + 2 * c ^ 2 - 3 * c - 1 = 0).
  { rewrite h3, h2 in hrel. nra. }
  nra.
Qed.

Lemma cos_pi_div_five : cos (PI / 5) = (1 + sqrt 5) / 4.
Proof.
  set (c := cos (PI / 5)).
  assert (hcpos : 0 < c).
  { unfold c. apply cos_gt_0; pose proof PI_RGT_0; lra. }
  pose proof cos_pi_div_five_quadratic as hq.
  fold c in hq.
  assert (hgt : 1 / 4 < c) by nra.
  assert (hsq : (4 * c - 1) * (4 * c - 1) = 5) by nra.
  assert (hsqrt : sqrt 5 = 4 * c - 1).
  { apply sqrt_lem_1; nra. }
  unfold c in *.
  nra.
Qed.

Lemma sin_twenty_one_add_sin_thirty_nine :
    sin (7 * PI / 60) + sin (13 * PI / 60) = cos (PI / 20).
Proof.
  rewrite form3.
  replace ((7 * PI / 60 - 13 * PI / 60) / 2) with (-(PI / 20)) by field.
  replace ((7 * PI / 60 + 13 * PI / 60) / 2) with (PI / 6) by field.
  rewrite cos_neg, sin_PI6.
  field.
Qed.

Lemma sin_nine_add_cos_nine :
    sin (PI / 20) + cos (PI / 20) = sqrt 2 * cos (PI / 5).
Proof.
  replace (cos (PI / 5)) with (sin (PI / 20 + PI / 4)).
  2: { replace (PI / 20 + PI / 4) with (PI / 2 - PI / 5) by field.
       apply sin_shift. }
  rewrite sin_plus, sin_PI4, cos_PI4.
  field.
  apply sqrt2_neq_0.
Qed.

Lemma sqrt_two_mul_cos_thirty_six :
    sqrt 2 * cos (PI / 5) = goldenRatio / sqrt 2.
Proof.
  rewrite cos_pi_div_five.
  unfold goldenRatio.
  assert (hsq2 : sqrt 2 * sqrt 2 = 2) by (apply sqrt_def; lra).
  apply (Rmult_eq_reg_r (sqrt 2)).
  2: apply sqrt2_neq_0.
  replace (sqrt 2 * ((1 + sqrt 5) / 4) * sqrt 2)
    with ((sqrt 2 * sqrt 2) * (1 + sqrt 5) / 4) by field.
  rewrite hsq2.
  field.
  apply sqrt2_neq_0.
Qed.

Theorem sin_deg9_add_sin_deg21_add_sin_deg39 :
    sin (9 * PI / 180) + sin (21 * PI / 180) + sin (39 * PI / 180) =
      goldenRatio / sqrt 2.
Proof.
  replace (9 * PI / 180) with (PI / 20) by field.
  replace (21 * PI / 180) with (7 * PI / 60) by field.
  replace (39 * PI / 180) with (13 * PI / 60) by field.
  rewrite Rplus_assoc.
  rewrite sin_twenty_one_add_sin_thirty_nine.
  rewrite sin_nine_add_cos_nine.
  apply sqrt_two_mul_cos_thirty_six.
Qed.

End TrigGoldenRatio.
End LeanProofs.
