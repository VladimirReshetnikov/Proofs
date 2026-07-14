(*
  Genuine complex-number statements for the A198683 n = 12 endgame,
  mirroring the Lean development in PowerTowers/A198683/N12/N12Symbolic.lean
  and PowerTowers/A198683/N12/N12OverflowWitness.lean.

  PowerTowers/Coq/A198683/N12/N12Bounds.v proves (by coq-interval) every real
  bound about the towers, but only through real-valued shadows of the
  complex quantities (rho, theta, sigma, tau, v_re/v_im, seed_re/im,
  level1..3 re/im, base_im, nearOne1404_norm, nearOne25_norm).  This
  module defines the towers themselves as elements of Coquelicot's C
  via the principal power of PowerTowers/Coq/A198683/Complex.v, proves the
  island identities (i^i = rho, (i^i)^i = -i, i^(-i) = exp(pi/2), the
  positive-real collapses to sigma/tau), and glues each complex tower
  to its Bounds shadow:

      Cmod nearOne1404C = nearOne1404_norm
      Cmod nearOne25C   = nearOne25_norm

  The payoff is the genuine C-statement

      nearOne25C <> nearOne1404C

  obtained from the Bounds norm separation.  The overflow chain
  w2C .. w10C -> overflowBase11C -> overflowCandidate12C is defined
  with its level-by-level re/im decomposition lemmas so that the
  overflow magnitude bound can be built on top; the bound itself
  (Im overflowBase11C very large) is intentionally NOT proved here.
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Psatz.
From Coquelicot Require Import Complex.
From PowerTowers.A198683 Require Import Complex.
From PowerTowers.A198683.N12 Require Import N12Bounds.

Open Scope R_scope.

Module LeanProofs.
Module A198683N12ComplexTowers.

Module Cx := PowerTowers.A198683.Complex.LeanProofs.A198683Complex.
Module Bd := PowerTowers.A198683.N12.N12Bounds.LeanProofs.A198683N12Bounds.

Import Cx.

(* ------------------------------------------------------------------ *)
(* The island constants (Lean: A198683N12Symbolic).                    *)
(* ------------------------------------------------------------------ *)

(* q = i^i. *)
Definition qC : C := principalPow Ci Ci.

(* u = i^(i^i). *)
Definition uC : C := principalPow Ci qC.

(* v = i^(i^(i^i)). *)
Definition vC : C := principalPow Ci uC.

(* nearProbeR = (i^((i^i)^i))^(i^((i^i)^i)), a positive real. *)
Definition nearProbeRC : C :=
  principalPow
    (principalPow Ci (principalPow qC Ci))
    (principalPow Ci (principalPow qC Ci)).

(* nearProbeS = (i^i)^nearProbeR, a tiny positive real. *)
Definition nearProbeSC : C := principalPow qC nearProbeRC.

(* Representative idx = 1404 of the n = 12 near-one class:
   (i^i)^nearProbeS. *)
Definition nearOne1404C : C := principalPow qC nearProbeSC.

(* The idx = 25 chain: seed = ((i^i)^i)^v = (-i)^v, then four i^...
   layers, then the near-one representative itself. *)
Definition nearOne25SeedC : C := principalPow (principalPow qC Ci) vC.

Definition nearOne25Level1C : C := principalPow Ci nearOne25SeedC.

Definition nearOne25Level2C : C := principalPow Ci nearOne25Level1C.

Definition nearOne25Level3C : C := principalPow Ci nearOne25Level2C.

Definition nearOne25BaseC : C := principalPow Ci nearOne25Level3C.

(* Representative idx = 25 of the n = 12 near-one class: i^nearOne25Base. *)
Definition nearOne25C : C := principalPow Ci nearOne25BaseC.

(* ------------------------------------------------------------------ *)
(* Island identities (Lean: I_pow_I_eq_q, q_pow_I_eq_neg_I,            *)
(* I_pow_neg_I_eq_qInv, and the positive-real probe collapses).        *)
(* ------------------------------------------------------------------ *)

(* i^i = exp(-pi/2) = rho, a positive real. *)
Lemma qC_eq : qC = RtoC Bd.rho.
Proof.
  unfold qC, principalPow.
  rewrite principalPow_Ci_arg.
  unfold Re, Im, Ci; simpl fst; simpl snd.
  replace (- (PI / 2) * 1) with (- (PI / 2)) by ring.
  replace (PI / 2 * 0) with 0 by ring.
  rewrite Cexp_pair, cos_0, sin_0.
  unfold RtoC, Bd.rho.
  apply injective_projections; simpl; ring.
Qed.

Lemma rho_pos : 0 < Bd.rho.
Proof. unfold Bd.rho; apply exp_pos. Qed.

(* (i^i)^i = -i. *)
Lemma qC_pow_Ci_eq : principalPow qC Ci = Copp Ci.
Proof.
  rewrite qC_eq.
  rewrite principalPow_posreal by exact rho_pos.
  unfold Bd.rho.
  rewrite ln_exp.
  unfold Re, Im, Ci; simpl fst; simpl snd.
  replace (- (PI / 2) * 0) with 0 by ring.
  replace (- (PI / 2) * 1) with (- (PI / 2)) by ring.
  rewrite Cexp_pair, exp_0, cos_neg, sin_neg, cos_PI2, sin_PI2.
  unfold Copp, Ci.
  apply injective_projections; simpl; ring.
Qed.

(* i^(-i) = exp(pi/2). *)
Lemma Ci_pow_neg_Ci_eq : principalPow Ci (Copp Ci) = RtoC (exp (PI / 2)).
Proof.
  unfold principalPow.
  rewrite principalPow_Ci_arg.
  unfold Re, Im, Copp, Ci; simpl fst; simpl snd.
  replace (- (PI / 2) * - (1)) with (PI / 2) by ring.
  replace (PI / 2 * - 0) with 0 by ring.
  rewrite Cexp_pair, cos_0, sin_0.
  unfold RtoC.
  apply injective_projections; simpl; ring.
Qed.

(* nearProbeR = exp((pi/2) * exp(pi/2)) = sigma, a positive real. *)
Lemma nearProbeRC_eq : nearProbeRC = RtoC Bd.sigma.
Proof.
  unfold nearProbeRC.
  rewrite qC_pow_Ci_eq, Ci_pow_neg_Ci_eq.
  rewrite principalPow_posreal_real by apply exp_pos.
  rewrite ln_exp.
  unfold Bd.sigma.
  reflexivity.
Qed.

(* nearProbeS = exp(-(pi/2) * sigma) = tau, a tiny positive real. *)
Lemma nearProbeSC_eq : nearProbeSC = RtoC Bd.tau.
Proof.
  unfold nearProbeSC.
  rewrite qC_eq, nearProbeRC_eq.
  rewrite principalPow_posreal_real by exact rho_pos.
  unfold Bd.rho.
  rewrite ln_exp.
  unfold Bd.tau.
  reflexivity.
Qed.

Lemma tau_pos : 0 < Bd.tau.
Proof. unfold Bd.tau; apply exp_pos. Qed.

(* nearOne1404 = exp(-(pi/2) * tau), a positive real. *)
Lemma nearOne1404C_eq : nearOne1404C = RtoC Bd.nearOne1404_norm.
Proof.
  unfold nearOne1404C.
  rewrite qC_eq, nearProbeSC_eq.
  rewrite principalPow_posreal_real by exact rho_pos.
  unfold Bd.rho.
  rewrite ln_exp.
  unfold Bd.nearOne1404_norm.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The idx = 25 chain against its Bounds shadows.                      *)
(* ------------------------------------------------------------------ *)

(* u = exp(i*theta) = (cos theta, sin theta). *)
Lemma uC_eq : uC = (cos Bd.theta, sin Bd.theta).
Proof.
  unfold uC.
  rewrite qC_eq.
  rewrite principalPow_Ci_real.
  unfold Bd.theta.
  reflexivity.
Qed.

Lemma vC_re : Re vC = Bd.v_re.
Proof.
  unfold vC.
  rewrite uC_eq, principalPow_Ci_re.
  unfold Bd.v_re, Re, Im; simpl fst; simpl snd.
  reflexivity.
Qed.

Lemma vC_im : Im vC = Bd.v_im.
Proof.
  unfold vC.
  rewrite uC_eq, principalPow_Ci_im.
  unfold Bd.v_im, Re, Im; simpl fst; simpl snd.
  reflexivity.
Qed.

Lemma vC_eq : vC = (Bd.v_re, Bd.v_im).
Proof.
  apply injective_projections; simpl.
  - exact vC_re.
  - exact vC_im.
Qed.

Lemma seedC_re : Re nearOne25SeedC = Bd.seed_re.
Proof.
  unfold nearOne25SeedC.
  rewrite qC_pow_Ci_eq, vC_eq, principalPow_neg_Ci_re.
  unfold Bd.seed_re, Re, Im; simpl fst; simpl snd.
  reflexivity.
Qed.

Lemma seedC_im : Im nearOne25SeedC = Bd.seed_im.
Proof.
  unfold nearOne25SeedC.
  rewrite qC_pow_Ci_eq, vC_eq, principalPow_neg_Ci_im.
  unfold Bd.seed_im, Re, Im; simpl fst; simpl snd.
  reflexivity.
Qed.

Lemma seedC_eq : nearOne25SeedC = (Bd.seed_re, Bd.seed_im).
Proof.
  apply injective_projections; simpl.
  - exact seedC_re.
  - exact seedC_im.
Qed.

Lemma level1C_re : Re nearOne25Level1C = Bd.level1_re.
Proof.
  unfold nearOne25Level1C.
  rewrite seedC_eq, principalPow_Ci_re.
  unfold Bd.level1_re, Re, Im; simpl fst; simpl snd.
  reflexivity.
Qed.

Lemma level1C_im : Im nearOne25Level1C = Bd.level1_im.
Proof.
  unfold nearOne25Level1C.
  rewrite seedC_eq, principalPow_Ci_im.
  unfold Bd.level1_im, Re, Im; simpl fst; simpl snd.
  reflexivity.
Qed.

Lemma level1C_eq : nearOne25Level1C = (Bd.level1_re, Bd.level1_im).
Proof.
  apply injective_projections; simpl.
  - exact level1C_re.
  - exact level1C_im.
Qed.

Lemma level2C_re : Re nearOne25Level2C = Bd.level2_re.
Proof.
  unfold nearOne25Level2C.
  rewrite level1C_eq, principalPow_Ci_re.
  unfold Bd.level2_re, Re, Im; simpl fst; simpl snd.
  reflexivity.
Qed.

Lemma level2C_im : Im nearOne25Level2C = Bd.level2_im.
Proof.
  unfold nearOne25Level2C.
  rewrite level1C_eq, principalPow_Ci_im.
  unfold Bd.level2_im, Re, Im; simpl fst; simpl snd.
  reflexivity.
Qed.

Lemma level2C_eq : nearOne25Level2C = (Bd.level2_re, Bd.level2_im).
Proof.
  apply injective_projections; simpl.
  - exact level2C_re.
  - exact level2C_im.
Qed.

Lemma level3C_re : Re nearOne25Level3C = Bd.level3_re.
Proof.
  unfold nearOne25Level3C.
  rewrite level2C_eq, principalPow_Ci_re.
  unfold Bd.level3_re, Re, Im; simpl fst; simpl snd.
  reflexivity.
Qed.

Lemma level3C_im : Im nearOne25Level3C = Bd.level3_im.
Proof.
  unfold nearOne25Level3C.
  rewrite level2C_eq, principalPow_Ci_im.
  unfold Bd.level3_im, Re, Im; simpl fst; simpl snd.
  reflexivity.
Qed.

Lemma level3C_eq : nearOne25Level3C = (Bd.level3_re, Bd.level3_im).
Proof.
  apply injective_projections; simpl.
  - exact level3C_re.
  - exact level3C_im.
Qed.

Lemma baseC_im : Im nearOne25BaseC = Bd.base_im.
Proof.
  unfold nearOne25BaseC.
  rewrite level3C_eq, principalPow_Ci_im.
  unfold Bd.base_im, Re, Im; simpl fst; simpl snd.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The glue: complex moduli equal the Bounds norm shadows.             *)
(* ------------------------------------------------------------------ *)

Theorem Cmod_nearOne1404C : Cmod nearOne1404C = Bd.nearOne1404_norm.
Proof.
  rewrite nearOne1404C_eq, Cmod_R.
  apply Rabs_pos_eq.
  unfold Bd.nearOne1404_norm.
  apply Rlt_le, exp_pos.
Qed.

Theorem Cmod_nearOne25C : Cmod nearOne25C = Bd.nearOne25_norm.
Proof.
  unfold nearOne25C.
  rewrite Cmod_principalPow_Ci, baseC_im.
  unfold Bd.nearOne25_norm.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The payoff: the two retained near-one representatives are distinct  *)
(* as complex numbers (Lean: nearOne25_ne_nearOne1404_of_endpoint_     *)
(* bounds, here unconditional).                                        *)
(* ------------------------------------------------------------------ *)

Theorem nearOne25C_ne_nearOne1404C : nearOne25C <> nearOne1404C.
Proof.
  intro Heq.
  assert (Hm : Cmod nearOne25C = Cmod nearOne1404C)
    by (rewrite Heq; reflexivity).
  rewrite Cmod_nearOne25C, Cmod_nearOne1404C in Hm.
  pose proof Bd.nearOne1404_norm_lt_nearOne25_norm.
  lra.
Qed.

(* ------------------------------------------------------------------ *)
(* The overflow chain (Lean: A198683N12OverflowWitness).               *)
(*                                                                     *)
(* Only the definitions, the exact island identities, and the          *)
(* level-by-level re/im decompositions are provided; the magnitude     *)
(* bound on Im overflowBase11C is deliberately left to the overflow    *)
(* bound module.                                                       *)
(* ------------------------------------------------------------------ *)

(* i^i. *)
Definition w2C : C := principalPow Ci Ci.

(* (i^i)^i. *)
Definition w3RC : C := principalPow w2C Ci.

(* (i^i)^(i^i). *)
Definition w4C : C := principalPow w2C w2C.

(* i^((i^i)^(i^i)). *)
Definition w5C : C := principalPow Ci w4C.

(* ((i^i)^i)^(i^((i^i)^(i^i))). *)
Definition w8C : C := principalPow w3RC w5C.

(* i^w8. *)
Definition w9C : C := principalPow Ci w8C.

(* i^w9. *)
Definition w10C : C := principalPow Ci w9C.

(* The traced values[11][57] representative: i^w10. *)
Definition overflowBase11C : C := principalPow Ci w10C.

(* The corresponding n = 12 overflow candidate: i^overflowBase11. *)
Definition overflowCandidate12C : C := principalPow Ci overflowBase11C.

Lemma w2C_eq_qC : w2C = qC.
Proof. reflexivity. Qed.

Lemma w2C_eq : w2C = RtoC Bd.rho.
Proof. exact qC_eq. Qed.

(* (i^i)^i = -i, exactly. *)
Lemma w3RC_eq : w3RC = Copp Ci.
Proof. exact qC_pow_Ci_eq. Qed.

(* (i^i)^(i^i) = exp(-theta), a positive real. *)
Lemma w4C_eq : w4C = RtoC (exp (- Bd.theta)).
Proof.
  unfold w4C.
  rewrite w2C_eq.
  rewrite principalPow_posreal_real by exact rho_pos.
  unfold Bd.rho.
  rewrite ln_exp.
  f_equal; f_equal.
  unfold Bd.theta, Bd.rho.
  ring.
Qed.

(* w5 = i^exp(-theta) lies on the unit circle. *)
Lemma w5C_eq :
  w5C = (cos (PI / 2 * exp (- Bd.theta)), sin (PI / 2 * exp (- Bd.theta))).
Proof.
  unfold w5C.
  rewrite w4C_eq.
  apply principalPow_Ci_real.
Qed.

(* Level decompositions: each next level's re/im in terms of exp, cos,
   sin of the previous level's re/im. *)

Lemma w8C_re :
  Re w8C = exp (PI / 2 * Im w5C) * cos (PI / 2 * Re w5C).
Proof.
  unfold w8C.
  rewrite w3RC_eq.
  apply principalPow_neg_Ci_re.
Qed.

Lemma w8C_im :
  Im w8C = - (exp (PI / 2 * Im w5C) * sin (PI / 2 * Re w5C)).
Proof.
  unfold w8C.
  rewrite w3RC_eq.
  apply principalPow_neg_Ci_im.
Qed.

Lemma w9C_re :
  Re w9C = exp (- (PI / 2) * Im w8C) * cos (PI / 2 * Re w8C).
Proof. apply principalPow_Ci_re. Qed.

Lemma w9C_im :
  Im w9C = exp (- (PI / 2) * Im w8C) * sin (PI / 2 * Re w8C).
Proof. apply principalPow_Ci_im. Qed.

Lemma w10C_re :
  Re w10C = exp (- (PI / 2) * Im w9C) * cos (PI / 2 * Re w9C).
Proof. apply principalPow_Ci_re. Qed.

Lemma w10C_im :
  Im w10C = exp (- (PI / 2) * Im w9C) * sin (PI / 2 * Re w9C).
Proof. apply principalPow_Ci_im. Qed.

Lemma overflowBase11C_re :
  Re overflowBase11C = exp (- (PI / 2) * Im w10C) * cos (PI / 2 * Re w10C).
Proof. apply principalPow_Ci_re. Qed.

Lemma overflowBase11C_im :
  Im overflowBase11C = exp (- (PI / 2) * Im w10C) * sin (PI / 2 * Re w10C).
Proof. apply principalPow_Ci_im. Qed.

(* The overflow candidate's modulus is controlled by Im overflowBase11C. *)
Lemma Cmod_overflowCandidate12C :
  Cmod overflowCandidate12C = exp (- (PI / 2) * Im overflowBase11C).
Proof. apply Cmod_principalPow_Ci. Qed.

(* The distinctness criterion for the overflow candidate: any i-power
   whose exponent has strictly smaller imaginary part than
   overflowBase11C differs from overflowCandidate12C. *)
Lemma overflowCandidate12C_ne_of_Im_lt (z : C) :
  Im z < Im overflowBase11C ->
  principalPow Ci z <> overflowCandidate12C.
Proof.
  intro Hlt.
  exact (principalPow_Ci_ne_of_Im_lt z overflowBase11C Hlt).
Qed.

End A198683N12ComplexTowers.
End LeanProofs.
