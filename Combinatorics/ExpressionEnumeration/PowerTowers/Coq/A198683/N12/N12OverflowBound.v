(*
  Coq port of the headline of PowerTowers/A198683/N12/N12OverflowBound.lean:
  the imaginary part of the traced values[11][57] overflow-chain
  representative overflowBase11 = i^w10 exceeds 10^100, so the n = 12
  overflow candidate i^overflowBase11 is separated (by sheer modulus)
  from every principal power a^b whose log-modulus is moderate.

  The Lean file certifies Im overflowBase11 > 10^100 through a
  ~44-digit hand-propagated Taylor/rational-box cascade.  Here the
  coq-interval `interval` tactic replaces the entire cascade.  The one
  genuinely delicate step survives in both developments: Re w10 is of
  magnitude ~6.8e34, while sin((PI/2) * Re w10) only makes sense after
  reducing Re w10 modulo the period 4.  We box Re w10 shifted by an
  explicit 35-digit integer multiple of 4,

      k = 16987618442022999001903102531394909,
      8/5 < Re w10 + 4*k < 7/4,

  (interval at i_prec 200; the box absorbs a ~35-digit cancellation)
  and transport sin across the shift with a Z-indexed periodicity lemma
  sin (x + 2*IZR k*PI) = sin x, giving sin((PI/2) * Re w10) > 1/4.
  The crude companion bound Im w10 < -150 then makes

      Im overflowBase11 = exp(-(PI/2) * Im w10) * sin((PI/2) * Re w10)
                        > exp(75*PI) * (1/4)
                        > 10^100.

  Ground truth (mpmath, 120 digits):
      Re w10 = -67950473768091996007612410125579634.33369385459...
      Im w10 = -60442194990557786601897195733781578.73489031624...
      Re w10 + 4*k = 1.66630614540820245...
      sin((PI/2) * Re w10) = 0.50049035472036380...
      log10 (Im overflowBase11) = 4.12329508097074205977e34.
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Psatz.
From Stdlib Require Import ZArith.
From Coquelicot Require Import Complex.
From Interval Require Import Tactic.
From PowerTowers.A198683 Require Import Complex.
From PowerTowers.A198683.N12 Require Import N12Bounds.
From PowerTowers.A198683.N12 Require Import N12ComplexTowers.

Open Scope R_scope.

Module LeanProofs.
Module A198683N12OverflowBound.

Module Cx := PowerTowers.A198683.Complex.LeanProofs.A198683Complex.
Module Bd := PowerTowers.A198683.N12.N12Bounds.LeanProofs.A198683N12Bounds.
Module Tw :=
  PowerTowers.A198683.N12.N12ComplexTowers.LeanProofs.A198683N12ComplexTowers.

Import Cx.

(* ------------------------------------------------------------------ *)
(* Real shadows of the overflow chain, in the exact shape produced by  *)
(* the Towers decomposition lemmas (everything rooted at PI).          *)
(* ------------------------------------------------------------------ *)

(* w5 = i^(exp(-theta)) on the unit circle. *)
Definition w5_re : R := cos (PI / 2 * exp (- Bd.theta)).
Definition w5_im : R := sin (PI / 2 * exp (- Bd.theta)).

(* w8 = (-i)^w5. *)
Definition w8_re : R := exp (PI / 2 * w5_im) * cos (PI / 2 * w5_re).
Definition w8_im : R := - (exp (PI / 2 * w5_im) * sin (PI / 2 * w5_re)).

(* w9 = i^w8. *)
Definition w9_re : R := exp (- (PI / 2) * w8_im) * cos (PI / 2 * w8_re).
Definition w9_im : R := exp (- (PI / 2) * w8_im) * sin (PI / 2 * w8_re).

(* w10 = i^w9. *)
Definition w10_re : R := exp (- (PI / 2) * w9_im) * cos (PI / 2 * w9_re).
Definition w10_im : R := exp (- (PI / 2) * w9_im) * sin (PI / 2 * w9_re).

(* ------------------------------------------------------------------ *)
(* Glue: the shadows equal the re/im parts of the complex towers.      *)
(* ------------------------------------------------------------------ *)

Lemma w5C_re_eq : Re Tw.w5C = w5_re.
Proof. unfold w5_re; rewrite Tw.w5C_eq; reflexivity. Qed.

Lemma w5C_im_eq : Im Tw.w5C = w5_im.
Proof. unfold w5_im; rewrite Tw.w5C_eq; reflexivity. Qed.

Lemma w8C_re_eq : Re Tw.w8C = w8_re.
Proof.
  unfold w8_re; rewrite Tw.w8C_re, w5C_re_eq, w5C_im_eq; reflexivity.
Qed.

Lemma w8C_im_eq : Im Tw.w8C = w8_im.
Proof.
  unfold w8_im; rewrite Tw.w8C_im, w5C_re_eq, w5C_im_eq; reflexivity.
Qed.

Lemma w9C_re_eq : Re Tw.w9C = w9_re.
Proof.
  unfold w9_re; rewrite Tw.w9C_re, w8C_re_eq, w8C_im_eq; reflexivity.
Qed.

Lemma w9C_im_eq : Im Tw.w9C = w9_im.
Proof.
  unfold w9_im; rewrite Tw.w9C_im, w8C_re_eq, w8C_im_eq; reflexivity.
Qed.

Lemma w10C_re_eq : Re Tw.w10C = w10_re.
Proof.
  unfold w10_re; rewrite Tw.w10C_re, w9C_re_eq, w9C_im_eq; reflexivity.
Qed.

Lemma w10C_im_eq : Im Tw.w10C = w10_im.
Proof.
  unfold w10_im; rewrite Tw.w10C_im, w9C_re_eq, w9C_im_eq; reflexivity.
Qed.

Lemma overflowBase11C_im_eq :
  Im Tw.overflowBase11C =
    exp (- (PI / 2) * w10_im) * sin (PI / 2 * w10_re).
Proof.
  rewrite Tw.overflowBase11C_im, w10C_re_eq, w10C_im_eq; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Z-indexed periodicity of sin (the stdlib sin_period is nat-only).   *)
(* ------------------------------------------------------------------ *)

Lemma Re_pair (a b : R) : Re (a, b) = a.
Proof. reflexivity. Qed.

Lemma sin_period_Z (x : R) (k : Z) : sin (x + 2 * IZR k * PI) = sin x.
Proof.
  destruct k as [|p|p].
  - replace (x + 2 * IZR 0 * PI) with x by ring; reflexivity.
  - rewrite <- (positive_nat_Z p), <- (INR_IZR_INZ (Pos.to_nat p));
      apply sin_period.
  - transitivity
      (sin ((x + 2 * IZR (Z.neg p) * PI) + 2 * INR (Pos.to_nat p) * PI)).
    + symmetry; apply sin_period.
    + f_equal.
      rewrite INR_IZR_INZ, positive_nat_Z.
      replace (IZR (Z.neg p)) with (- IZR (Z.pos p))
        by (rewrite <- opp_IZR; reflexivity).
      generalize (IZR (Z.pos p)); intro K; ring.
Qed.

(* ------------------------------------------------------------------ *)
(* The interval certificates.                                          *)
(* ------------------------------------------------------------------ *)

(* The explicit phase integer: Re w10 + 4*kZ lands in (8/5, 7/4). *)
Definition kZ : Z := 16987618442022999001903102531394909%Z.

(* The delicate box: Re w10 ~ -6.795e34 pinned to absolute width
   < 0.15 (a ~36-significant-digit certificate), then shifted by the
   period multiple 4*kZ into the comfortable subinterval (8/5, 7/4)
   around 1.66630614540820245. *)
Lemma w10_re_shift_box :
  8 / 5 < w10_re + 4 * IZR kZ /\ w10_re + 4 * IZR kZ < 7 / 4.
Proof.
  unfold kZ, w10_re, w9_re, w9_im, w8_re, w8_im, w5_re, w5_im,
    Bd.theta, Bd.rho.
  split; interval with (i_prec 200).
Qed.

(* The crude magnitude bound on Im w10 (true value ~ -6.04e34; any
   bound below -150 suffices for the 10^100 payoff). *)
Lemma w10_im_lt : w10_im < - 150.
Proof.
  unfold w10_im, w9_re, w9_im, w8_re, w8_im, w5_re, w5_im,
    Bd.theta, Bd.rho.
  interval with (i_prec 100).
Qed.

(* sin on the reduced argument range. *)
Lemma sin_reduced (y : R) :
  8 / 5 < y -> y < 7 / 4 -> 1 / 4 < sin (PI / 2 * y).
Proof. intros Hlo Hhi; interval. Qed.

(* The sine factor of Im overflowBase11 is comfortably positive. *)
Lemma sin_w10_re_gt : 1 / 4 < sin (PI / 2 * w10_re).
Proof.
  destruct w10_re_shift_box as [Hlo Hhi].
  replace (PI / 2 * w10_re)
    with (PI / 2 * (w10_re + 4 * IZR kZ) + 2 * IZR (- kZ) * PI)
    by (rewrite opp_IZR; generalize (IZR kZ); intro K; field).
  rewrite sin_period_Z.
  apply sin_reduced; assumption.
Qed.

(* exp(75*PI) ~ 5.36e102 dominates 4*10^100. *)
Lemma exp_75PI_gt : 4 * 10 ^ 100 < exp (75 * PI).
Proof. interval with (i_prec 60). Qed.

(* The clear-scoped nonlinear assembly step, on abstract variables so
   nra sees a four-atom problem. *)
Lemma prod_gt (E A S : R) :
  0 < E -> E < A -> 1 / 4 < S -> 4 * 10 ^ 100 < E ->
  10 ^ 100 < A * S.
Proof. intros; nra. Qed.

(* ------------------------------------------------------------------ *)
(* Headline 1: the overflow base has astronomically large imaginary    *)
(* part (Lean: overflowBase11_im_gt).                                  *)
(* ------------------------------------------------------------------ *)

Theorem overflowBase11C_im_gt : 10 ^ 100 < Im Tw.overflowBase11C.
Proof.
  rewrite overflowBase11C_im_eq.
  apply (prod_gt (exp (75 * PI))).
  - apply exp_pos.
  - apply exp_increasing.
    pose proof w10_im_lt as Hw.
    pose proof PI_RGT_0 as Hpi.
    nra.
  - exact sin_w10_re_gt.
  - exact exp_75PI_gt.
Qed.

(* ------------------------------------------------------------------ *)
(* Headline 2: the n = 12 overflow candidate i^overflowBase11 differs  *)
(* from every principal power whose log-modulus is moderate — its own  *)
(* log-modulus is below -(PI/2)*10^100 (Lean:                          *)
(* overflowCandidate12_ne_of_moderate_logModulus).                     *)
(* ------------------------------------------------------------------ *)

Theorem overflowCandidate12C_ne_of_moderate_logModulus :
  forall a b : C,
    - (PI / 2) * 10 ^ 100 < Re (Cmult (Cln a) b) ->
    Tw.overflowCandidate12C <> principalPow a b.
Proof.
  intros a b Hmod Heq.
  apply (Cexp_ne_of_Re_lt (Cmult (Cln Ci) Tw.overflowBase11C)
           (Cmult (Cln a) b)).
  - rewrite principalPow_Ci_arg, Re_pair.
    pose proof overflowBase11C_im_gt as Him.
    pose proof PI_RGT_0 as Hpi.
    set (t := Im Tw.overflowBase11C) in *.
    set (r := Re (Cmult (Cln a) b)) in *.
    clearbody t r.
    nra.
  - exact Heq.
Qed.

End A198683N12OverflowBound.
End LeanProofs.
