(*
  Reusable complex-number foundation for the A198683 principal power
  towers, mirroring the Lean development in
  LeanProofs/A198683Tower.lean (`principalPow z w = exp (log z * w)`).

  Coquelicot's `Complex` module provides the type `C := R * R` with
  `Ci`, `RtoC`, `Cmod`, and the field operations, but no complex
  exponential or logarithm.  This module defines:

    Cexp z        := (exp (Re z) * cos (Im z), exp (Re z) * sin (Im z))
    Carg z        := the principal argument in (-PI, PI] (case-defined)
    Cln z         := (ln (Cmod z), Carg z)
    principalPow z w := Cexp (Cln z * w)

  together with the evaluation lemmas actually used by the concrete
  towers (Cln at Ci, -Ci, and positive reals) and the workhorse
  real/imaginary-part power formulas that match the shape of the real
  decompositions in CoqProofs/A198683N12Bounds.v:

    Re (i^z)    = exp (-(PI/2) * Im z) * cos (PI/2 * Re z)
    Im (i^z)    = exp (-(PI/2) * Im z) * sin (PI/2 * Re z)
    Re ((-i)^z) = exp (PI/2 * Im z) * cos (PI/2 * Re z)
    Im ((-i)^z) = - (exp (PI/2 * Im z) * sin (PI/2 * Re z))
    r^z (r > 0) = Cexp (ln r * Re z, ln r * Im z)

  The injectivity-breaking criteria `Cexp_ne_of_Re_lt` and
  `principalPow_Ci_ne_of_Im_lt` are the C-analogues of the Lean
  Magnitude criterion: two principal exponentials with strictly
  ordered "growth" coordinates have different moduli, hence differ.
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Psatz.
From Coquelicot Require Import Complex.

Open Scope R_scope.

Module LeanProofs.
Module A198683Complex.

(* ------------------------------------------------------------------ *)
(* Complex exponential.                                                *)
(* ------------------------------------------------------------------ *)

Definition Cexp (z : C) : C :=
  (exp (Re z) * cos (Im z), exp (Re z) * sin (Im z)).

Lemma Cexp_pair (a b : R) :
  Cexp (a, b) = (exp a * cos b, exp a * sin b).
Proof. reflexivity. Qed.

Lemma Cmod_Cexp (z : C) : Cmod (Cexp z) = exp (Re z).
Proof.
  unfold Cmod, Cexp; simpl fst; simpl snd.
  replace ((exp (Re z) * cos (Im z)) ^ 2 + (exp (Re z) * sin (Im z)) ^ 2)
    with (Rsqr (exp (Re z))).
  - apply sqrt_Rsqr, Rlt_le, exp_pos.
  - unfold Rsqr.
    pose proof (sin2_cos2 (Im z)) as H.
    unfold Rsqr in H.
    nra.
Qed.

Lemma Cexp_add (z w : C) :
  Cexp (Cplus z w) = Cmult (Cexp z) (Cexp w).
Proof.
  unfold Cexp, Cplus, Cmult, Re, Im; simpl.
  apply injective_projections; simpl.
  - rewrite exp_plus, cos_plus; ring.
  - rewrite exp_plus, sin_plus; ring.
Qed.

(* Cexp of a real number is the real exponential. *)
Lemma Cexp_real (a : R) : Cexp (RtoC a) = RtoC (exp a).
Proof.
  unfold Cexp, RtoC; simpl.
  rewrite cos_0, sin_0.
  apply injective_projections; simpl; ring.
Qed.

Lemma Cexp_ne_0 (z : C) : Cexp z <> RtoC 0.
Proof.
  intro H.
  assert (Hm : Cmod (Cexp z) = 0).
  { rewrite H, Cmod_R, Rabs_R0; reflexivity. }
  rewrite Cmod_Cexp in Hm.
  pose proof (exp_pos (Re z)); lra.
Qed.

(*
  The injectivity-breaking criterion: complex exponentials of points
  with strictly ordered real parts have strictly ordered moduli.
*)
Lemma Cexp_ne_of_Re_lt (x y : C) :
  Re x < Re y -> Cexp x <> Cexp y.
Proof.
  intros Hlt Heq.
  assert (Hm : Cmod (Cexp x) = Cmod (Cexp y)) by (rewrite Heq; reflexivity).
  rewrite !Cmod_Cexp in Hm.
  pose proof (exp_increasing (Re x) (Re y) Hlt); lra.
Qed.

(* ------------------------------------------------------------------ *)
(* Principal argument and logarithm.                                   *)
(*                                                                     *)
(* Only the evaluations at Ci, -Ci, and positive reals are proved;     *)
(* the Re z < 0 branches exist solely to make the definition total     *)
(* and principal ((-PI, PI]) on nonzero inputs.                        *)
(* ------------------------------------------------------------------ *)

Definition Carg (z : C) : R :=
  if Rlt_dec 0 (Re z) then atan (Im z / Re z)
  else if Rlt_dec (Re z) 0 then
         (if Rle_dec 0 (Im z)
          then atan (Im z / Re z) + PI
          else atan (Im z / Re z) - PI)
  else if Rlt_dec 0 (Im z) then PI / 2
  else if Rlt_dec (Im z) 0 then - (PI / 2)
  else 0.

Definition Cln (z : C) : C := (ln (Cmod z), Carg z).

Lemma Carg_Ci : Carg Ci = PI / 2.
Proof.
  unfold Carg, Ci; simpl.
  destruct (Rlt_dec 0 0) as [H|H]; [lra|].
  destruct (Rlt_dec 0 0) as [H'|H']; [lra|].
  destruct (Rlt_dec 0 1) as [H''|H'']; [reflexivity|lra].
Qed.

Lemma Carg_neg_Ci : Carg (Copp Ci) = - (PI / 2).
Proof.
  unfold Carg, Copp, Ci; simpl.
  destruct (Rlt_dec 0 (- 0)) as [H|H]; [lra|].
  destruct (Rlt_dec (- 0) 0) as [H'|H']; [lra|].
  destruct (Rlt_dec 0 (- (1))) as [H''|H'']; [lra|].
  destruct (Rlt_dec (- (1)) 0) as [H'''|H''']; [reflexivity|lra].
Qed.

Lemma Carg_posreal (r : R) : 0 < r -> Carg (RtoC r) = 0.
Proof.
  intro Hr.
  unfold Carg, RtoC; simpl.
  destruct (Rlt_dec 0 r) as [H|H]; [|lra].
  replace (0 / r) with 0 by (field; lra).
  apply atan_0.
Qed.

Lemma Cmod_Ci : Cmod Ci = 1.
Proof.
  unfold Cmod, Ci; simpl fst; simpl snd.
  replace (0 ^ 2 + 1 ^ 2) with 1 by ring.
  apply sqrt_1.
Qed.

Lemma Cmod_neg_Ci : Cmod (Copp Ci) = 1.
Proof.
  unfold Cmod, Copp, Ci; simpl fst; simpl snd.
  replace ((- 0) ^ 2 + (- (1)) ^ 2) with 1 by ring.
  apply sqrt_1.
Qed.

Lemma Cln_Ci : Cln Ci = (0, PI / 2).
Proof.
  unfold Cln.
  rewrite Cmod_Ci, ln_1, Carg_Ci.
  reflexivity.
Qed.

Lemma Cln_neg_Ci : Cln (Copp Ci) = (0, - (PI / 2)).
Proof.
  unfold Cln.
  rewrite Cmod_neg_Ci, ln_1, Carg_neg_Ci.
  reflexivity.
Qed.

Lemma Cln_posreal (r : R) : 0 < r -> Cln (RtoC r) = (ln r, 0).
Proof.
  intro Hr.
  unfold Cln.
  rewrite Cmod_R, Rabs_pos_eq by lra.
  rewrite Carg_posreal by exact Hr.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Principal power.                                                    *)
(* ------------------------------------------------------------------ *)

(* The uniform principal power, matching Lean's
   `principalPow z w = Complex.exp (Complex.log z * w)`. *)
Definition principalPow (z w : C) : C := Cexp (Cmult (Cln z) w).

(* --- powers of i --------------------------------------------------- *)

Lemma principalPow_Ci_arg (w : C) :
  Cmult (Cln Ci) w = (- (PI / 2) * Im w, PI / 2 * Re w).
Proof.
  rewrite Cln_Ci.
  unfold Cmult, Re, Im; simpl.
  apply injective_projections; simpl; ring.
Qed.

Lemma principalPow_Ci_re (w : C) :
  Re (principalPow Ci w) =
    exp (- (PI / 2) * Im w) * cos (PI / 2 * Re w).
Proof.
  unfold principalPow.
  rewrite principalPow_Ci_arg.
  reflexivity.
Qed.

Lemma principalPow_Ci_im (w : C) :
  Im (principalPow Ci w) =
    exp (- (PI / 2) * Im w) * sin (PI / 2 * Re w).
Proof.
  unfold principalPow.
  rewrite principalPow_Ci_arg.
  reflexivity.
Qed.

Lemma Cmod_principalPow_Ci (w : C) :
  Cmod (principalPow Ci w) = exp (- (PI / 2) * Im w).
Proof.
  unfold principalPow.
  rewrite Cmod_Cexp, principalPow_Ci_arg.
  reflexivity.
Qed.

(* i^s for a real exponent s lies on the unit circle at angle PI/2*s. *)
Lemma principalPow_Ci_real (s : R) :
  principalPow Ci (RtoC s) = (cos (PI / 2 * s), sin (PI / 2 * s)).
Proof.
  unfold principalPow.
  rewrite principalPow_Ci_arg; simpl.
  unfold Cexp; simpl.
  replace (- (PI / 2) * 0) with 0 by ring.
  rewrite exp_0.
  apply injective_projections; simpl; ring.
Qed.

(* The i-power injectivity-breaking criterion: exponents with strictly
   ordered imaginary parts give powers with different moduli. *)
Lemma principalPow_Ci_ne_of_Im_lt (z w : C) :
  Im z < Im w -> principalPow Ci z <> principalPow Ci w.
Proof.
  intros Hlt Heq.
  assert (Hm : Cmod (principalPow Ci z) = Cmod (principalPow Ci w))
    by (rewrite Heq; reflexivity).
  rewrite !Cmod_principalPow_Ci in Hm.
  assert (Hexp : exp (- (PI / 2) * Im w) < exp (- (PI / 2) * Im z)).
  { apply exp_increasing.
    pose proof PI_RGT_0; nra. }
  lra.
Qed.

(* --- powers of -i -------------------------------------------------- *)

Lemma principalPow_neg_Ci_arg (w : C) :
  Cmult (Cln (Copp Ci)) w = (PI / 2 * Im w, - (PI / 2 * Re w)).
Proof.
  rewrite Cln_neg_Ci.
  unfold Cmult, Re, Im; simpl.
  apply injective_projections; simpl; ring.
Qed.

Lemma principalPow_neg_Ci_re (w : C) :
  Re (principalPow (Copp Ci) w) =
    exp (PI / 2 * Im w) * cos (PI / 2 * Re w).
Proof.
  unfold principalPow.
  rewrite principalPow_neg_Ci_arg.
  unfold Cexp; simpl.
  rewrite cos_neg.
  reflexivity.
Qed.

Lemma principalPow_neg_Ci_im (w : C) :
  Im (principalPow (Copp Ci) w) =
    - (exp (PI / 2 * Im w) * sin (PI / 2 * Re w)).
Proof.
  unfold principalPow.
  rewrite principalPow_neg_Ci_arg.
  unfold Cexp; simpl.
  rewrite sin_neg.
  ring.
Qed.

Lemma Cmod_principalPow_neg_Ci (w : C) :
  Cmod (principalPow (Copp Ci) w) = exp (PI / 2 * Im w).
Proof.
  unfold principalPow.
  rewrite Cmod_Cexp, principalPow_neg_Ci_arg.
  reflexivity.
Qed.

(* --- powers of a positive real base -------------------------------- *)

Lemma principalPow_posreal (r : R) (w : C) :
  0 < r ->
  principalPow (RtoC r) w = Cexp (ln r * Re w, ln r * Im w).
Proof.
  intro Hr.
  unfold principalPow.
  rewrite Cln_posreal by exact Hr.
  f_equal.
  unfold Cmult, Re, Im; simpl.
  apply injective_projections; simpl; ring.
Qed.

Lemma principalPow_posreal_re (r : R) (w : C) :
  0 < r ->
  Re (principalPow (RtoC r) w) =
    exp (ln r * Re w) * cos (ln r * Im w).
Proof.
  intro Hr.
  rewrite principalPow_posreal by exact Hr.
  reflexivity.
Qed.

Lemma principalPow_posreal_im (r : R) (w : C) :
  0 < r ->
  Im (principalPow (RtoC r) w) =
    exp (ln r * Re w) * sin (ln r * Im w).
Proof.
  intro Hr.
  rewrite principalPow_posreal by exact Hr.
  reflexivity.
Qed.

Lemma Cmod_principalPow_posreal (r : R) (w : C) :
  0 < r ->
  Cmod (principalPow (RtoC r) w) = exp (ln r * Re w).
Proof.
  intro Hr.
  rewrite principalPow_posreal by exact Hr.
  rewrite Cmod_Cexp.
  reflexivity.
Qed.

(* A positive real to a real power is the real power function. *)
Lemma principalPow_posreal_real (r s : R) :
  0 < r ->
  principalPow (RtoC r) (RtoC s) = RtoC (exp (ln r * s)).
Proof.
  intro Hr.
  rewrite principalPow_posreal by exact Hr.
  simpl.
  replace (ln r * 0) with 0 by ring.
  rewrite Cexp_pair, cos_0, sin_0.
  unfold RtoC.
  apply injective_projections; simpl; ring.
Qed.

End A198683Complex.
End LeanProofs.
