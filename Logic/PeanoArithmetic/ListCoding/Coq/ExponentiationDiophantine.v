(**
  Natural-number exponentiation is Diophantine.

  This module connects the result-first relation [PowerNat m n k], meaning
  [m = n^k], to the constructive Diophantine-formula development in the
  Undecidability library.  The imported theorem [dio_fun_expo] is the direct
  formalization of Matiyasevich's argument: its positive case uses the
  alpha-sequence/Pell certificate, while its separate zero cases include the
  convention [0^0 = 1].  Thus this proof does not appeal to the more general
  computable-function-to-DPRM bridge used elsewhere in this project.

  The theorem is deliberately closed with [Defined].  Its first projection
  is therefore an executable Diophantine formula, and [dio_rel_single]
  constructively compiles that formula to one polynomial equation.
*)

From Stdlib Require Import Arith Vector.
From PAListCoding Require Import NumberTheory.
From Undecidability.Shared.Libs.DLW Require Import pos.
From Undecidability.Shared.Libs.DLW.Utils Require Import sums.
From Undecidability.H10 Require Import H10.
From Undecidability.H10.Dio Require Import dio_logic dio_expo dio_single.

Module PAListExponentiationDiophantine.

Import PAListNumberTheory.

(** The official H10 interface uses a finite vector of parameters, whereas
    [dio_rel] valuations have type [nat -> nat].  Indices outside the finite
    vector are padded with zero.  The converted relation is explicitly
    evaluated in this padded environment, making the conversion total and
    giving the polynomial compiler a concrete value for every unused
    parameter. *)
Definition finiteEnv {n} (v : Vector.t nat n) (i : nat) : nat :=
  match le_lt_dec n i with
  | left _ => 0
  | right hi => Vector.nth v (nat2pos hi)
  end.

(** Constructively compile rich Diophantine formula syntax to the official
    one-equation H10 definition.  [dio_rel_single] first produces two
    nat-indexed polynomials.  [dio_poly_eq_pos] bounds the auxiliary-variable
    indices, and [dp_proj_par] restricts parameters to the supplied finite
    vector. *)
Theorem dio_rel_Diophantine {n} (R : (nat -> nat) -> Prop) :
  dio_rel R ->
  Diophantine (fun v : Vector.t nat n => R (finiteEnv v)).
Proof.
  intro HR.
  destruct (dio_rel_single HR) as [e He].
  destruct (dio_poly_eq_pos e) as [m [p [q Hpq]]].
  exists m, (dp_proj_par n p), (dp_proj_par n q).
  intro v. cbn.
  rewrite He, Hpq.
  unfold dio_single_pred. cbn.
  split.
  - intros [phi hphi]. exists phi.
    rewrite !dp_proj_par_eval. exact hphi.
  - intros [phi hphi]. exists phi.
    rewrite !dp_proj_par_eval in hphi. exact hphi.
Qed.

(** The standard-library spelling [Nat.pow] and the iterated-multiplication
    spelling used by the Diophantine library compute the same function. *)
Lemma nat_pow_eq_mscal : forall n k,
  Nat.pow n k = mscal mult 1 k n.
Proof.
  intros n k. induction k as [|k IH].
  - reflexivity.
  - cbn [Nat.pow mscal msum]. now rewrite IH.
Qed.

(** The ordinary binary exponentiation function, with base and exponent at
    indices zero and one of its input valuation. *)
Definition NatPowFunction (nu : nat -> nat) : nat :=
  Nat.pow (nu 0) (nu 1).

(** Matiyasevich's theorem at the function-graph interface. *)
Theorem nat_pow_dio_fun : dio_fun NatPowFunction.
Proof.
  apply dio_fun_equiv with
      (r := fun nu => mscal mult 1 (nu 1) (nu 0)).
  - intro nu. apply nat_pow_eq_mscal.
  - apply dio_fun_expo; apply dio_fun_var.
Defined.

(** The parameter order is result, base, exponent.  A [dio_rel] value is a
    dependent pair consisting of explicit formula syntax and a proof that its
    evaluation is equivalent to the displayed relation for every valuation. *)
Theorem PowerNat_dio_rel :
  𝔻R (fun nu => PowerNat (nu 0) (nu 1) (nu 2)).
Proof.
  exact nat_pow_dio_fun.
Defined.

(** A named, inspectable formula witness for the exponentiation graph. *)
Definition powerNatDiophantineFormula : dio_formula :=
  proj1_sig PowerNat_dio_rel.

Theorem powerNatDiophantineFormula_spec : forall nu,
  df_pred powerNatDiophantineFormula nu <->
  PowerNat (nu 0) (nu 1) (nu 2).
Proof.
  exact (proj2_sig PowerNat_dio_rel).
Qed.

(** The same relation represented by a single equality between natural
    polynomials with existentially quantified auxiliary variables. *)
Definition powerNatDiophantineEquation :
  { E : dio_single nat nat |
    forall nu,
      PowerNat (nu 0) (nu 1) (nu 2) <-> dio_single_pred E nu } :=
  dio_rel_single PowerNat_dio_rel.

(** The official finite-vector graph.  Its entries are, in order, the result
    [m], base [n], and exponent [k]. *)
Definition PowerNatVector (v : Vector.t nat 3) : Prop :=
  PowerNat (Vector.nth v Fin.F1)
    (Vector.nth v (Fin.FS Fin.F1))
    (Vector.nth v (Fin.FS (Fin.FS Fin.F1))).

(** Natural-number exponentiation is Diophantine in the standard H10 sense:
    one equality between natural polynomials, with a finite tuple of
    existentially quantified auxiliary variables. *)
Theorem PowerNat_Diophantine :
  Diophantine PowerNatVector.
Proof.
  unfold PowerNatVector, PowerNat.
  change (Diophantine
    (fun v : Vector.t nat 3 =>
      finiteEnv v 0 = Nat.pow (finiteEnv v 1) (finiteEnv v 2))).
  apply (@dio_rel_Diophantine 3
    (fun nu => nu 0 = Nat.pow (nu 1) (nu 2))).
  exact nat_pow_dio_fun.
Qed.

End PAListExponentiationDiophantine.
