(*
  Coq port of the wrapper surface from LeanProofs/FermatFour.lean.

  The Lean file imports mathlib's full descent proof of Fermat's Last Theorem
  for exponent 4 (`not_fermat_42` / `fermatLastTheoremFour`) and exposes two
  small project-local theorem names.  Coq's installed standard/contrib
  libraries do not ship an equivalent theorem.  There is a historical
  self-contained Coq formalization in rocq-archive/coq-contribs `fermat4`,
  but it targets Coq 8.0 and is not a drop-in dependency for Rocq 9.0.

  This module therefore proves the local wrapper layer under an explicit
  descent theorem parameter.  No global axiom is introduced: downstream users
  can instantiate the section with a modernized FLT-4 descent proof.
*)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia Ring.

Open Scope Z_scope.

Module LeanProofs.
Module FermatFour.

Definition Fermat42_descent_statement : Prop :=
  forall a b c : Z,
    a <> 0 ->
    b <> 0 ->
    ~ ((a ^ 4 + b ^ 4)%Z = (c ^ 2)%Z).

Section WithDescent.

Variable no_square_right_int_solutions : Fermat42_descent_statement.

Theorem fermat_four_no_square_right_int_solutions
    {a b c : Z} (ha : a <> 0) (hb : b <> 0) :
    ~ ((a ^ 4 + b ^ 4)%Z = (c ^ 2)%Z).
Proof.
  exact (no_square_right_int_solutions a b c ha hb).
Qed.

Theorem fermat_four_no_positive_nat_solutions
    {a b c : nat}
    (ha : (0 < a)%nat) (hb : (0 < b)%nat) (_hc : (0 < c)%nat) :
    (a ^ 4 + b ^ 4 <> c ^ 4)%nat.
Proof.
  intro hnat.
  pose proof (f_equal Z.of_nat hnat) as hz.
  rewrite Nat2Z.inj_add in hz.
  repeat rewrite Nat2Z.inj_pow in hz.
  change (Z.of_nat 4) with 4 in hz.
  apply (no_square_right_int_solutions
    (Z.of_nat a) (Z.of_nat b) ((Z.of_nat c) ^ 2)).
  - lia.
  - lia.
  - rewrite hz.
    ring.
Qed.

End WithDescent.

End FermatFour.
End LeanProofs.
