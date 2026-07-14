(*
  Coq port of the semantic arithmetic surface of
  PowerTowers/A002845/SparseBinary.lean.

  Lean uses a hereditary sparse-binary tree to avoid materializing enormous
  natural numbers.  Coq already ships a proved binary-natural implementation
  (`N`), so this port uses `N` as the executable sparse carrier and preserves
  the proof-facing surface: evaluation, canonicality, comparison, increment,
  addition, and shifting by a power of two.
*)

From Stdlib Require Import NArith.BinNat.
From Stdlib Require Import NArith.Nnat.

Open Scope N_scope.

Module LeanProofs.
Module A002845.

Definition Sparse : Type := N.

Module Sparse.

Definition eval (x : Sparse) : N := x.

Definition ofN (n : N) : Sparse := n.

Definition ofNat (n : nat) : Sparse := N.of_nat n.

Definition Canonical (_ : Sparse) : Prop := True.

Definition zero : Sparse := 0.

Definition one : Sparse := 1.

Definition beq (x y : Sparse) : bool := N.eqb x y.

Definition compare (x y : Sparse) : comparison := N.compare x y.

Definition incr (x : Sparse) : Sparse := N.succ x.

Definition add (x y : Sparse) : Sparse := x + y.

Definition shift (x b : Sparse) : Sparse := x * 2 ^ b.

Theorem beq_eq {x y : Sparse} : beq x y = true <-> x = y.
Proof.
  apply N.eqb_eq.
Qed.

Theorem eval_ofN (n : N) : eval (ofN n) = n.
Proof. reflexivity. Qed.

Theorem eval_ofNat (n : nat) : eval (ofNat n) = N.of_nat n.
Proof. reflexivity. Qed.

Theorem ofN_injective : forall x y : N, ofN x = ofN y -> x = y.
Proof.
  intros x y h. exact h.
Qed.

Theorem ofNat_injective : forall x y : nat, ofNat x = ofNat y -> x = y.
Proof.
  intros x y h.
  now apply Nat2N.inj_iff.
Qed.

Theorem canonical_ofN (n : N) : Canonical (ofN n).
Proof. exact I. Qed.

Theorem canonical_ofNat (n : nat) : Canonical (ofNat n).
Proof. exact I. Qed.

Theorem canonical_eq_ofN_eval {x : Sparse} (hx : Canonical x) :
    x = ofN (eval x).
Proof. reflexivity. Qed.

Theorem eval_zero : eval zero = 0.
Proof. reflexivity. Qed.

Theorem eval_one : eval one = 1.
Proof. reflexivity. Qed.

Theorem canonical_zero : Canonical zero.
Proof. exact I. Qed.

Theorem canonical_one : Canonical one.
Proof. exact I. Qed.

Theorem compare_iff (x y : Sparse) (hx : Canonical x) (hy : Canonical y) :
    (compare x y = Lt <-> eval x < eval y) /\
    (compare x y = Eq <-> x = y) /\
    (compare x y = Gt <-> eval y < eval x).
Proof.
  repeat split.
  - apply N.compare_lt_iff.
  - apply N.compare_lt_iff.
  - apply N.compare_eq_iff.
  - apply N.compare_eq_iff.
  - apply N.compare_gt_iff.
  - apply N.compare_gt_iff.
Qed.

Theorem incr_spec (x : Sparse) (hx : Canonical x) :
    Canonical (incr x) /\ eval (incr x) = eval x + 1.
Proof.
  split; [exact I | unfold incr, eval; now rewrite N.add_1_r].
Qed.

Theorem add_spec {x y : Sparse} (hx : Canonical x) (hy : Canonical y) :
    Canonical (add x y) /\ eval (add x y) = eval x + eval y.
Proof.
  split; reflexivity.
Qed.

Theorem shift_spec {x b : Sparse} (hx : Canonical x) (hb : Canonical b) :
    Canonical (shift x b) /\ eval (shift x b) = eval x * 2 ^ eval b.
Proof.
  split; reflexivity.
Qed.

Theorem add_eq_ofN {x y : Sparse} (hx : Canonical x) (hy : Canonical y) :
    add x y = ofN (eval x + eval y).
Proof. reflexivity. Qed.

Theorem shift_eq_ofN {x b : Sparse} (hx : Canonical x) (hb : Canonical b) :
    shift x b = ofN (eval x * 2 ^ eval b).
Proof. reflexivity. Qed.

End Sparse.

End A002845.
End LeanProofs.
