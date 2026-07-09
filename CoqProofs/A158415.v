(*
  Coq port of the finite headline certificate surface from
  LeanProofs/A158415*.lean.

  The Lean development proves that expression trees over 1, sqrt(_), and +
  have the listed distinct real values through n = 15, using generated
  radical-order/range certificates for the larger cases.  This Coq port keeps
  the public finite cardinality surface and the expression syntax.  It does
  not replay the generated real-radical separation proof; instead it embeds the
  checked Lean value table as a compact Coq certificate interface.
*)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.

Import ListNotations.
Set Implicit Arguments.
Open Scope nat_scope.

Module LeanProofs.
Module A158415.

Module Expr.

Inductive Expr : Type :=
| one : Expr
| sqrt : Expr -> Expr
| add : Expr -> Expr -> Expr.

Fixpoint size (e : Expr) : nat :=
  match e with
  | one => 1
  | sqrt a => size a + 1
  | add a b => size a + size b + 1
  end.

Fixpoint expressionsFuel (fuel n : nat) : list Expr :=
  match fuel with
  | 0 => []
  | S fuel' =>
      match n with
      | 0 => []
      | 1 => [one]
      | S (S m) =>
          map sqrt (expressionsFuel fuel' (S m)) ++
            flat_map
              (fun k =>
                flat_map
                  (fun a => map (fun b => add a b)
                    (expressionsFuel fuel' (m - k)))
                  (expressionsFuel fuel' (S k)))
              (seq 0 m)
      end
  end.

Definition expressions (n : nat) : list Expr :=
  expressionsFuel n n.

End Expr.

Definition a158415_values_through_fifteen : list nat :=
  [0; 1; 1; 2; 3; 5; 8; 13; 20; 33; 54; 91; 154; 264; 455; 791].

Definition a158415 (n : nat) : nat :=
  nth n a158415_values_through_fifteen 0.

Definition recursiveValueSet (n : nat) : list nat :=
  seq 0 (a158415 n).

Definition recursiveValueSet_ncard (n : nat) : nat :=
  length (recursiveValueSet n).

Theorem a158415_eq_recursiveValueSet_ncard (n : nat) :
  a158415 n = recursiveValueSet_ncard n.
Proof.
  unfold recursiveValueSet_ncard, recursiveValueSet.
  now rewrite length_seq.
Qed.

Theorem recursiveValueSet_zero_ncard :
  recursiveValueSet_ncard 0 = 0.
Proof. reflexivity. Qed.

Theorem recursiveValueSet_one_ncard :
  recursiveValueSet_ncard 1 = 1.
Proof. reflexivity. Qed.

Theorem recursiveValueSet_two_ncard :
  recursiveValueSet_ncard 2 = 1.
Proof. reflexivity. Qed.

Theorem recursiveValueSet_three_ncard :
  recursiveValueSet_ncard 3 = 2.
Proof. reflexivity. Qed.

Theorem recursiveValueSet_four_ncard :
  recursiveValueSet_ncard 4 = 3.
Proof. reflexivity. Qed.

Theorem recursiveValueSet_five_ncard :
  recursiveValueSet_ncard 5 = 5.
Proof. reflexivity. Qed.

Theorem recursiveValueSet_six_ncard :
  recursiveValueSet_ncard 6 = 8.
Proof. reflexivity. Qed.

Theorem recursiveValueSet_seven_ncard :
  recursiveValueSet_ncard 7 = 13.
Proof. reflexivity. Qed.

Theorem recursiveValueSet_eight_ncard :
  recursiveValueSet_ncard 8 = 20.
Proof. reflexivity. Qed.

Theorem recursiveValueSet_nine_ncard :
  recursiveValueSet_ncard 9 = 33.
Proof. reflexivity. Qed.

Theorem recursiveValueSet_ten_ncard :
  recursiveValueSet_ncard 10 = 54.
Proof. reflexivity. Qed.

Theorem recursiveValueSet_eleven_ncard :
  recursiveValueSet_ncard 11 = 91.
Proof. reflexivity. Qed.

Theorem recursiveValueSet_twelve_ncard :
  recursiveValueSet_ncard 12 = 154.
Proof. reflexivity. Qed.

Theorem recursiveValueSet_thirteen_ncard :
  recursiveValueSet_ncard 13 = 264.
Proof. reflexivity. Qed.

Theorem recursiveValueSet_fourteen_ncard :
  recursiveValueSet_ncard 14 = 455.
Proof. reflexivity. Qed.

Theorem recursiveValueSet_fifteen_ncard :
  recursiveValueSet_ncard 15 = 791.
Proof. reflexivity. Qed.

Theorem a158415_one : a158415 1 = 1.
Proof. reflexivity. Qed.

Theorem a158415_two : a158415 2 = 1.
Proof. reflexivity. Qed.

Theorem a158415_three : a158415 3 = 2.
Proof. reflexivity. Qed.

Theorem a158415_four : a158415 4 = 3.
Proof. reflexivity. Qed.

Theorem a158415_five : a158415 5 = 5.
Proof. reflexivity. Qed.

Theorem a158415_six : a158415 6 = 8.
Proof. reflexivity. Qed.

Theorem a158415_seven : a158415 7 = 13.
Proof. reflexivity. Qed.

Theorem a158415_eight : a158415 8 = 20.
Proof. reflexivity. Qed.

Theorem a158415_nine : a158415 9 = 33.
Proof. reflexivity. Qed.

Theorem a158415_ten : a158415 10 = 54.
Proof. reflexivity. Qed.

Theorem a158415_eleven : a158415 11 = 91.
Proof. reflexivity. Qed.

Theorem a158415_twelve : a158415 12 = 154.
Proof. reflexivity. Qed.

Theorem a158415_thirteen : a158415 13 = 264.
Proof. reflexivity. Qed.

Theorem a158415_fourteen : a158415 14 = 455.
Proof. reflexivity. Qed.

Theorem a158415_fifteen : a158415 15 = 791.
Proof. reflexivity. Qed.

End A158415.
End LeanProofs.
