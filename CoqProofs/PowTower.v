(*
  Coq port of the computational core of LeanProofs/PowTower.lean.

  The Lean module also proves a substantial finset/set-cardinality API around
  this syntax.  This Coq module starts with the shared lexical syntax and
  executable parenthesization/evaluation layer, which is the common base needed
  by the OEIS power-tower ports.
*)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.

Import ListNotations.

Set Implicit Arguments.

Module LeanProofs.
Module PowTower.

Inductive Expr : Type :=
| atom : Expr
| pow : Expr -> Expr -> Expr.

Fixpoint exprEqb (x y : Expr) : bool :=
  match x, y with
  | atom, atom => true
  | pow xl xr, pow yl yr => exprEqb xl yl && exprEqb xr yr
  | _, _ => false
  end.

Theorem exprEqb_refl (e : Expr) : exprEqb e e = true.
Proof.
  induction e; simpl; auto.
  now rewrite IHe1, IHe2.
Qed.

Fixpoint size (e : Expr) : nat :=
  match e with
  | atom => 1
  | pow a b => size a + size b
  end.

Fixpoint parenthesizationsFuel (fuel n : nat) : list Expr :=
  match fuel with
  | 0 =>
      match n with
      | 1 => [atom]
      | _ => []
      end
  | S fuel' =>
      match n with
      | 0 => []
      | 1 => [atom]
      | S (S n') =>
          flat_map (fun k =>
            flat_map (fun a =>
              map (fun b => pow a b)
                (parenthesizationsFuel fuel' (S n' - k)))
              (parenthesizationsFuel fuel' (S k)))
            (seq 0 (S n'))
      end
  end.

Definition parenthesizations (n : nat) : list Expr :=
  parenthesizationsFuel n n.

Theorem parenthesizations_zero :
    parenthesizations 0 = [].
Proof. reflexivity. Qed.

Theorem parenthesizations_one :
    parenthesizations 1 = [atom].
Proof. reflexivity. Qed.

Theorem parenthesizations_two :
    parenthesizations 2 = [pow atom atom].
Proof. reflexivity. Qed.

Theorem parenthesizations_three :
    parenthesizations 3 =
      [pow atom (pow atom atom); pow (pow atom atom) atom].
Proof. reflexivity. Qed.

Theorem parenthesizations_four :
    parenthesizations 4 =
      [ pow atom (pow atom (pow atom atom));
        pow atom (pow (pow atom atom) atom);
        pow (pow atom atom) (pow atom atom);
        pow (pow atom (pow atom atom)) atom;
        pow (pow (pow atom atom) atom) atom ].
Proof. reflexivity. Qed.

Fixpoint eval {A : Type} (atomValue : A) (powValue : A -> A -> A)
    (e : Expr) : A :=
  match e with
  | atom => atomValue
  | pow a b => powValue (eval atomValue powValue a) (eval atomValue powValue b)
  end.

Fixpoint memberBy {A : Type} (eqb : A -> A -> bool) (x : A)
    (xs : list A) : bool :=
  match xs with
  | [] => false
  | y :: ys => eqb x y || memberBy eqb x ys
  end.

Definition insertBy {A : Type} (eqb : A -> A -> bool) (x : A)
    (xs : list A) : list A :=
  if memberBy eqb x xs then xs else x :: xs.

Fixpoint dedupBy {A : Type} (eqb : A -> A -> bool) (xs : list A) : list A :=
  match xs with
  | [] => []
  | x :: rest => insertBy eqb x (dedupBy eqb rest)
  end.

Definition evalList {A : Type} (evalFn : Expr -> A) (n : nat) : list A :=
  map evalFn (parenthesizations n).

Definition valueList {A : Type} (eqb : A -> A -> bool)
    (evalFn : Expr -> A) (n : nat) : list A :=
  dedupBy eqb (evalList evalFn n).

Definition valueCount {A : Type} (eqb : A -> A -> bool)
    (evalFn : Expr -> A) (n : nat) : nat :=
  length (valueList eqb evalFn n).

Definition combineLevel {A : Type} (powValue : A -> A -> A)
    (left right : list A) : list A :=
  flat_map (fun a => map (fun b => powValue a b) right) left.

Fixpoint recursiveValueListFuel {A : Type} (fuel : nat)
    (eqb : A -> A -> bool) (atomValue : A) (powValue : A -> A -> A)
    (n : nat) : list A :=
  match fuel with
  | 0 =>
      match n with
      | 1 => [atomValue]
      | _ => []
      end
  | S fuel' =>
      match n with
      | 0 => []
      | 1 => [atomValue]
      | S (S n') =>
          dedupBy eqb
            (flat_map (fun k =>
              combineLevel powValue
                (recursiveValueListFuel fuel' eqb atomValue powValue (S k))
                (recursiveValueListFuel fuel' eqb atomValue powValue (S n' - k)))
              (seq 0 (S n')))
      end
  end.

Definition recursiveValueList {A : Type} (eqb : A -> A -> bool)
    (atomValue : A) (powValue : A -> A -> A) (n : nat) : list A :=
  recursiveValueListFuel n eqb atomValue powValue n.

Theorem parenthesization_values_match_recursive_small_nat
    (atomValue : nat) (powValue : nat -> nat -> nat) :
    valueCount Nat.eqb (eval atomValue powValue) 0 =
      length (recursiveValueList Nat.eqb atomValue powValue 0) /\
    valueCount Nat.eqb (eval atomValue powValue) 1 =
      length (recursiveValueList Nat.eqb atomValue powValue 1) /\
    valueCount Nat.eqb (eval atomValue powValue) 2 =
      length (recursiveValueList Nat.eqb atomValue powValue 2) /\
    valueCount Nat.eqb (eval atomValue powValue) 3 =
      length (recursiveValueList Nat.eqb atomValue powValue 3).
Proof.
  repeat split; vm_compute; reflexivity.
Qed.

End PowTower.
End LeanProofs.
