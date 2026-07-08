(*
  Coq port of the computational core of LeanProofs/PowTower.lean.

  The Lean module also proves a substantial finset/set-cardinality API around
  this syntax.  This Coq module starts with the shared lexical syntax and
  executable parenthesization/evaluation layer, which is the common base needed
  by the OEIS power-tower ports.
*)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Arith.Wf_nat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
From Stdlib Require Import Setoid.

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

(*
  General equivalence between the lexical evaluation list and the
  split-recursive value list, ported from the Lean theorems
  `valueSet_eq_recursiveValueSet` and `evalFinset_eq_recursiveValueFinset`
  in LeanProofs/PowTower.lean.  The Coq statement is membership-based:
  for every value type with a Boolean equality that decides propositional
  equality, the deduplicated evaluation list and the recursive value list
  contain exactly the same elements, hence have the same length.
*)

Lemma flat_map_ext_In (A B : Type) (f g : A -> list B) (l : list A) :
    (forall a, In a l -> f a = g a) -> flat_map f l = flat_map g l.
Proof.
  induction l as [|a l IHl]; intros H; simpl.
  - reflexivity.
  - rewrite (H a (or_introl eq_refl)).
    f_equal.
    apply IHl.
    intros b Hb.
    apply H.
    right; exact Hb.
Qed.

(* The fuel argument of `parenthesizationsFuel` is irrelevant once it is
   large enough. *)
Lemma parenthesizationsFuel_fuel_irrelevant :
    forall fuel1 fuel2 n, n <= S fuel1 -> n <= S fuel2 ->
      parenthesizationsFuel fuel1 n = parenthesizationsFuel fuel2 n.
Proof.
  induction fuel1 as [|fuel1 IH]; intros fuel2 n H1 H2.
  - destruct n as [|[|n]].
    + destruct fuel2; reflexivity.
    + destruct fuel2; reflexivity.
    + lia.
  - destruct n as [|[|n]].
    + destruct fuel2; reflexivity.
    + destruct fuel2; reflexivity.
    + destruct fuel2 as [|fuel2]; [lia|].
      cbn [parenthesizationsFuel].
      apply flat_map_ext_In; intros k Hk.
      apply in_seq in Hk; destruct Hk as [_ Hk].
      assert (E1 : parenthesizationsFuel fuel1 (S k) =
                     parenthesizationsFuel fuel2 (S k))
        by (apply IH; lia).
      assert (E2 : parenthesizationsFuel fuel1 (S n - k) =
                     parenthesizationsFuel fuel2 (S n - k))
        by (apply IH; lia).
      rewrite E1, E2.
      reflexivity.
Qed.

(* The split recurrence satisfied by `parenthesizations`. *)
Lemma parenthesizations_step (n : nat) :
    parenthesizations (S (S n)) =
      flat_map (fun k =>
        flat_map (fun a =>
          map (fun b => pow a b) (parenthesizations (S n - k)))
          (parenthesizations (S k)))
        (seq 0 (S n)).
Proof.
  transitivity
    (flat_map (fun k =>
       flat_map (fun a =>
         map (fun b => pow a b) (parenthesizationsFuel (S n) (S n - k)))
         (parenthesizationsFuel (S n) (S k)))
       (seq 0 (S n))).
  { reflexivity. }
  apply flat_map_ext_In; intros k Hk.
  apply in_seq in Hk; destruct Hk as [_ Hk].
  unfold parenthesizations.
  assert (E1 : parenthesizationsFuel (S n) (S k) =
                 parenthesizationsFuel (S k) (S k))
    by (apply parenthesizationsFuel_fuel_irrelevant; lia).
  assert (E2 : parenthesizationsFuel (S n) (S n - k) =
                 parenthesizationsFuel (S n - k) (S n - k))
    by (apply parenthesizationsFuel_fuel_irrelevant; lia).
  rewrite E1, E2.
  reflexivity.
Qed.

(* The fuel argument of `recursiveValueListFuel` is irrelevant once it is
   large enough. *)
Lemma recursiveValueListFuel_fuel_irrelevant (A : Type)
    (eqb : A -> A -> bool) (atomValue : A) (powValue : A -> A -> A) :
    forall fuel1 fuel2 n, n <= S fuel1 -> n <= S fuel2 ->
      recursiveValueListFuel fuel1 eqb atomValue powValue n =
        recursiveValueListFuel fuel2 eqb atomValue powValue n.
Proof.
  induction fuel1 as [|fuel1 IH]; intros fuel2 n H1 H2.
  - destruct n as [|[|n]].
    + destruct fuel2; reflexivity.
    + destruct fuel2; reflexivity.
    + lia.
  - destruct n as [|[|n]].
    + destruct fuel2; reflexivity.
    + destruct fuel2; reflexivity.
    + destruct fuel2 as [|fuel2]; [lia|].
      cbn [recursiveValueListFuel].
      f_equal.
      apply flat_map_ext_In; intros k Hk.
      apply in_seq in Hk; destruct Hk as [_ Hk].
      assert (E1 : recursiveValueListFuel fuel1 eqb atomValue powValue (S k) =
                     recursiveValueListFuel fuel2 eqb atomValue powValue (S k))
        by (apply IH; lia).
      assert (E2 :
          recursiveValueListFuel fuel1 eqb atomValue powValue (S n - k) =
            recursiveValueListFuel fuel2 eqb atomValue powValue (S n - k))
        by (apply IH; lia).
      rewrite E1, E2.
      reflexivity.
Qed.

(* The split recurrence satisfied by `recursiveValueList`. *)
Lemma recursiveValueList_step (A : Type) (eqb : A -> A -> bool)
    (atomValue : A) (powValue : A -> A -> A) (n : nat) :
    recursiveValueList eqb atomValue powValue (S (S n)) =
      dedupBy eqb
        (flat_map (fun k =>
          combineLevel powValue
            (recursiveValueList eqb atomValue powValue (S k))
            (recursiveValueList eqb atomValue powValue (S n - k)))
          (seq 0 (S n))).
Proof.
  transitivity
    (dedupBy eqb
      (flat_map (fun k =>
        combineLevel powValue
          (recursiveValueListFuel (S n) eqb atomValue powValue (S k))
          (recursiveValueListFuel (S n) eqb atomValue powValue (S n - k)))
        (seq 0 (S n)))).
  { reflexivity. }
  f_equal.
  apply flat_map_ext_In; intros k Hk.
  apply in_seq in Hk; destruct Hk as [_ Hk].
  unfold recursiveValueList.
  assert (E1 : recursiveValueListFuel (S n) eqb atomValue powValue (S k) =
                 recursiveValueListFuel (S k) eqb atomValue powValue (S k))
    by (apply recursiveValueListFuel_fuel_irrelevant; lia).
  assert (E2 :
      recursiveValueListFuel (S n) eqb atomValue powValue (S n - k) =
        recursiveValueListFuel (S n - k) eqb atomValue powValue (S n - k))
    by (apply recursiveValueListFuel_fuel_irrelevant; lia).
  rewrite E1, E2.
  reflexivity.
Qed.

Lemma NoDup_length_eq (A : Type) (l l' : list A) :
    NoDup l -> NoDup l' -> (forall x, In x l <-> In x l') ->
    length l = length l'.
Proof.
  intros Hl Hl' Hiff.
  apply Nat.le_antisymm.
  - apply NoDup_incl_length; [exact Hl|].
    intros x Hx; apply Hiff; exact Hx.
  - apply NoDup_incl_length; [exact Hl'|].
    intros x Hx; apply Hiff; exact Hx.
Qed.

Section ParenthesizationRecursiveEquivalence.

Variable A : Type.
Variable eqb : A -> A -> bool.
Variable atomValue : A.
Variable powValue : A -> A -> A.
Hypothesis eqb_spec : forall x y : A, eqb x y = true <-> x = y.

Lemma memberBy_true_iff (x : A) (l : list A) :
    memberBy eqb x l = true <-> In x l.
Proof.
  induction l as [|y l IHl]; simpl.
  - split; [discriminate|tauto].
  - rewrite Bool.orb_true_iff, IHl, eqb_spec.
    split; intros [H|H]; auto.
Qed.

Lemma In_dedupBy (l : list A) (x : A) :
    In x (dedupBy eqb l) <-> In x l.
Proof.
  induction l as [|a l IHl]; simpl.
  - tauto.
  - unfold insertBy.
    destruct (memberBy eqb a (dedupBy eqb l)) eqn:E.
    + apply memberBy_true_iff in E.
      rewrite IHl.
      split.
      * tauto.
      * intros [Ha|Hx]; [subst a; apply IHl in E; exact E|exact Hx].
    + simpl.
      rewrite IHl.
      tauto.
Qed.

Lemma NoDup_dedupBy (l : list A) : NoDup (dedupBy eqb l).
Proof.
  induction l as [|a l IHl]; simpl.
  - constructor.
  - unfold insertBy.
    destruct (memberBy eqb a (dedupBy eqb l)) eqn:E.
    + exact IHl.
    + constructor; [|exact IHl].
      intros Hin.
      apply memberBy_true_iff in Hin.
      rewrite Hin in E.
      discriminate.
Qed.

(*
  The general theorem, ported from Lean's `valueSet_eq_recursiveValueSet`:
  a value is produced by some parenthesization of a power tower of `n`
  atoms if and only if it appears in the split-recursive value list.
*)
Theorem In_evalList_iff_recursiveValueList :
    forall n x,
      In x (evalList (eval atomValue powValue) n) <->
      In x (recursiveValueList eqb atomValue powValue n).
Proof.
  intros n.
  induction n as [n IH] using lt_wf_ind; intros x.
  destruct n as [|[|n]].
  - simpl; tauto.
  - simpl; tauto.
  - unfold evalList.
    rewrite parenthesizations_step, recursiveValueList_step, In_dedupBy.
    split.
    + intros H.
      apply in_map_iff in H; destruct H as [e [He Hin]].
      apply in_flat_map in Hin; destruct Hin as [k [Hk Hin]].
      apply in_flat_map in Hin; destruct Hin as [a [Ha Hin]].
      apply in_map_iff in Hin; destruct Hin as [b [Hb Hbin]].
      subst e.
      simpl in He.
      assert (Hk' := Hk); apply in_seq in Hk'; destruct Hk' as [_ Hk'].
      apply in_flat_map.
      exists k; split; [exact Hk|].
      unfold combineLevel.
      apply in_flat_map.
      exists (eval atomValue powValue a); split.
      * apply (IH (S k)); [lia|].
        unfold evalList; apply in_map; exact Ha.
      * apply in_map_iff.
        exists (eval atomValue powValue b); split; [exact He|].
        apply (IH (S n - k)); [lia|].
        unfold evalList; apply in_map; exact Hbin.
    + intros H.
      apply in_flat_map in H; destruct H as [k [Hk Hin]].
      assert (Hk' := Hk); apply in_seq in Hk'; destruct Hk' as [_ Hk'].
      unfold combineLevel in Hin.
      apply in_flat_map in Hin; destruct Hin as [va [Hva Hin]].
      apply in_map_iff in Hin; destruct Hin as [vb [Hvb Hvbin]].
      apply (IH (S k)) in Hva; [|lia].
      apply (IH (S n - k)) in Hvbin; [|lia].
      unfold evalList in Hva, Hvbin.
      apply in_map_iff in Hva; destruct Hva as [a [Ha Hain]].
      apply in_map_iff in Hvbin; destruct Hvbin as [b [Hb Hbin]].
      apply in_map_iff.
      exists (pow a b); split.
      * simpl; rewrite Ha, Hb; exact Hvb.
      * apply in_flat_map.
        exists k; split; [exact Hk|].
        apply in_flat_map.
        exists a; split; [exact Hain|].
        apply in_map_iff.
        exists b; split; [reflexivity|exact Hbin].
Qed.

Lemma NoDup_recursiveValueList (n : nat) :
    NoDup (recursiveValueList eqb atomValue powValue n).
Proof.
  destruct n as [|[|n]].
  - constructor.
  - constructor; [simpl; tauto|constructor].
  - rewrite recursiveValueList_step.
    apply NoDup_dedupBy.
Qed.

(*
  Ported counting consequence (Lean's `evalFinset_eq_recursiveValueFinset`
  plus cardinality): the number of distinct values of all parenthesizations
  equals the length of the split-recursive value list.  This is the theorem
  the OEIS certificates need: the recurrence output counts genuine distinct
  parenthesization values for every `n`.
*)
Theorem valueCount_eq_recursiveValueList_length (n : nat) :
    valueCount eqb (eval atomValue powValue) n =
      length (recursiveValueList eqb atomValue powValue n).
Proof.
  unfold valueCount, valueList.
  apply NoDup_length_eq.
  - apply NoDup_dedupBy.
  - apply NoDup_recursiveValueList.
  - intros x.
    rewrite In_dedupBy.
    apply In_evalList_iff_recursiveValueList.
Qed.

(* Dedup-on-both-sides formulation of the same count equality. *)
Corollary dedup_evalList_length_eq_dedup_recursiveValueList_length (n : nat) :
    length (dedupBy eqb (evalList (eval atomValue powValue) n)) =
      length (dedupBy eqb (recursiveValueList eqb atomValue powValue n)).
Proof.
  apply NoDup_length_eq; try apply NoDup_dedupBy.
  intros x.
  rewrite !In_dedupBy.
  apply In_evalList_iff_recursiveValueList.
Qed.

End ParenthesizationRecursiveEquivalence.

(* Instantiation at `nat`, generalizing the `n <= 3` instance check below
   to every tower size. *)
Theorem parenthesization_values_match_recursive_nat
    (atomValue : nat) (powValue : nat -> nat -> nat) (n : nat) :
    valueCount Nat.eqb (eval atomValue powValue) n =
      length (recursiveValueList Nat.eqb atomValue powValue n).
Proof.
  apply valueCount_eq_recursiveValueList_length.
  intros x y; apply Nat.eqb_eq.
Qed.

End PowTower.
End LeanProofs.
