(**
  Closure, order, and algebra laws for the epsilon-zero notation codes.

  The executable algorithms live in [EpsilonZero].  This file deliberately
  keeps their longer invariant proofs separate from the coding bijection, so
  the latter remains a small independently checkable kernel boundary.
*)

From Stdlib Require Import Arith Lia Bool PeanoNat.
From PAListCoding Require Import EpsilonZero.

Module PAEpsilonZeroLaws.

Import PAEpsilonZero.

(** * Structural comparison is a strict total order *)

Theorem onoteCompare_lt_trans : forall a b c,
  onoteCompare a b = Lt ->
  onoteCompare b c = Lt ->
  onoteCompare a c = Lt.
Proof.
  induction a as [|ae IHe ac ar IHr]; intros b c hab hbc.
  - destruct b, c; simpl in *; try discriminate; reflexivity.
  - destruct b as [|be bc br]; [simpl in hab; discriminate |].
    destruct c as [|ce cc cr]; [simpl in hbc; discriminate |].
    simpl in hab, hbc |-.
    destruct (onoteCompare ae be) eqn:heab.
    + apply onoteCompare_eq in heab. subst be.
      destruct (onoteCompare ae ce) eqn:heac.
      * apply onoteCompare_eq in heac. subst ce.
        simpl. rewrite onoteCompare_refl.
        destruct (Nat.compare ac bc) eqn:hcab.
        (* Equal first coefficient: the decision moves to the tail.  Compare
           the second coefficient before using tail transitivity. *)
        ++ apply Nat.compare_eq in hcab. subst bc.
           destruct (Nat.compare ac cc) eqn:hcac.
           ** apply Nat.compare_eq in hcac. subst cc.
              exact (IHr br cr hab hbc).
           ** reflexivity.
           ** discriminate.
        (* A smaller first coefficient stays smaller if the middle note is
           below the third one. *)
        ++ destruct (Nat.compare bc cc) eqn:hcbc.
           ** apply Nat.compare_eq in hcbc. subst cc. now rewrite hcab.
           ** apply Nat.compare_lt_iff in hcab.
              apply Nat.compare_lt_iff in hcbc.
              assert (hacc : Nat.compare ac cc = Lt).
              { apply Nat.compare_lt_iff. lia. }
              now rewrite hacc.
           ** discriminate.
        ++ discriminate.
      * simpl. now rewrite heac.
      * discriminate.
    + destruct (onoteCompare be ce) eqn:hebc.
      * apply onoteCompare_eq in hebc. subst ce.
        simpl. now rewrite heab.
      * simpl. rewrite (IHe be ce heab hebc). reflexivity.
      * discriminate.
    + discriminate.
Qed.

Theorem onoteCompare_trichotomy : forall a b,
  onoteCompare a b = Lt \/ a = b \/ onoteCompare b a = Lt.
Proof.
  intros a b.
  destruct (onoteCompare a b) eqn:hcmp.
  - right. left. now apply onoteCompare_eq.
  - now left.
  - right. right. now apply onoteCompare_gt_reverse.
Qed.

Theorem onoteCompare_lt_irrefl : forall a,
  onoteCompare a a <> Lt.
Proof. intros a h. rewrite onoteCompare_refl in h. discriminate. Qed.

End PAEpsilonZeroLaws.
