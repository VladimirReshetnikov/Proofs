From Stdlib Require Import Reals Ring Field Psatz.
From Coquelicot Require Import Complex.

Open Scope C_scope.

(**
  Shared material for the three- and five-variable Jacobian counterexample
  developments: the named complex constants appearing in the witnesses and
  collisions, and the small facts used to tell explicit complex numbers and
  points apart.
*)

Definition c0 : C := RtoC 0.
Definition c1 : C := RtoC 1.
Definition c2 : C := RtoC 2.
Definition c3 : C := RtoC 3.
Definition c4 : C := RtoC 4.
Definition c5 : C := RtoC 5.
Definition c7 : C := RtoC 7.
Definition c13 : C := RtoC 13.
Definition c16 : C := RtoC 16.

(** Two complex numbers with different real parts are different. *)
Lemma neq_of_Re (z w : C) : Re z <> Re w -> z <> w.
Proof.
  intros hre h; apply hre; rewrite h; reflexivity.
Qed.

(** Negation is nonzero on nonzero inputs. *)
Lemma neq_0_opp (t : C) (ht : t <> c0) : - t <> c0.
Proof.
  intro h0; apply ht.
  destruct t as [a b].
  cbv [c0 RtoC] in h0 |- *; cbn in h0.
  injection h0 as h1 h2.
  f_equal; lra.
Qed.

(** Decide an inequality of two closed complex constants by real parts. *)
Ltac re_neq := apply neq_of_Re; cbv; cbn; lra.
