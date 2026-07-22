From Stdlib Require Import Reals Ring Field Psatz.
From Coquelicot Require Import Complex.
From JacobianConjecture Require Import Counterexample.

Open Scope C_scope.
Import LeanProofs.JacobianCounterexample.

(**
  The integral collision is one member of an explicit rational family.

  The family interacts with the equivariance of [Counterexample.v]: the
  source involution carries the parameter-[t] member to the parameter-[-t]
  member, so the family is closed under the symmetry, and the [t = -1]
  instance is exactly the denominator-free collision.
*)

Module CollisionFamily.

Definition collision_family_0 (t : C) : Point3 :=
  point3 t (-c1 / t) (c5 / (t * t)).

Definition collision_family_1 (t : C) : Point3 :=
  point3 c0 (c2 / t) (-c16 / (t * t)).

Definition collision_family_value (t : C) : Point3 :=
  point3 c0 (c2 / t) c0.

(** Unfold the family points on top of the shared unfolding tactic. *)
Ltac family_c :=
  cbv [collision_family_0 collision_family_1 collision_family_value];
  eval_c.

Theorem collision_family_0_value (t : C) (ht : t <> c0) :
  eval_map counterexample (collision_family_0 t) = collision_family_value t.
Proof.
  apply point3_ext; family_c; field; exact ht.
Qed.

Theorem collision_family_1_value (t : C) (ht : t <> c0) :
  eval_map counterexample (collision_family_1 t) = collision_family_value t.
Proof.
  apply point3_ext; family_c; field; exact ht.
Qed.

Theorem collision_family (t : C) (ht : t <> c0) :
  eval_map counterexample (collision_family_0 t) =
  eval_map counterexample (collision_family_1 t).
Proof.
  rewrite collision_family_0_value by exact ht.
  rewrite collision_family_1_value by exact ht.
  reflexivity.
Qed.

Theorem collision_family_points_distinct (t : C) (ht : t <> c0) :
  collision_family_0 t <> collision_family_1 t.
Proof.
  intro h.
  apply (f_equal xcoord) in h.
  cbv [collision_family_0 collision_family_1 xcoord] in h.
  exact (ht h).
Qed.

(** **Equivariance of the family.**  The source involution sends the
    parameter-[t] member to the parameter-[-t] member. *)
Theorem collision_family_0_mirror (t : C) (ht : t <> c0) :
  flip_source (collision_family_0 t) = collision_family_0 (- t).
Proof.
  apply point3_ext; family_c; field; repeat split; auto using neq_0_opp.
Qed.

Theorem collision_family_1_mirror (t : C) (ht : t <> c0) :
  flip_source (collision_family_1 t) = collision_family_1 (- t).
Proof.
  apply point3_ext; family_c; field; repeat split; auto using neq_0_opp.
Qed.

Theorem collision_family_value_mirror (t : C) (ht : t <> c0) :
  flip_target (collision_family_value t) = collision_family_value (- t).
Proof.
  apply point3_ext; family_c; field; repeat split; auto using neq_0_opp.
Qed.

(** **The integral collision is the [t = -1] member of the family.** *)
Theorem collision_family_0_at_minus_one :
  collision_family_0 (- c1) = integral_collision_0.
Proof.
  apply point3_ext; family_c; field;
    apply neq_0_opp; apply neq_of_Re; cbv; cbn; lra.
Qed.

Theorem collision_family_1_at_minus_one :
  collision_family_1 (- c1) = integral_collision_1.
Proof.
  apply point3_ext; family_c; field;
    apply neq_0_opp; apply neq_of_Re; cbv; cbn; lra.
Qed.

Theorem collision_family_value_at_minus_one :
  collision_family_value (- c1) = integral_collision_value.
Proof.
  apply point3_ext; family_c; field;
    apply neq_0_opp; apply neq_of_Re; cbv; cbn; lra.
Qed.

End CollisionFamily.
