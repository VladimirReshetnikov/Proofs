From Stdlib Require Import Reals Ring Field Psatz.
From Coquelicot Require Import Complex.
From JacobianConjecture Require Import Counterexample.

Open Scope C_scope.
Import LeanProofs.JacobianCounterexample.

(** The integral collision is one member of an explicit rational family. *)
Module CollisionFamily.

Definition collision_family_0 (t : C) : Point3 :=
  point3 t (-c1 / t) (c5 / (t * t)).

Definition collision_family_1 (t : C) : Point3 :=
  point3 c0 (c2 / t) (-c16 / (t * t)).

Definition collision_family_value (t : C) : Point3 :=
  point3 c0 (c2 / t) c0.

Theorem collision_family_0_value (t : C) (ht : t <> c0) :
  eval_map counterexample (collision_family_0 t) = collision_family_value t.
Proof.
  apply point3_ext;
    cbv [eval_map counterexample collision_family_0 collision_family_value
         counterexample_1 counterexample_2 counterexample_3 Sub
         eval_poly coordinate u one two three four px py pz
         first second third xcoord ycoord zcoord c0 c1 c2 c3 c4 c5];
    field; exact ht.
Qed.

Theorem collision_family_1_value (t : C) (ht : t <> c0) :
  eval_map counterexample (collision_family_1 t) = collision_family_value t.
Proof.
  apply point3_ext;
    cbv [eval_map counterexample collision_family_1 collision_family_value
         counterexample_1 counterexample_2 counterexample_3 Sub
         eval_poly coordinate u one two three four px py pz
         first second third xcoord ycoord zcoord c0 c1 c2 c3 c4 c16];
    field; exact ht.
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

End CollisionFamily.
