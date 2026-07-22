From Stdlib Require Import Reals Ring Field Psatz.
From Coquelicot Require Import Complex.
From JacobianConjecture Require Import Counterexample CollisionFamily.

Open Scope C_scope.
Import LeanProofs.JacobianCounterexample.
Import CollisionFamily.

(**
  The weighted torus action behind the discrete symmetry.

  Alpöge's map is homogeneous for the grading [weight (x, y, z) = (-1, 1, 2)]:
  for every nonzero scalar [s],

    [F (x / s, s y, s^2 z) = (s^2 P, s Q, R / s)].

  The flip involutions of [Counterexample.v] are the [s = -1] instance, and
  the rational one-parameter family of [CollisionFamily.v] is exactly the
  orbit of the mirrored integral collision under this action.
*)

Module Scaling.

(** The weight [(-1, 1, 2)] source action. *)
Definition scale_source (s : C) (p : Point3) : Point3 :=
  point3 (xcoord p / s) (s * ycoord p) (s * s * zcoord p).

(** The weight [(2, 1, -1)] target action. *)
Definition scale_target (s : C) (p : Point3) : Point3 :=
  point3 (s * s * xcoord p) (s * ycoord p) (zcoord p / s).

(** **Weighted homogeneity.** *)
Theorem counterexample_scaling (s : C) (hs : s <> c0) (p : Point3) :
  eval_map counterexample (scale_source s p) =
  scale_target s (eval_map counterexample p).
Proof.
  destruct p as [x y z]; apply point3_ext;
    cbv [scale_source scale_target]; eval_c; field; exact hs.
Qed.

(** Scaling preserves collisions. *)
Theorem collision_scaling (s : C) (hs : s <> c0) (p q : Point3)
    (h : eval_map counterexample p = eval_map counterexample q) :
  eval_map counterexample (scale_source s p) =
  eval_map counterexample (scale_source s q).
Proof.
  rewrite !(counterexample_scaling s hs), h; reflexivity.
Qed.

(** The discrete flips are the [s = -1] instance of the action. *)
Theorem flip_source_eq_scale (p : Point3) :
  flip_source p = scale_source (- c1) p.
Proof.
  apply point3_ext; cbv [scale_source]; eval_c; field; re_neq.
Qed.

Theorem flip_target_eq_scale (p : Point3) :
  flip_target p = scale_target (- c1) p.
Proof.
  apply point3_ext; cbv [scale_target]; eval_c; field; re_neq.
Qed.

(** **The family is a torus orbit.**  Scaling the parameter-[t] member by [t]
    recovers the mirrored integral collision, so the whole rational family is
    the orbit of one integral collision under the weighted action. *)
Theorem scale_collision_family_0 (t : C) (ht : t <> c0) :
  scale_source t (collision_family_0 t) = flip_source integral_collision_0.
Proof.
  apply point3_ext; cbv [scale_source]; family_c; field; exact ht.
Qed.

Theorem scale_collision_family_1 (t : C) (ht : t <> c0) :
  scale_source t (collision_family_1 t) = flip_source integral_collision_1.
Proof.
  apply point3_ext; cbv [scale_source]; family_c; field; exact ht.
Qed.

Theorem scale_collision_family_value (t : C) (ht : t <> c0) :
  scale_target t (collision_family_value t) =
  flip_target integral_collision_value.
Proof.
  apply point3_ext; cbv [scale_target]; family_c; field; exact ht.
Qed.

End Scaling.
