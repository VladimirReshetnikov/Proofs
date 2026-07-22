From Stdlib Require Import Reals Ring Field Psatz.
From Coquelicot Require Import Complex.

Open Scope C_scope.

(**
  Alpöge's dimension-three counterexample to the Jacobian conjecture.

  [Poly3] is a deliberately small syntax of complex polynomials.  [partial]
  is formal differentiation (including the product rule), and [jacobian_det]
  is the ordinary three-by-three determinant in that syntax.  Thus the
  theorem below checks a formal polynomial Jacobian, not an analytic or
  externally computed derivative.

  Polynomial equality is interpreted extensionally over Coquelicot's complex
  field [C].  Since [C] is infinite, this is the usual equality of polynomial
  functions.  The conjecture asks for a two-sided inverse represented by
  another [PolyMap3]; the explicit collision rules out even a set-theoretic
  left inverse.
*)

Module LeanProofs.
Module JacobianCounterexample.

Definition c0 : C := RtoC 0.
Definition c1 : C := RtoC 1.
Definition c2 : C := RtoC 2.
Definition c3 : C := RtoC 3.
Definition c4 : C := RtoC 4.
Definition c5 : C := RtoC 5.
Definition c13 : C := RtoC 13.
Definition c16 : C := RtoC 16.

Inductive Var3 : Type := VX | VY | VZ.

Definition var_eqb (i j : Var3) : bool :=
  match i, j with
  | VX, VX | VY, VY | VZ, VZ => true
  | _, _ => false
  end.

Inductive Poly3 : Type :=
| Const (c : C)
| Var (i : Var3)
| Add (p q : Poly3)
| Mul (p q : Poly3)
| Opp (p : Poly3).

Record Point3 : Type := point3 {
  xcoord : C;
  ycoord : C;
  zcoord : C
}.

Definition coordinate (i : Var3) (p : Point3) : C :=
  match i with
  | VX => xcoord p
  | VY => ycoord p
  | VZ => zcoord p
  end.

Fixpoint eval_poly (p : Poly3) (a : Point3) : C :=
  match p with
  | Const c => c
  | Var i => coordinate i a
  | Add p q => eval_poly p a + eval_poly q a
  | Mul p q => eval_poly p a * eval_poly q a
  | Opp p => - eval_poly p a
  end.

Fixpoint partial (i : Var3) (p : Poly3) : Poly3 :=
  match p with
  | Const _ => Const c0
  | Var j => Const (if var_eqb i j then c1 else c0)
  | Add p q => Add (partial i p) (partial i q)
  | Mul p q => Add (Mul (partial i p) q) (Mul p (partial i q))
  | Opp p => Opp (partial i p)
  end.

Definition Sub (p q : Poly3) : Poly3 := Add p (Opp q).

Definition one : Poly3 := Const c1.
Definition two : Poly3 := Const c2.
Definition three : Poly3 := Const c3.
Definition four : Poly3 := Const c4.
Definition px : Poly3 := Var VX.
Definition py : Poly3 := Var VY.
Definition pz : Poly3 := Var VZ.

Definition u : Poly3 := Add one (Mul px py).

Definition counterexample_1 : Poly3 :=
  Add (Mul (Mul (Mul u u) u) pz)
      (Mul (Mul (Mul py py) u)
           (Add four (Mul (Mul three px) py))).

Definition counterexample_2 : Poly3 :=
  Add py
      (Add (Mul (Mul (Mul three px) (Mul u u)) pz)
           (Mul (Mul (Mul (Mul three px) py) py)
                (Add four (Mul (Mul three px) py)))).

Definition counterexample_3 : Poly3 :=
  Sub (Sub (Mul two px) (Mul (Mul (Mul three px) px) py))
      (Mul (Mul (Mul px px) px) pz).

Record PolyMap3 : Type := poly_map3 {
  first : Poly3;
  second : Poly3;
  third : Poly3
}.

Definition counterexample : PolyMap3 :=
  poly_map3 counterexample_1 counterexample_2 counterexample_3.

Definition eval_map (f : PolyMap3) (p : Point3) : Point3 :=
  point3 (eval_poly (first f) p)
         (eval_poly (second f) p)
         (eval_poly (third f) p).

Definition det3
    (a11 a12 a13 a21 a22 a23 a31 a32 a33 : Poly3) : Poly3 :=
  Add
    (Sub
      (Mul a11 (Sub (Mul a22 a33) (Mul a23 a32)))
      (Mul a12 (Sub (Mul a21 a33) (Mul a23 a31))))
    (Mul a13 (Sub (Mul a21 a32) (Mul a22 a31))).

Definition jacobian_det (f : PolyMap3) : Poly3 :=
  det3
    (partial VX (first f))  (partial VY (first f))  (partial VZ (first f))
    (partial VX (second f)) (partial VY (second f)) (partial VZ (second f))
    (partial VX (third f))  (partial VY (third f))  (partial VZ (third f)).

Lemma point3_ext (p q : Point3) :
  xcoord p = xcoord q ->
  ycoord p = ycoord q ->
  zcoord p = zcoord q ->
  p = q.
Proof.
  destruct p as [x y z], q as [x' y' z']; cbn.
  intros; subst; reflexivity.
Qed.

Theorem jacobian_det_is_minus_two (p : Point3) :
  eval_poly (jacobian_det counterexample) p = - c2.
Proof.
  destruct p as [x y z].
  cbv [jacobian_det counterexample det3 counterexample_1
       counterexample_2 counterexample_3 Sub partial var_eqb
       eval_poly coordinate u one two three four px py pz
       first second third xcoord ycoord zcoord c0 c1 c2 c3 c4].
  ring.
Qed.

Definition collision_0 : Point3 := point3 c0 c0 (-c1 / c4).
Definition collision_1 : Point3 := point3 c1 (-c3 / c2) (c13 / c2).
Definition collision_2 : Point3 := point3 (-c1) (c3 / c2) (c13 / c2).
Definition collision_value : Point3 := point3 (-c1 / c4) c0 c0.

Theorem collision_0_value :
  eval_map counterexample collision_0 = collision_value.
Proof.
  apply point3_ext;
    cbv [eval_map counterexample collision_0 collision_value
         counterexample_1 counterexample_2 counterexample_3 Sub
         eval_poly coordinate u one two three four px py pz
         first second third xcoord ycoord zcoord c0 c1 c2 c3 c4 c13];
    field.
Qed.

Theorem collision_1_value :
  eval_map counterexample collision_1 = collision_value.
Proof.
  apply point3_ext;
    cbv [eval_map counterexample collision_1 collision_value
         counterexample_1 counterexample_2 counterexample_3 Sub
         eval_poly coordinate u one two three four px py pz
         first second third xcoord ycoord zcoord c0 c1 c2 c3 c4 c13]; field.
Qed.

Theorem collision_2_value :
  eval_map counterexample collision_2 = collision_value.
Proof.
  apply point3_ext;
    cbv [eval_map counterexample collision_2 collision_value
         counterexample_1 counterexample_2 counterexample_3 Sub
         eval_poly coordinate u one two three four px py pz
         first second third xcoord ycoord zcoord c0 c1 c2 c3 c4 c13]; field.
Qed.

Theorem collision_points_distinct :
  collision_0 <> collision_1 /\
  collision_0 <> collision_2 /\
  collision_1 <> collision_2.
Proof.
  repeat split; intro h;
    apply (f_equal xcoord) in h;
    apply (f_equal Re) in h;
    cbv [collision_0 collision_1 collision_2 xcoord c0 c1 RtoC Copp Re] in h.
  all: cbn in h; lra.
Qed.

(** A second, denominator-free collision. *)
Definition integral_collision_0 : Point3 := point3 (-c1) c1 c5.
Definition integral_collision_1 : Point3 := point3 c0 (-c2) (-c16).
Definition integral_collision_value : Point3 := point3 c0 (-c2) c0.

Theorem integral_collision_0_value :
  eval_map counterexample integral_collision_0 = integral_collision_value.
Proof.
  apply point3_ext;
    cbv [eval_map counterexample integral_collision_0 integral_collision_value
         counterexample_1 counterexample_2 counterexample_3 Sub
         eval_poly coordinate u one two three four px py pz
         first second third xcoord ycoord zcoord
         c0 c1 c2 c3 c4 c5 c13 c16];
    ring.
Qed.

Theorem integral_collision_1_value :
  eval_map counterexample integral_collision_1 = integral_collision_value.
Proof.
  apply point3_ext;
    cbv [eval_map counterexample integral_collision_1 integral_collision_value
         counterexample_1 counterexample_2 counterexample_3 Sub
         eval_poly coordinate u one two three four px py pz
         first second third xcoord ycoord zcoord
         c0 c1 c2 c3 c4 c5 c13 c16];
    ring.
Qed.

Theorem integral_collision_points_distinct :
  integral_collision_0 <> integral_collision_1.
Proof.
  intro h.
  apply (f_equal xcoord) in h.
  apply (f_equal Re) in h.
  cbv [integral_collision_0 integral_collision_1 xcoord c0 c1 RtoC Copp Re] in h.
  cbn in h.
  lra.
Qed.

Definition PolynomialEq (p q : Poly3) : Prop :=
  forall a : Point3, eval_poly p a = eval_poly q a.

Definition HasNonzeroConstantJacobian (f : PolyMap3) : Prop :=
  exists c : C,
    c <> c0 /\ PolynomialEq (jacobian_det f) (Const c).

Definition HasPolynomialInverse (f : PolyMap3) : Prop :=
  exists g : PolyMap3,
    (forall p : Point3, eval_map g (eval_map f p) = p) /\
    (forall p : Point3, eval_map f (eval_map g p) = p).

Definition JacobianConjectureInDimensionThreeOverC : Prop :=
  forall f : PolyMap3,
    HasNonzeroConstantJacobian f -> HasPolynomialInverse f.

Definition JacobianConjecture3C : Prop :=
  JacobianConjectureInDimensionThreeOverC.

Theorem counterexample_has_nonzero_constant_jacobian :
  HasNonzeroConstantJacobian counterexample.
Proof.
  exists (-c2).
  split.
  - intro h.
    apply (f_equal Re) in h.
    cbv [c0 c2 RtoC Copp Re] in h.
    cbn in h.
    lra.
  - intro p.
    cbn [eval_poly].
    exact (jacobian_det_is_minus_two p).
Qed.

Theorem counterexample_not_injective :
  ~ (forall p q : Point3,
       eval_map counterexample p = eval_map counterexample q -> p = q).
Proof.
  intro hinj.
  pose proof (proj1 collision_points_distinct) as hne.
  apply hne.
  apply hinj.
  rewrite collision_0_value, collision_1_value.
  reflexivity.
Qed.

Theorem counterexample_has_no_polynomial_inverse :
  ~ HasPolynomialInverse counterexample.
Proof.
  intros [g [hleft _]].
  pose proof (proj1 collision_points_distinct) as hne.
  apply hne.
  rewrite <- (hleft collision_0), <- (hleft collision_1).
  rewrite collision_0_value, collision_1_value.
  reflexivity.
Qed.

Theorem jacobian_conjecture_dimension_three_is_false :
  ~ JacobianConjectureInDimensionThreeOverC.
Proof.
  intro h.
  apply counterexample_has_no_polynomial_inverse.
  apply h.
  exact counterexample_has_nonzero_constant_jacobian.
Qed.

End JacobianCounterexample.
End LeanProofs.
