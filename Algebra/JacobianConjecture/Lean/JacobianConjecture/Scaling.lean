import JacobianConjecture.Equivariance

/-!
# The weighted torus action behind the discrete symmetry

Alpöge's map is homogeneous for the grading `weight (x, y, z) = (-1, 1, 2)`:
for every nonzero scalar `s`,

```text
F (x / s, s y, s² z) = (s² P, s Q, R / s).
```

The flip involutions of `Equivariance` are the `s = -1` instance, and the
rational one-parameter family of `CollisionFamily` is exactly the orbit of
the mirrored integral collision under this action.
-/

namespace LeanProofs.JacobianCounterexample

open Matrix MvPolynomial PolynomialMap

universe u

/-- The weight `(-1, 1, 2)` source action. -/
def scaleSource {R : Type u} [Field R] (s : R) (p : I → R) : I → R :=
  ![p 0 / s, s * p 1, s ^ 2 * p 2]

/-- The weight `(2, 1, -1)` target action. -/
def scaleTarget {R : Type u} [Field R] (s : R) (v : I → R) : I → R :=
  ![s ^ 2 * v 0, s * v 1, v 2 / s]

set_option maxHeartbeats 800000 in
/-- **Weighted homogeneity.** `F (x/s, sy, s²z) = (s²P, sQ, R/s)`. -/
theorem counterexample_scaling
    {R : Type u} [Field R] (s : R) (hs : s ≠ 0) (p : I → R) :
    evalMap (counterexample R) (scaleSource s p) =
      scaleTarget s (evalMap (counterexample R) p) := by
  funext i
  fin_cases i <;>
    simp [evalMap, counterexample, scaleSource, scaleTarget,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] <;>
    field_simp

/-- Scaling preserves collisions. -/
theorem collision_scaling
    {R : Type u} [Field R] (s : R) (hs : s ≠ 0) (p q : I → R)
    (h : evalMap (counterexample R) p = evalMap (counterexample R) q) :
    evalMap (counterexample R) (scaleSource s p) =
      evalMap (counterexample R) (scaleSource s q) := by
  rw [counterexample_scaling s hs, counterexample_scaling s hs, h]

/-- The discrete source flip is the `s = -1` instance of the action. -/
theorem flipSource_eq_scale {R : Type u} [Field R] (p : I → R) :
    flipSource p = scaleSource (-1) p := by
  funext i
  fin_cases i <;>
    norm_num [flipSource, scaleSource, div_neg, div_one,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]

/-- The discrete target flip is the `s = -1` instance of the action. -/
theorem flipTarget_eq_scale {R : Type u} [Field R] (v : I → R) :
    flipTarget v = scaleTarget (-1) v := by
  funext i
  fin_cases i <;>
    norm_num [flipTarget, scaleTarget, div_neg, div_one,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]

/-!
## The family is a torus orbit

Scaling the parameter-`t` member by `t` recovers the mirrored integral
collision, so the whole rational family is the orbit of one integral
collision under the weighted action.
-/

theorem scale_collisionFamily₀ {R : Type u} [Field R] (t : R) (ht : t ≠ 0) :
    scaleSource t (collisionFamily₀ R t) = flipSource (collision₀ R) := by
  funext i
  fin_cases i <;>
    simp [scaleSource, collisionFamily₀, flipSource, collision₀,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] <;>
    first
      | exact ht
      | field_simp

theorem scale_collisionFamily₁ {R : Type u} [Field R] (t : R) (ht : t ≠ 0) :
    scaleSource t (collisionFamily₁ R t) = flipSource (collision₁ R) := by
  funext i
  fin_cases i <;>
    simp [scaleSource, collisionFamily₁, flipSource, collision₁,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] <;>
    first
      | exact ht
      | field_simp

theorem scale_collisionFamilyValue {R : Type u} [Field R] (t : R) (ht : t ≠ 0) :
    scaleTarget t (collisionFamilyValue R t) = flipTarget (collisionValue R) := by
  funext i
  fin_cases i <;>
    simp [scaleTarget, collisionFamilyValue, flipTarget, collisionValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
  field_simp

end LeanProofs.JacobianCounterexample
