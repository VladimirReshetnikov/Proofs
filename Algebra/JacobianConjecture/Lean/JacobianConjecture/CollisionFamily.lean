import JacobianConjecture.Counterexample
import Mathlib.Tactic.FieldSimp

/-!
# A one-parameter family of collisions

The integral collision used by the main proof is the `t = -1` member of this
family.  Thus the counterexample is noninjective along an explicit rational
one-parameter family, not merely at an isolated pair of points.
-/

namespace LeanProofs.JacobianCounterexample

open Matrix MvPolynomial PolynomialMap

def collisionFamily₀ (R : Type*) [Field R] (t : R) : I → R :=
  ![t, -1 / t, 5 / t ^ 2]

def collisionFamily₁ (R : Type*) [Field R] (t : R) : I → R :=
  ![0, 2 / t, -16 / t ^ 2]

def collisionFamilyValue (R : Type*) [Field R] (t : R) : I → R :=
  ![0, 2 / t, 0]

theorem collisionFamily₀_value (R : Type*) [Field R] (t : R) (ht : t ≠ 0) :
    evalMap (counterexample R) (collisionFamily₀ R t) =
      collisionFamilyValue R t := by
  funext i
  fin_cases i
  all_goals simp [evalMap, counterexample, collisionFamily₀, collisionFamilyValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  all_goals field_simp [ht]
  all_goals ring

theorem collisionFamily₁_value (R : Type*) [Field R] (t : R) (ht : t ≠ 0) :
    evalMap (counterexample R) (collisionFamily₁ R t) =
      collisionFamilyValue R t := by
  funext i
  fin_cases i
  all_goals simp [evalMap, counterexample, collisionFamily₁, collisionFamilyValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  all_goals field_simp [ht]
  all_goals ring

theorem collisionFamily (R : Type*) [Field R] (t : R) (ht : t ≠ 0) :
    evalMap (counterexample R) (collisionFamily₀ R t) =
      evalMap (counterexample R) (collisionFamily₁ R t) :=
  (collisionFamily₀_value R t ht).trans (collisionFamily₁_value R t ht).symm

theorem collisionFamily_points_distinct
    (R : Type*) [Field R] (t : R) (ht : t ≠ 0) :
    collisionFamily₀ R t ≠ collisionFamily₁ R t := by
  intro h
  have hx := congrFun h 0
  apply ht
  simpa [collisionFamily₀, collisionFamily₁] using hx

end LeanProofs.JacobianCounterexample
