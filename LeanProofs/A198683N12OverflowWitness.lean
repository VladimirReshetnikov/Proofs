import LeanProofs.A198683
import LeanProofs.A198683N12Magnitude
import Mathlib.Tactic.NormNum

/-!
# Semantic overflow witness for OEIS A198683 at n = 12

The retained n = 12 TSV's overflow singleton has split `(k=1, ia=0, ib=57)`:
it is `i` raised to the dynamic-programming representative `values[11][57]`.
The diagnostic `trace_dp_expression.py` identifies that representative as

```text
(i^(i^(i^(((i^i)^i)^(i^((i^i)^(i^i)))))))
```

This module records that expression directly in the semantic complex-valued
language of `LeanProofs.A198683` and proves that it is a genuine element of
`a198683ValueSet 11`, hence that the corresponding overflow candidate is a
genuine element of `a198683ValueSet 12`.

This still does not prove the candidate is distinct from every other n = 12
value; it supplies the formal witness and the log-modulus formula that the
certification plan needs next.
-/

namespace LeanProofs

namespace A198683N12OverflowWitness

noncomputable section

open Complex

/-- `i^i`. -/
def w2 : ℂ := principalPow Complex.I Complex.I

/-- `(i^i)^i`. -/
def w3R : ℂ := principalPow w2 Complex.I

/-- `(i^i)^(i^i)`. -/
def w4C : ℂ := principalPow w2 w2

/-- `i^((i^i)^(i^i))`. -/
def w5C : ℂ := principalPow Complex.I w4C

/-- `((i^i)^i)^(i^((i^i)^(i^i)))`. -/
def w8 : ℂ := principalPow w3R w5C

/-- `i^(((i^i)^i)^(i^((i^i)^(i^i))))`. -/
def w9 : ℂ := principalPow Complex.I w8

/-- `i^(i^(((i^i)^i)^(i^((i^i)^(i^i)))))`. -/
def w10 : ℂ := principalPow Complex.I w9

/-- The traced `values[11][57]` representative. -/
def overflowBase11 : ℂ := principalPow Complex.I w10

/-- The corresponding n = 12 overflow candidate. -/
def overflowCandidate12 : ℂ := principalPow Complex.I overflowBase11

private theorem overflowExponent_re :
    (Complex.log Complex.I * overflowBase11).re =
      -(Real.pi / 2) * overflowBase11.im := by
  rw [Complex.log_I]
  simp [Complex.mul_re, Complex.mul_im]

private theorem mem_one : Complex.I ∈ a198683ValueSet 1 := by
  simp [a198683ValueSet]

private theorem mem_w2 : w2 ∈ a198683ValueSet 2 := by
  simp [a198683ValueSet, w2]

private theorem mem_w3R : w3R ∈ a198683ValueSet 3 := by
  simp only [a198683ValueSet]
  refine ⟨⟨1, by norm_num⟩, w2, mem_w2, Complex.I, mem_one, ?_⟩
  simp [w3R]

private theorem mem_w4C : w4C ∈ a198683ValueSet 4 := by
  simp only [a198683ValueSet]
  refine ⟨⟨1, by norm_num⟩, w2, mem_w2, w2, mem_w2, ?_⟩
  simp [w4C]

private theorem mem_w5C : w5C ∈ a198683ValueSet 5 := by
  simp only [a198683ValueSet]
  refine ⟨⟨0, by norm_num⟩, Complex.I, mem_one, w4C, mem_w4C, ?_⟩
  simp [w5C]

private theorem mem_w8 : w8 ∈ a198683ValueSet 8 := by
  simp only [a198683ValueSet]
  refine ⟨⟨2, by norm_num⟩, w3R, mem_w3R, w5C, mem_w5C, ?_⟩
  simp [w8]

private theorem mem_w9 : w9 ∈ a198683ValueSet 9 := by
  simp only [a198683ValueSet]
  refine ⟨⟨0, by norm_num⟩, Complex.I, mem_one, w8, mem_w8, ?_⟩
  simp [w9]

private theorem mem_w10 : w10 ∈ a198683ValueSet 10 := by
  simp only [a198683ValueSet]
  refine ⟨⟨0, by norm_num⟩, Complex.I, mem_one, w9, mem_w9, ?_⟩
  simp [w10]

/-- The traced overflow base is semantically one of the n = 11 values. -/
theorem overflowBase11_mem : overflowBase11 ∈ a198683ValueSet 11 := by
  simp only [a198683ValueSet]
  refine ⟨⟨0, by norm_num⟩, Complex.I, mem_one, w10, mem_w10, ?_⟩
  simp [overflowBase11]

/-- The traced overflow candidate is semantically one of the n = 12 values. -/
theorem overflowCandidate12_mem : overflowCandidate12 ∈ a198683ValueSet 12 := by
  simp only [a198683ValueSet]
  refine ⟨⟨0, by norm_num⟩, Complex.I, mem_one, overflowBase11, overflowBase11_mem, ?_⟩
  simp [overflowCandidate12]

/-- The overflow witness modulus is determined by the imaginary part of its n = 11 base. -/
theorem overflowCandidate12_norm :
    ‖overflowCandidate12‖ = Real.exp (-(Real.pi / 2) * overflowBase11.im) := by
  dsimp [overflowCandidate12, principalPow]
  rw [Complex.norm_exp, overflowExponent_re]

/--
The real part of the level-12 exponent for this witness is controlled by the
imaginary part of the n = 11 base.
-/
theorem overflowCandidate12_exponent_re :
    (overflowBase11 * Complex.log Complex.I).re =
      -(Real.pi / 2) * overflowBase11.im :=
  A198683N12Magnitude.re_mul_log_I overflowBase11

/--
Any candidate whose exponent has larger real part than the overflow witness's
exponent is distinct from the overflow witness. This is the formal version of
the log-modulus separation target from the local n = 12 magnitude note.
-/
theorem overflowCandidate12_ne_exp_of_re_gt {e : ℂ}
    (h : -(Real.pi / 2) * overflowBase11.im < e.re) :
    overflowCandidate12 ≠ Complex.exp e := by
  dsimp [overflowCandidate12, principalPow]
  exact A198683N12Magnitude.exp_ne_of_re_lt (by
    rw [overflowExponent_re]
    exact h)

/--
The same separation criterion specialized to another principal power candidate.
-/
theorem overflowCandidate12_ne_principalPow_of_re_gt {a b : ℂ}
    (h : -(Real.pi / 2) * overflowBase11.im < (Complex.log a * b).re) :
    overflowCandidate12 ≠ principalPow a b := by
  dsimp [principalPow]
  exact overflowCandidate12_ne_exp_of_re_gt h

/--
Bounded version of the same separation criterion. It is enough to prove a
lower bound on the overflow base's imaginary part and a corresponding lower
bound on the other candidate's exponent real part.
-/
theorem overflowCandidate12_ne_principalPow_of_im_gt_of_re_gt {a b : ℂ} {bound : ℝ}
    (hbase : bound < overflowBase11.im)
    (hother : -(Real.pi / 2) * bound < (Complex.log a * b).re) :
    overflowCandidate12 ≠ principalPow a b := by
  dsimp [overflowCandidate12, principalPow]
  rw [mul_comm (Complex.log Complex.I) overflowBase11]
  exact A198683N12Magnitude.exp_mul_log_I_ne_of_im_gt_of_re_gt hbase hother

end

end A198683N12OverflowWitness

end LeanProofs
