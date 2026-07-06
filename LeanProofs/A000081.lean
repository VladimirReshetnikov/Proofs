import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Initial values of OEIS A000081 from exponent functions

OEIS A000081 counts the distinct functions of a positive real variable obtained
from all binary parenthesizations of `x^x^...^x`.  The primary definition in
this module is exactly that semantic set of functions
`{x : ℝ // 0 < x} -> {x : ℝ // 0 < x}`.

The first values are proved by enumerating the legal parenthesizations,
collapsing only identities proved over positive reals, and separating the
remaining functions by exact logarithmic/exponent tests.
-/

namespace LeanProofs

namespace A000081

/-- Positive real numbers as the domain and codomain of the exponent functions. -/
abbrev PosReal := {x : ℝ // 0 < x}

/-- Positive-real exponentiation, bundled with its positivity proof. -/
noncomputable def PosReal.rpow (x : PosReal) (y : ℝ) : PosReal :=
  ⟨x.1 ^ y, Real.rpow_pos_of_pos x.2 y⟩

/-- Binary parenthesized expressions built from copies of the variable `x`. -/
inductive PowExpr where
  | x
  | pow (a b : PowExpr)
deriving Repr, DecidableEq

namespace PowExpr

open PowExpr

/-- Evaluate a parenthesized power expression as a function on positive reals. -/
noncomputable def eval : PowExpr -> PosReal -> PosReal
  | x, t => t
  | pow a b, t => PosReal.rpow (eval a t) (eval b t).1

/-- The number of variable occurrences in a power expression. -/
def size : PowExpr -> Nat
  | x => 1
  | pow a b => size a + size b

/-- All legal binary parenthesizations with exactly `n` copies of `x`. -/
def parenthesizations : Nat -> List PowExpr
  | 0 => []
  | 1 => [x]
  | n + 2 =>
      (List.finRange (n + 1)).flatMap fun k =>
        (parenthesizations (k.1 + 1)).flatMap fun a =>
          (parenthesizations (n + 1 - k.1)).map fun b => pow a b
termination_by n => n
decreasing_by
  · exact Nat.lt_succ_of_le (Nat.sub_le _ _)
  · exact Nat.succ_lt_succ k.2

/--
The semantic value set for A000081: distinct functions of a positive real
variable arising from all legal parenthesizations.
-/
def valueSet (n : Nat) : Set (PosReal -> PosReal) :=
  {f | ∃ e ∈ parenthesizations n, eval e = f}

/-- OEIS A000081, defined as the cardinality of the semantic exponent-function set. -/
noncomputable def a000081 (n : Nat) : Nat :=
  (valueSet n).ncard

/-- A fixed positive real used only to separate functions by evaluation. -/
def three : PosReal :=
  ⟨3, by norm_num⟩

/--
For a positive-real expression `e`, `exponent e t` is the exponent of the outer
base `t`: `(eval e t).1 = t.1 ^ exponent e t`.
-/
noncomputable def exponent : PowExpr -> PosReal -> ℝ
  | x, _ => 1
  | pow a b, t => exponent a t * (eval b t).1

/-- Every expression evaluates to `t` raised to its outer exponent. -/
theorem eval_eq_rpow_exponent (e : PowExpr) (t : PosReal) :
    (eval e t).1 = t.1 ^ exponent e t := by
  induction e with
  | x =>
      simp [eval, exponent, Real.rpow_one]
  | pow a b iha _ =>
      simp only [eval, exponent, PosReal.rpow]
      rw [iha]
      rw [Real.rpow_mul t.2.le]

/-- The map `u ↦ 3^u` is injective on real exponents. -/
theorem three_rpow_inj {a b : ℝ} (h : (3 : ℝ) ^ a = (3 : ℝ) ^ b) : a = b := by
  have hlog := congrArg Real.log h
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 3) a,
      Real.log_rpow (by norm_num : (0 : ℝ) < 3) b] at hlog
  have hpos : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num : (1 : ℝ) < 3)
  nlinarith

/-- Distinct outer exponents at `x = 3` separate semantic functions. -/
theorem eval_ne_of_exponent_ne_at_three {e₁ e₂ : PowExpr}
    (h : exponent e₁ three ≠ exponent e₂ three) : eval e₁ ≠ eval e₂ := by
  intro hf
  have hval := congrArg (fun f : PosReal -> PosReal => (f three).1) hf
  rw [eval_eq_rpow_exponent e₁ three, eval_eq_rpow_exponent e₂ three] at hval
  exact h (three_rpow_inj hval)

def e2 : PowExpr :=
  pow x x

def e3a : PowExpr :=
  pow x (pow x x)

def e3b : PowExpr :=
  pow (pow x x) x

def e4a : PowExpr :=
  pow x (pow x (pow x x))

def e4b : PowExpr :=
  pow x (pow (pow x x) x)

def e4c : PowExpr :=
  pow (pow x x) (pow x x)

def e4d : PowExpr :=
  pow (pow x (pow x x)) x

def e4e : PowExpr :=
  pow (pow (pow x x) x) x

theorem parenthesizations_one :
    parenthesizations 1 = [x] := by
  native_decide

theorem parenthesizations_two :
    parenthesizations 2 = [e2] := by
  native_decide

theorem parenthesizations_three :
    parenthesizations 3 = [e3a, e3b] := by
  native_decide

theorem parenthesizations_four :
    parenthesizations 4 = [e4a, e4b, e4c, e4d, e4e] := by
  native_decide

theorem valueSet_one :
    valueSet 1 = ({eval x} : Set (PosReal -> PosReal)) := by
  ext f
  rw [valueSet, parenthesizations_one]
  simp [eq_comm]

theorem valueSet_two :
    valueSet 2 = ({eval e2} : Set (PosReal -> PosReal)) := by
  ext f
  rw [valueSet, parenthesizations_two]
  simp [eq_comm]

theorem valueSet_three :
    valueSet 3 = ({eval e3a, eval e3b} : Set (PosReal -> PosReal)) := by
  ext f
  rw [valueSet, parenthesizations_three]
  simp [eq_comm]

theorem e3a_ne_e3b : eval e3a ≠ eval e3b := by
  apply eval_ne_of_exponent_ne_at_three
  norm_num [exponent, eval, PosReal.rpow, three, e3a, e3b]

/--
The middle two binary parenthesizations with four variables define the same
positive-real function:

`(x^x)^(x^x) = (x^(x^x))^x`.
-/
theorem e4c_eq_e4d : eval e4c = eval e4d := by
  funext t
  apply Subtype.ext
  simp only [eval, e4c, e4d, PosReal.rpow]
  rw [← Real.rpow_mul t.2.le t.1 (t.1 ^ t.1),
      ← Real.rpow_mul t.2.le (t.1 ^ t.1) t.1]
  ring_nf

theorem valueSet_four :
    valueSet 4 =
      ({eval e4a, eval e4b, eval e4d, eval e4e} : Set (PosReal -> PosReal)) := by
  ext f
  rw [valueSet, parenthesizations_four]
  simp [e4c_eq_e4d, eq_comm]

theorem e4a_ne_e4b : eval e4a ≠ eval e4b := by
  apply eval_ne_of_exponent_ne_at_three
  norm_num [exponent, eval, PosReal.rpow, three, e4a, e4b]

theorem e4a_ne_e4d : eval e4a ≠ eval e4d := by
  apply eval_ne_of_exponent_ne_at_three
  norm_num [exponent, eval, PosReal.rpow, three, e4a, e4d]

theorem e4a_ne_e4e : eval e4a ≠ eval e4e := by
  apply eval_ne_of_exponent_ne_at_three
  norm_num [exponent, eval, PosReal.rpow, three, e4a, e4e]

theorem e4b_ne_e4d : eval e4b ≠ eval e4d := by
  apply eval_ne_of_exponent_ne_at_three
  norm_num [exponent, eval, PosReal.rpow, three, e4b, e4d]

theorem e4b_ne_e4e : eval e4b ≠ eval e4e := by
  apply eval_ne_of_exponent_ne_at_three
  norm_num [exponent, eval, PosReal.rpow, three, e4b, e4e]

theorem e4d_ne_e4e : eval e4d ≠ eval e4e := by
  apply eval_ne_of_exponent_ne_at_three
  norm_num [exponent, eval, PosReal.rpow, three, e4d, e4e]

theorem valueSet_four_ncard :
    ({eval e4a, eval e4b, eval e4d, eval e4e} : Set (PosReal -> PosReal)).ncard = 4 := by
  rw [Set.ncard_insert_of_notMem]
  · rw [Set.ncard_insert_of_notMem]
    · rw [Set.ncard_pair e4d_ne_e4e]
    · simp [e4b_ne_e4d, e4b_ne_e4e]
  · simp [e4a_ne_e4b, e4a_ne_e4d, e4a_ne_e4e]

/-- `A000081(0) = 0`. -/
theorem a000081_zero : a000081 0 = 0 := by
  simp [a000081, valueSet, parenthesizations]

/-- `A000081(1) = 1`. -/
theorem a000081_one : a000081 1 = 1 := by
  rw [a000081, valueSet_one, Set.ncard_singleton]

/-- `A000081(2) = 1`. -/
theorem a000081_two : a000081 2 = 1 := by
  rw [a000081, valueSet_two, Set.ncard_singleton]

/-- `A000081(3) = 2`. -/
theorem a000081_three : a000081 3 = 2 := by
  rw [a000081, valueSet_three, Set.ncard_pair e3a_ne_e3b]

/-- `A000081(4) = 4`. -/
theorem a000081_four : a000081 4 = 4 := by
  rw [a000081, valueSet_four, valueSet_four_ncard]

end PowExpr

export PowExpr (a000081 a000081_zero a000081_one a000081_two a000081_three a000081_four)

end A000081

end LeanProofs
