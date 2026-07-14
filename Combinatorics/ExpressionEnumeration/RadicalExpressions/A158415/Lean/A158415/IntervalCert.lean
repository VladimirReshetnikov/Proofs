import A158415.Core

/-!
# Shared interval certificates for OEIS A158415 proofs

This module contains the small checker used by generated adjacent-order
certificates.  Generated modules provide the concrete certificates; this file
provides the reusable soundness and comparison lemmas.
-/

namespace LeanProofs
namespace A158415
namespace Expr

inductive IntervalCert where
  | one (lo hi : Rat)
  | sqrt (lo hi : Rat) (c : IntervalCert)
  | add (lo hi : Rat) (a b : IntervalCert)

namespace IntervalCert

def lower : IntervalCert -> Rat
  | one lo _ => lo
  | sqrt lo _ _ => lo
  | add lo _ _ _ => lo

def upper : IntervalCert -> Rat
  | one _ hi => hi
  | sqrt _ hi _ => hi
  | add _ hi _ _ => hi

def expr : IntervalCert -> Expr
  | one _ _ => Expr.one
  | sqrt _ _ c => Expr.sqrt c.expr
  | add _ _ a b => Expr.add a.expr b.expr

def valid : IntervalCert -> Bool
  | one lo hi => decide (lo < 1) && decide (1 < hi)
  | sqrt lo hi c =>
      c.valid && (decide (lo < 0) || decide (lo ^ 2 < c.lower)) &&
        decide (c.upper < hi ^ 2) && decide (0 < hi)
  | add lo hi a b =>
      a.valid && b.valid && decide (lo < a.lower + b.lower) &&
        decide (a.upper + b.upper < hi)

def Valid (c : IntervalCert) : Prop := c.valid = true

def separated (left right : IntervalCert) : Bool :=
  left.valid && right.valid && decide (left.upper < right.lower)

private theorem cast_lt {a b : Rat} (h : a < b) : (a : Real) < (b : Real) :=
  (Rat.cast_lt (K := Real)).2 h

private theorem cast_sq_lt {a b : Rat} (h : a ^ 2 < b) :
    (a : Real) ^ 2 < (b : Real) := by
  rw [← Rat.cast_pow]
  exact cast_lt h

private theorem cast_lt_sq {a b : Rat} (h : a < b ^ 2) :
    (a : Real) < (b : Real) ^ 2 := by
  rw [← Rat.cast_pow]
  exact cast_lt h

private theorem cast_lt_add {a b c : Rat} (h : a < b + c) :
    (a : Real) < (b : Real) + (c : Real) := by
  rw [← Rat.cast_add]
  exact cast_lt h

private theorem cast_add_lt {a b c : Rat} (h : a + b < c) :
    (a : Real) + (b : Real) < (c : Real) := by
  rw [← Rat.cast_add]
  exact cast_lt h

theorem sound (c : IntervalCert) (h : c.Valid) :
    (c.lower : Real) < c.expr.eval ∧ c.expr.eval < (c.upper : Real) := by
  induction c with
  | one lo hi =>
      simp only [Valid, valid, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [lower, upper, expr, eval]
      exact And.intro
        (by simpa only [Rat.cast_one] using cast_lt h.1)
        (by simpa only [Rat.cast_one] using cast_lt h.2)
  | sqrt lo hi c ih =>
      simp only [Valid, valid, Bool.and_eq_true, Bool.or_eq_true,
        decide_eq_true_eq] at h
      rcases h with ⟨⟨⟨hc, hlo⟩, hhi⟩, hpos⟩
      have hs := ih hc
      simp only [lower, upper, expr, eval]
      constructor
      · rcases hlo with hneg | hsq
        · exact lt_of_lt_of_le
            (by simpa only [Rat.cast_zero] using cast_lt hneg) (Real.sqrt_nonneg _)
        · apply Real.lt_sqrt_of_sq_lt
          exact lt_trans (cast_sq_lt hsq) hs.1
      · rw [Real.sqrt_lt'
            (by simpa only [Rat.cast_zero] using cast_lt hpos)]
        exact lt_trans hs.2 (cast_lt_sq hhi)
  | add lo hi a b iha ihb =>
      simp only [Valid, valid, Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with ⟨⟨⟨ha, hb⟩, hlo⟩, hhi⟩
      have hsa := iha ha
      have hsb := ihb hb
      simp only [lower, upper, expr, eval]
      constructor
      · exact lt_trans (cast_lt_add hlo) (add_lt_add hsa.1 hsb.1)
      · exact lt_trans (add_lt_add hsa.2 hsb.2) (cast_add_lt hhi)

theorem lt_of_separated {x y : Real} (left right : IntervalCert)
    (hcert : left.separated right = true)
    (hleftEval : x = left.expr.eval) (hrightEval : y = right.expr.eval)
    : x < y := by
  simp only [separated, Bool.and_eq_true, decide_eq_true_eq] at hcert
  rcases hcert with ⟨⟨hleft, hright⟩, hgap⟩
  have hleftRaw := sound left hleft
  have hrightRaw := sound right hright
  rw [hleftEval, hrightEval]
  exact lt_trans hleftRaw.2 (lt_trans (cast_lt hgap) hrightRaw.1)

end IntervalCert

end Expr
end A158415
end LeanProofs
