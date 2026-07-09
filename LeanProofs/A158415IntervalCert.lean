import LeanProofs.A158415

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

def Valid : IntervalCert -> Prop
  | one lo hi => (lo : Real) < 1 ∧ (1 : Real) < hi
  | sqrt lo hi c =>
      c.Valid ∧ ((lo : Real) < 0 ∨ (lo : Real) ^ 2 < (c.lower : Real)) ∧
        ((c.upper : Real) < (hi : Real) ^ 2) ∧ (0 : Real) < hi
  | add lo hi a b =>
      a.Valid ∧ b.Valid ∧
        ((lo : Real) < (a.lower : Real) + (b.lower : Real)) ∧
        ((a.upper : Real) + (b.upper : Real) < (hi : Real))

theorem sound (c : IntervalCert) (h : c.Valid) :
    (c.lower : Real) < c.expr.eval ∧ c.expr.eval < (c.upper : Real) := by
  induction c with
  | one lo hi =>
      simpa [Valid, lower, upper, expr, eval] using h
  | sqrt lo hi c ih =>
      rcases h with ⟨hc, hlo, hhi, hpos⟩
      have hs := ih hc
      simp [lower, upper, expr, eval]
      constructor
      · rcases hlo with hneg | hsq
        · exact lt_of_lt_of_le hneg (Real.sqrt_nonneg _)
        · apply Real.lt_sqrt_of_sq_lt
          exact lt_trans hsq hs.1
      · rw [Real.sqrt_lt' hpos]
        exact lt_trans hs.2 hhi
  | add lo hi a b iha ihb =>
      rcases h with ⟨ha, hb, hlo, hhi⟩
      have hsa := iha ha
      have hsb := ihb hb
      constructor <;> simp [lower, upper, expr, eval] at * <;> linarith

theorem lt_of_gap {x y : Real} (left right : IntervalCert)
    (hleft : left.Valid) (hright : right.Valid)
    (hleftEval : x = left.expr.eval) (hrightEval : y = right.expr.eval)
    (hgap : (left.upper : Real) < (right.lower : Real)) : x < y := by
  have hleftRaw := sound left hleft
  have hrightRaw := sound right hright
  rw [hleftEval, hrightEval]
  exact lt_trans hleftRaw.2 (lt_trans hgap hrightRaw.1)

end IntervalCert

end Expr
end A158415
end LeanProofs
