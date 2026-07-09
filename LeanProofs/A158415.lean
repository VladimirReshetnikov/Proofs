import Init.Tactics
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.NAry
import Mathlib.Data.Set.Card
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum

/-!
# Initial values of OEIS A158415

OEIS A158415 counts the distinct real values represented by expressions built
from one nullary symbol `1`, one unary symbol `sqrt`, and one binary symbol `+`,
where the size of an expression is its number of symbols.

The primary definition below is lexical: we enumerate all expression trees of a
given size and interpret them in `ℝ` using `Real.sqrt` and addition.  A proved
split-recursive value-set presentation is then used for the small checked
initial values.  This avoids the floating-point `eps = 10^-20` test from the
OEIS PARI program.
-/

namespace LeanProofs

namespace A158415

open Set

/-- Expression trees over the signature `1`, `sqrt(_)`, and binary `+`. -/
inductive Expr where
  | one
  | sqrt (e : Expr)
  | add (a b : Expr)
deriving Repr, DecidableEq

namespace Expr

open Expr

/-- The number of symbols in an expression. -/
def size : Expr -> Nat
  | one => 1
  | sqrt e => e.size + 1
  | add a b => a.size + b.size + 1

theorem size_pos (e : Expr) : 0 < e.size := by
  cases e <;> simp [size]

/-- All expression trees with exactly `n` symbols. -/
def expressions : Nat -> List Expr
  | 0 => []
  | 1 => [one]
  | n + 2 =>
      (expressions (n + 1)).map sqrt ++
        (List.finRange n).flatMap fun k =>
          (expressions (k.1 + 1)).flatMap fun a =>
            (expressions (n - k.1)).map fun b => add a b
termination_by n => n
decreasing_by
  all_goals omega

theorem expressions_zero : expressions 0 = [] := by
  rw [expressions.eq_def]

theorem expressions_one : expressions 1 = [one] := by
  rw [expressions.eq_def]

theorem expressions_succ_succ (n : Nat) :
    expressions (n + 2) =
      (expressions (n + 1)).map sqrt ++
        (List.finRange n).flatMap fun k =>
          (expressions (k.1 + 1)).flatMap fun a =>
            (expressions (n - k.1)).map fun b => add a b := by
  rw [expressions.eq_def]

theorem mem_expressions_size (e : Expr) : e ∈ expressions e.size := by
  induction e with
  | one =>
      simp [size, expressions_one]
  | sqrt e ih =>
      have hpos := size_pos e
      rw [show (sqrt e).size = (e.size - 1) + 2 by
        dsimp [size]
        omega]
      rw [expressions_succ_succ]
      simp only [List.mem_append, List.mem_map]
      left
      refine ⟨e, ?_, rfl⟩
      simpa [Nat.sub_add_cancel hpos] using ih
  | add a b iha ihb =>
      have ha := size_pos a
      have hb := size_pos b
      rw [show (add a b).size = (a.size + b.size - 1) + 2 by
        dsimp [size]
        omega]
      rw [expressions_succ_succ]
      simp only [List.mem_append, List.mem_map, List.mem_flatMap]
      right
      let k : Fin (a.size + b.size - 1) := ⟨a.size - 1, by omega⟩
      refine ⟨k, List.mem_finRange k, a, ?_, b, ?_, rfl⟩
      · have hk : k.1 + 1 = a.size := by
          simp [k]
          omega
        simpa [hk] using iha
      · have hk : (a.size + b.size - 1) - k.1 = b.size := by
          simp [k]
          omega
        simpa [hk] using ihb

/-- Interpret an expression as a real number. -/
noncomputable def eval : Expr -> ℝ
  | one => 1
  | sqrt e => Real.sqrt e.eval
  | add a b => a.eval + b.eval

/--
Pad an expression by one symbol without changing its value, by replacing the
leftmost `1` leaf with `sqrt(1)`.
-/
def padOne : Expr -> Expr
  | one => sqrt one
  | sqrt e => sqrt (padOne e)
  | add a b => add (padOne a) b

theorem size_padOne (e : Expr) : (padOne e).size = e.size + 1 := by
  induction e with
  | one =>
      rfl
  | sqrt e ih =>
      simp [padOne, size, ih]
  | add a b iha _ihb =>
      simp [padOne, size, iha]
      omega

theorem eval_padOne (e : Expr) : eval (padOne e) = eval e := by
  induction e with
  | one =>
      simp [padOne, eval]
  | sqrt e ih =>
      simp [padOne, eval, ih]
  | add a b iha _ihb =>
      simp [padOne, eval, iha]

/-- The lexical set of real values represented by all expressions of size `n`. -/
def valueSet (n : Nat) : Set ℝ :=
  {v | ∃ e ∈ expressions n, eval e = v}

theorem padOne_mem_expressions_succ {n : Nat} {e : Expr}
    (he : e ∈ expressions n) : padOne e ∈ expressions (n + 1) := by
  induction n using Nat.strong_induction_on generalizing e with
  | h n ih =>
      cases n with
      | zero =>
          simp [expressions_zero] at he
      | succ n =>
          cases n with
          | zero =>
              rw [expressions_one] at he
              rcases List.mem_singleton.mp he with rfl
              simp [expressions_succ_succ, expressions_one, padOne]
          | succ n =>
              rw [expressions_succ_succ] at he
              simp only [List.mem_append, List.mem_map, List.mem_flatMap] at he
              rw [show Nat.succ (Nat.succ n) + 1 = (n + 1) + 2 by omega]
              rw [expressions_succ_succ (n + 1)]
              simp only [List.mem_append, List.mem_map, List.mem_flatMap]
              rcases he with ⟨a, ha, rfl⟩ | ⟨k, _hk, a, ha, b, hb, rfl⟩
              · left
                refine ⟨padOne a, ?_, rfl⟩
                exact ih (n + 1) (by omega) ha
              · right
                let k' : Fin (n + 1) := ⟨k.1 + 1, Nat.succ_lt_succ k.2⟩
                refine ⟨k', List.mem_finRange k', padOne a, ?_, b, ?_, rfl⟩
                · simpa [k'] using ih (k.1 + 1) (by omega) ha
                · have hright : (n + 1) - (k.1 + 1) = n - k.1 := by omega
                  simpa [k', hright] using hb

theorem valueSet_subset_succ (n : Nat) : valueSet n ⊆ valueSet (n + 1) := by
  rintro x ⟨e, he, rfl⟩
  exact ⟨padOne e, padOne_mem_expressions_succ he, eval_padOne e⟩

theorem valueSet_subset_of_le {m n : Nat} (h : m ≤ n) : valueSet m ⊆ valueSet n := by
  intro x hx
  induction h with
  | refl =>
      exact hx
  | step _ ih =>
      exact valueSet_subset_succ _ ih

/-- The split-recursive presentation of the same value set. -/
def recursiveValueSet : Nat -> Set ℝ
  | 0 => ∅
  | 1 => {1}
  | n + 2 =>
      (fun x : ℝ => Real.sqrt x) '' recursiveValueSet (n + 1) ∪
        {v | ∃ k : Fin n,
          ∃ x ∈ recursiveValueSet (k.1 + 1),
          ∃ y ∈ recursiveValueSet (n - k.1),
            v = x + y}
termination_by n => n
decreasing_by
  all_goals omega

/-- The recursive value set is exactly the lexical expression value set. -/
theorem valueSet_eq_recursiveValueSet (n : Nat) :
    valueSet n = recursiveValueSet n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          ext v
          simp [valueSet, expressions_zero, recursiveValueSet]
      | succ n =>
          cases n with
          | zero =>
              ext v
              simp [valueSet, expressions_one, recursiveValueSet, eval]
          | succ n =>
              ext v
              constructor
              · rintro ⟨e, he, rfl⟩
                rw [expressions_succ_succ] at he
                simp only [List.mem_append, List.mem_map, List.mem_flatMap] at he
                rcases he with ⟨a, ha, rfl⟩ | ⟨k, _hk, a, ha, b, hb, rfl⟩
                · rw [recursiveValueSet]
                  left
                  refine ⟨eval a, ?_, rfl⟩
                  rw [← ih (n + 1) (by omega)]
                  exact ⟨a, ha, rfl⟩
                · rw [recursiveValueSet]
                  right
                  refine ⟨k, eval a, ?_, eval b, ?_, rfl⟩
                  · rw [← ih (k.1 + 1) (by omega)]
                    exact ⟨a, ha, rfl⟩
                  · rw [← ih (n - k.1) (by omega)]
                    exact ⟨b, hb, rfl⟩
              · intro hv
                rw [recursiveValueSet] at hv
                rcases hv with ⟨x, hx, rfl⟩ | ⟨k, x, hx, y, hy, rfl⟩
                · have hxLex : x ∈ valueSet (n + 1) := by
                    rw [ih (n + 1) (by omega)]
                    exact hx
                  rcases hxLex with ⟨a, ha, rfl⟩
                  refine ⟨sqrt a, ?_, rfl⟩
                  rw [expressions_succ_succ]
                  simp only [List.mem_append, List.mem_map]
                  exact Or.inl ⟨a, ha, rfl⟩
                · have hxLex : x ∈ valueSet (k.1 + 1) := by
                    rw [ih (k.1 + 1) (by omega)]
                    exact hx
                  have hyLex : y ∈ valueSet (n - k.1) := by
                    rw [ih (n - k.1) (by omega)]
                    exact hy
                  rcases hxLex with ⟨a, ha, rfl⟩
                  rcases hyLex with ⟨b, hb, rfl⟩
                  refine ⟨add a b, ?_, rfl⟩
                  rw [expressions_succ_succ]
                  simp only [List.mem_append, List.mem_map, List.mem_flatMap]
                  exact Or.inr ⟨k, List.mem_finRange k, a, ha, b, hb, rfl⟩

theorem recursiveValueSet_subset_of_le {m n : Nat} (h : m ≤ n) :
    recursiveValueSet m ⊆ recursiveValueSet n := by
  intro x hx
  rw [← valueSet_eq_recursiveValueSet m] at hx
  rw [← valueSet_eq_recursiveValueSet n]
  exact valueSet_subset_of_le h hx

theorem eval_mem_recursiveValueSet_of_size {e : Expr} {n : Nat} (h : e.size = n) :
    e.eval ∈ recursiveValueSet n := by
  rw [← valueSet_eq_recursiveValueSet]
  exact ⟨e, by simpa [h] using mem_expressions_size e, rfl⟩

theorem one_add_mem_recursiveValueSet_add_two {n : Nat} (hn : 0 < n) {x : ℝ}
    (hx : x ∈ recursiveValueSet n) : 1 + x ∈ recursiveValueSet (n + 2) := by
  rw [recursiveValueSet]
  right
  let k : Fin n := ⟨0, hn⟩
  refine ⟨k, 1, ?_, x, ?_, rfl⟩
  · change (1 : ℝ) ∈ recursiveValueSet 1
    simp [recursiveValueSet]
  · change x ∈ recursiveValueSet n
    exact hx

theorem natCast_add_mem_recursiveValueSet_add_two_mul {m n : Nat} (hn : 0 < n) {x : ℝ}
    (hx : x ∈ recursiveValueSet n) :
    (m : ℝ) + x ∈ recursiveValueSet (n + 2 * m) := by
  induction m with
  | zero =>
      simpa using hx
  | succ m ih =>
      have hpos : 0 < n + 2 * m := by omega
      have hstep : 1 + ((m : ℝ) + x) ∈ recursiveValueSet ((n + 2 * m) + 2) :=
        one_add_mem_recursiveValueSet_add_two hpos ih
      have hindex : (n + 2 * m) + 2 = n + 2 * Nat.succ m := by omega
      have heq : ((Nat.succ m : Nat) : ℝ) + x = 1 + ((m : ℝ) + x) := by
        simp [Nat.cast_succ, add_assoc, add_comm]
      rw [heq, ← hindex]
      exact hstep

/-- OEIS A158415, as a cardinality of the lexical real-value set. -/
noncomputable def a158415 (n : Nat) : Nat :=
  (valueSet n).ncard

theorem a158415_eq_recursiveValueSet_ncard (n : Nat) :
    a158415 n = (recursiveValueSet n).ncard := by
  rw [a158415, valueSet_eq_recursiveValueSet]

theorem recursiveValueSet_two :
    recursiveValueSet 2 = ({1} : Set ℝ) := by
  ext x
  simp [recursiveValueSet]

theorem recursiveValueSet_three :
    recursiveValueSet 3 = ({1, 2} : Set ℝ) := by
  ext x
  simp [recursiveValueSet, recursiveValueSet_two]
  constructor
  · rintro (rfl | rfl)
    · right
      norm_num
    · left
      rfl
  · rintro (rfl | rfl)
    · exact Or.inr rfl
    · exact Or.inl (by norm_num : (2 : ℝ) = 1 + 1)

theorem one_ne_sqrt_two : (1 : ℝ) ≠ Real.sqrt 2 := by
  exact ne_of_lt Real.one_lt_sqrt_two

theorem sqrt_two_ne_two : Real.sqrt 2 ≠ (2 : ℝ) := by
  exact ne_of_lt (Real.sqrt_two_lt_three_halves.trans (by norm_num : (3 : ℝ) / 2 < 2))

theorem sqrt_two_lt_two : Real.sqrt 2 < (2 : ℝ) :=
  Real.sqrt_two_lt_three_halves.trans (by norm_num : (3 : ℝ) / 2 < 2)

theorem one_ne_two : (1 : ℝ) ≠ 2 := by
  norm_num

theorem one_lt_sqrt_sqrt_two : (1 : ℝ) < Real.sqrt (Real.sqrt 2) := by
  simpa using
    (Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) Real.one_lt_sqrt_two)

theorem sqrt_sqrt_two_lt_sqrt_two :
    Real.sqrt (Real.sqrt 2) < Real.sqrt 2 := by
  exact Real.sqrt_lt_sqrt (Real.sqrt_nonneg 2) sqrt_two_lt_two

theorem sqrt_sqrt_two_ne_sqrt_two :
    Real.sqrt (Real.sqrt 2) ≠ Real.sqrt 2 :=
  ne_of_lt sqrt_sqrt_two_lt_sqrt_two

theorem one_ne_sqrt_sqrt_two : (1 : ℝ) ≠ Real.sqrt (Real.sqrt 2) :=
  ne_of_lt one_lt_sqrt_sqrt_two

noncomputable abbrev rt2_4 : ℝ := Real.sqrt (Real.sqrt 2)

noncomputable abbrev rt2_8 : ℝ := Real.sqrt rt2_4

noncomputable abbrev rt2_16 : ℝ := Real.sqrt rt2_8

noncomputable abbrev rt3_4 : ℝ := Real.sqrt (Real.sqrt 3)

noncomputable abbrev sqrt_one_add_sqrt_two : ℝ := Real.sqrt (1 + Real.sqrt 2)

theorem sqrt_lt_self_of_one_lt {x : ℝ} (h : 1 < x) : Real.sqrt x < x := by
  rw [Real.sqrt_lt' (lt_trans zero_lt_one h)]
  nlinarith

theorem rt2_8_lt_rt2_4 : rt2_8 < rt2_4 := by
  rw [rt2_8]
  have hnon : (0 : ℝ) ≤ rt2_4 := by
    rw [rt2_4]
    exact Real.sqrt_nonneg (Real.sqrt 2)
  exact
    (Real.sqrt_lt (x := rt2_4) (y := rt2_4)
      hnon hnon).2 (by
        rw [rt2_4, Real.sq_sqrt (Real.sqrt_nonneg 2)]
        exact sqrt_sqrt_two_lt_sqrt_two)

theorem one_lt_rt2_8 : (1 : ℝ) < rt2_8 := by
  rw [rt2_8, rt2_4]
  simpa using
    (Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) one_lt_sqrt_sqrt_two)

theorem rt2_16_lt_rt2_8 : rt2_16 < rt2_8 := by
  rw [rt2_16]
  exact sqrt_lt_self_of_one_lt one_lt_rt2_8

theorem one_lt_rt2_16 : (1 : ℝ) < rt2_16 := by
  rw [rt2_16]
  simpa using
    (Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) one_lt_rt2_8)

theorem sqrt_two_lt_sqrt_three : Real.sqrt 2 < Real.sqrt 3 :=
  Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) < 3)

theorem sqrt_three_lt_two : Real.sqrt 3 < (2 : ℝ) := by
  rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)]
  norm_num

theorem sqrt_four : Real.sqrt 4 = (2 : ℝ) := by
  rw [Real.sqrt_eq_iff_eq_sq (by norm_num : (0 : ℝ) ≤ 4) (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem rt2_4_lt_rt3_4 : rt2_4 < rt3_4 := by
  rw [rt2_4, rt3_4]
  exact Real.sqrt_lt_sqrt (Real.sqrt_nonneg 2) sqrt_two_lt_sqrt_three

theorem rt3_4_lt_sqrt_two : rt3_4 < Real.sqrt 2 := by
  rw [rt3_4, Real.sqrt_lt' (Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 2))]
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  exact sqrt_three_lt_two

theorem two_lt_one_add_sqrt_two : (2 : ℝ) < 1 + Real.sqrt 2 := by
  linarith [Real.one_lt_sqrt_two]

theorem one_add_sqrt_two_lt_three : 1 + Real.sqrt 2 < (3 : ℝ) := by
  linarith [sqrt_two_lt_two]

theorem sqrt_two_lt_sqrt_one_add_sqrt_two :
    Real.sqrt 2 < sqrt_one_add_sqrt_two := by
  rw [sqrt_one_add_sqrt_two]
  exact Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 2) two_lt_one_add_sqrt_two

theorem sqrt_one_add_sqrt_two_lt_sqrt_three :
    sqrt_one_add_sqrt_two < Real.sqrt 3 := by
  rw [sqrt_one_add_sqrt_two]
  exact Real.sqrt_lt_sqrt (by nlinarith [Real.sqrt_nonneg 2]) one_add_sqrt_two_lt_three

theorem two_lt_one_add_rt2_4 : (2 : ℝ) < 1 + rt2_4 := by
  linarith [one_lt_sqrt_sqrt_two]

theorem one_add_rt2_4_lt_one_add_sqrt_two :
    1 + rt2_4 < 1 + Real.sqrt 2 := by
  linarith [sqrt_sqrt_two_lt_sqrt_two]

theorem recursiveValueSet_four :
    recursiveValueSet 4 = ({1, Real.sqrt 2, 2} : Set ℝ) := by
  ext x
  simp [recursiveValueSet, recursiveValueSet_two, recursiveValueSet_three]
  constructor
  · rintro (rfl | rfl | rfl)
    · right
      norm_num
    · simp
    · simp
  · rintro (rfl | rfl | rfl)
    · simp
    · simp
    · norm_num

theorem recursiveValueSet_four_ncard :
    (recursiveValueSet 4).ncard = 3 := by
  rw [recursiveValueSet_four]
  have h1 : (1 : ℝ) ∉ ({Real.sqrt 2, 2} : Set ℝ) := by
    simp [one_ne_sqrt_two]
  have h2 : Real.sqrt 2 ∉ ({2} : Set ℝ) := by
    simp [sqrt_two_ne_two]
  rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2, Set.ncard_singleton]

theorem recursiveValueSet_five :
    recursiveValueSet 5 =
      ({1, Real.sqrt (Real.sqrt 2), Real.sqrt 2, 2, 3} : Set ℝ) := by
  ext x
  simp [recursiveValueSet, recursiveValueSet_four]
  constructor
  · rintro (h | h)
    · rcases h with h | h | h <;> subst x <;> simp
    · rcases h with ⟨k, a, ha, b, hb, rfl⟩
      fin_cases k
      · simp [recursiveValueSet, recursiveValueSet_three] at ha hb
        rcases ha with rfl
        rcases hb with rfl | rfl
        · right; right; right; left; norm_num
        · right; right; right; right; norm_num
      · simp [recursiveValueSet_two] at ha hb
        rcases ha with rfl
        rcases hb with rfl
        right; right; right; left; norm_num
      · simp [recursiveValueSet, recursiveValueSet_three] at ha hb
        rcases ha with rfl | rfl
        · rcases hb with rfl
          right; right; right; left; norm_num
        · rcases hb with rfl
          right; right; right; right; norm_num
  · rintro (rfl | rfl | rfl | rfl | rfl)
    · simp
    · simp
    · simp
    · right
      refine ⟨⟨0, by decide⟩, 1, ?_, 1, ?_, by norm_num⟩
      · simp [recursiveValueSet]
      · change (1 : ℝ) ∈ recursiveValueSet 3
        rw [recursiveValueSet_three]
        simp
    · right
      refine ⟨⟨0, by decide⟩, 1, ?_, 2, ?_, by norm_num⟩
      · simp [recursiveValueSet]
      · change (2 : ℝ) ∈ recursiveValueSet 3
        rw [recursiveValueSet_three]
        simp

theorem recursiveValueSet_five_ncard :
    (recursiveValueSet 5).ncard = 5 := by
  rw [recursiveValueSet_five]
  have h1 :
      (1 : ℝ) ∉ ({Real.sqrt (Real.sqrt 2), Real.sqrt 2, 2, 3} : Set ℝ) := by
    simp [one_ne_sqrt_sqrt_two, one_ne_sqrt_two]
  have hss :
      Real.sqrt (Real.sqrt 2) ∉ ({Real.sqrt 2, 2, 3} : Set ℝ) := by
    have hlt2 : Real.sqrt (Real.sqrt 2) < (2 : ℝ) :=
      sqrt_sqrt_two_lt_sqrt_two.trans sqrt_two_lt_two
    have hlt3 : Real.sqrt (Real.sqrt 2) < (3 : ℝ) :=
      hlt2.trans (by norm_num : (2 : ℝ) < 3)
    intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h | h
    · exact sqrt_sqrt_two_ne_sqrt_two h
    · exact (ne_of_lt hlt2) h
    · exact (ne_of_lt hlt3) h
  have hs2 : Real.sqrt 2 ∉ ({2, 3} : Set ℝ) := by
    have hlt3 : Real.sqrt 2 < (3 : ℝ) :=
      sqrt_two_lt_two.trans (by norm_num : (2 : ℝ) < 3)
    simp [sqrt_two_ne_two, ne_of_lt hlt3]
  have h2 : (2 : ℝ) ∉ ({3} : Set ℝ) := by
    norm_num
  rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem hss,
    Set.ncard_insert_of_notMem hs2, Set.ncard_insert_of_notMem h2,
    Set.ncard_singleton]

theorem recursiveValueSet_six :
    recursiveValueSet 6 =
      ({1, rt2_8, rt2_4, Real.sqrt 2, Real.sqrt 3, 2, 1 + Real.sqrt 2, 3} :
        Set ℝ) := by
  ext x
  simp [recursiveValueSet, recursiveValueSet_five, rt2_4, rt2_8]
  constructor
  · rintro (h | h)
    · rcases h with h | h | h | h | h <;> subst x <;> simp
    · rcases h with ⟨k, a, ha, b, hb, rfl⟩
      fin_cases k
      · simp [recursiveValueSet, recursiveValueSet_four] at ha hb
        rcases ha with rfl
        rcases hb with rfl | rfl | rfl
        · right; right; right; right; right; left; norm_num
        · right; right; right; right; right; right; left; rfl
        · right; right; right; right; right; right; right; norm_num
      · simp [recursiveValueSet_two, recursiveValueSet_three] at ha hb
        rcases ha with rfl
        rcases hb with rfl | rfl
        · right; right; right; right; right; left; norm_num
        · right; right; right; right; right; right; right; norm_num
      · simp [recursiveValueSet_three, recursiveValueSet_two] at ha hb
        rcases ha with rfl | rfl
        · rcases hb with rfl
          right; right; right; right; right; left; norm_num
        · rcases hb with rfl
          right; right; right; right; right; right; right; norm_num
      · simp [recursiveValueSet_four, recursiveValueSet] at ha hb
        rcases ha with rfl | rfl | rfl
        · rcases hb with rfl
          right; right; right; right; right; left; norm_num
        · rcases hb with rfl
          right; right; right; right; right; right; left
          rw [add_comm]
        · rcases hb with rfl
          right; right; right; right; right; right; right; norm_num
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · simp
    · simp
    · simp
    · simp
    · simp
    · right
      refine ⟨⟨0, by decide⟩, 1, ?_, 1, ?_, by norm_num⟩
      · simp [recursiveValueSet]
      · change (1 : ℝ) ∈ recursiveValueSet 4
        rw [recursiveValueSet_four]
        simp
    · right
      refine ⟨⟨0, by decide⟩, 1, ?_, Real.sqrt 2, ?_, rfl⟩
      · simp [recursiveValueSet]
      · change Real.sqrt 2 ∈ recursiveValueSet 4
        rw [recursiveValueSet_four]
        simp
    · right
      refine ⟨⟨0, by decide⟩, 1, ?_, 2, ?_, by norm_num⟩
      · simp [recursiveValueSet]
      · change (2 : ℝ) ∈ recursiveValueSet 4
        rw [recursiveValueSet_four]
        simp

theorem recursiveValueSet_six_ncard :
    (recursiveValueSet 6).ncard = 8 := by
  rw [recursiveValueSet_six]
  have h1 :
      (1 : ℝ) ∉
        ({rt2_8, rt2_4, Real.sqrt 2, Real.sqrt 3, 2, 1 + Real.sqrt 2, 3} :
          Set ℝ) := by
    intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    have h1r8 : (1 : ℝ) < rt2_8 := by
      rw [rt2_8, rt2_4]
      simpa using
        (Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) one_lt_sqrt_sqrt_two)
    have h1s3 : (1 : ℝ) < Real.sqrt 3 :=
      Real.one_lt_sqrt_two.trans sqrt_two_lt_sqrt_three
    have h1add : (1 : ℝ) < 1 + Real.sqrt 2 := by
      have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num)
      linarith
    rcases h with h | h | h | h | h | h | h
    · exact (ne_of_lt h1r8) h
    · exact one_ne_sqrt_sqrt_two h
    · exact one_ne_sqrt_two h
    · exact (ne_of_lt h1s3) h
    · norm_num at h
    · exact (ne_of_lt h1add) h
    · norm_num at h
  have hr8 :
      rt2_8 ∉ ({rt2_4, Real.sqrt 2, Real.sqrt 3, 2, 1 + Real.sqrt 2, 3} :
        Set ℝ) := by
    intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    have hr8s2 : rt2_8 < Real.sqrt 2 := rt2_8_lt_rt2_4.trans sqrt_sqrt_two_lt_sqrt_two
    have hr8s3 : rt2_8 < Real.sqrt 3 := hr8s2.trans sqrt_two_lt_sqrt_three
    have hr8two : rt2_8 < (2 : ℝ) := hr8s2.trans sqrt_two_lt_two
    have hr8add : rt2_8 < 1 + Real.sqrt 2 := hr8two.trans two_lt_one_add_sqrt_two
    have hr8three : rt2_8 < (3 : ℝ) := hr8add.trans one_add_sqrt_two_lt_three
    rcases h with h | h | h | h | h | h
    · exact (ne_of_lt rt2_8_lt_rt2_4) h
    · exact (ne_of_lt hr8s2) h
    · exact (ne_of_lt hr8s3) h
    · exact (ne_of_lt hr8two) h
    · exact (ne_of_lt hr8add) h
    · exact (ne_of_lt hr8three) h
  have hr4 :
      rt2_4 ∉ ({Real.sqrt 2, Real.sqrt 3, 2, 1 + Real.sqrt 2, 3} : Set ℝ) := by
    intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    have hr4s3 : rt2_4 < Real.sqrt 3 :=
      sqrt_sqrt_two_lt_sqrt_two.trans sqrt_two_lt_sqrt_three
    have hr4two : rt2_4 < (2 : ℝ) :=
      sqrt_sqrt_two_lt_sqrt_two.trans sqrt_two_lt_two
    have hr4add : rt2_4 < 1 + Real.sqrt 2 := hr4two.trans two_lt_one_add_sqrt_two
    have hr4three : rt2_4 < (3 : ℝ) := hr4add.trans one_add_sqrt_two_lt_three
    rcases h with h | h | h | h | h
    · exact sqrt_sqrt_two_ne_sqrt_two h
    · exact (ne_of_lt hr4s3) h
    · exact (ne_of_lt hr4two) h
    · exact (ne_of_lt hr4add) h
    · exact (ne_of_lt hr4three) h
  have hs2 :
      Real.sqrt 2 ∉ ({Real.sqrt 3, 2, 1 + Real.sqrt 2, 3} : Set ℝ) := by
    intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    have hs2add : Real.sqrt 2 < 1 + Real.sqrt 2 := by norm_num
    have hs2three : Real.sqrt 2 < (3 : ℝ) :=
      sqrt_two_lt_two.trans (by norm_num : (2 : ℝ) < 3)
    rcases h with h | h | h | h
    · exact (ne_of_lt sqrt_two_lt_sqrt_three) h
    · exact sqrt_two_ne_two h
    · exact (ne_of_lt hs2add) h
    · exact (ne_of_lt hs2three) h
  have hs3 : Real.sqrt 3 ∉ ({2, 1 + Real.sqrt 2, 3} : Set ℝ) := by
    intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    have hs3add : Real.sqrt 3 < 1 + Real.sqrt 2 :=
      sqrt_three_lt_two.trans two_lt_one_add_sqrt_two
    have hs3three : Real.sqrt 3 < (3 : ℝ) :=
      sqrt_three_lt_two.trans (by norm_num : (2 : ℝ) < 3)
    rcases h with h | h | h
    · exact (ne_of_lt sqrt_three_lt_two) h
    · exact (ne_of_lt hs3add) h
    · exact (ne_of_lt hs3three) h
  have h2 : (2 : ℝ) ∉ ({1 + Real.sqrt 2, 3} : Set ℝ) := by
    intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h
    · exact (ne_of_lt two_lt_one_add_sqrt_two) h
    · norm_num at h
  have hadd : 1 + Real.sqrt 2 ∉ ({3} : Set ℝ) := by
    intro h
    simp only [Set.mem_singleton_iff] at h
    exact (ne_of_lt one_add_sqrt_two_lt_three) h
  rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem hr8,
    Set.ncard_insert_of_notMem hr4, Set.ncard_insert_of_notMem hs2,
    Set.ncard_insert_of_notMem hs3, Set.ncard_insert_of_notMem h2,
    Set.ncard_insert_of_notMem hadd, Set.ncard_singleton]

noncomputable def values7List : List ℝ :=
  [1, rt2_16, rt2_8, rt2_4, rt3_4, Real.sqrt 2, sqrt_one_add_sqrt_two,
    Real.sqrt 3, 2, 1 + rt2_4, 1 + Real.sqrt 2, 3, 4]

noncomputable def values7 (i : Fin 13) : ℝ :=
  values7List.getD i.1 0

theorem values7_strictMono : StrictMono values7 := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  have h34 : (3 : ℝ) < 4 := by norm_num
  fin_cases i <;>
    simp [values7, values7List] <;>
    linarith [one_lt_rt2_16, rt2_16_lt_rt2_8, rt2_8_lt_rt2_4,
      rt2_4_lt_rt3_4, rt3_4_lt_sqrt_two, sqrt_two_lt_sqrt_one_add_sqrt_two,
      sqrt_one_add_sqrt_two_lt_sqrt_three, sqrt_three_lt_two,
      two_lt_one_add_rt2_4, one_add_rt2_4_lt_one_add_sqrt_two,
      one_add_sqrt_two_lt_three, h34, Real.one_lt_sqrt_two,
      one_lt_sqrt_sqrt_two, one_lt_rt2_8, sqrt_sqrt_two_lt_sqrt_two,
      sqrt_two_lt_two, sqrt_two_lt_sqrt_three, two_lt_one_add_sqrt_two]

theorem values7_range_eq :
    Set.range values7 =
      ({1, rt2_16, rt2_8, rt2_4, rt3_4, Real.sqrt 2, sqrt_one_add_sqrt_two,
        Real.sqrt 3, 2, 1 + rt2_4, 1 + Real.sqrt 2, 3, 4} : Set ℝ) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [values7, values7List]
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨0, by decide⟩, by simp [values7, values7List]⟩
    · exact ⟨⟨1, by decide⟩, by simp [values7, values7List]⟩
    · exact ⟨⟨2, by decide⟩, by simp [values7, values7List]⟩
    · exact ⟨⟨3, by decide⟩, by simp [values7, values7List]⟩
    · exact ⟨⟨4, by decide⟩, by simp [values7, values7List]⟩
    · exact ⟨⟨5, by decide⟩, by simp [values7, values7List]⟩
    · exact ⟨⟨6, by decide⟩, by simp [values7, values7List]⟩
    · exact ⟨⟨7, by decide⟩, by simp [values7, values7List]⟩
    · exact ⟨⟨8, by decide⟩, by simp [values7, values7List]⟩
    · exact ⟨⟨9, by decide⟩, by simp [values7, values7List]⟩
    · exact ⟨⟨10, by decide⟩, by simp [values7, values7List]⟩
    · exact ⟨⟨11, by decide⟩, by simp [values7, values7List]⟩
    · exact ⟨⟨12, by decide⟩, by simp [values7, values7List]⟩

theorem recursiveValueSet_seven :
    recursiveValueSet 7 = Set.range values7 := by
  ext x
  constructor
  · intro hx
    rw [recursiveValueSet] at hx
    rcases hx with h | h
    · rcases h with ⟨y, hy, rfl⟩
      rw [recursiveValueSet_six] at hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨⟨0, by decide⟩, by simp [values7, values7List]⟩
      · exact ⟨⟨1, by decide⟩, by simp [values7, values7List, rt2_16]⟩
      · exact ⟨⟨2, by decide⟩, by simp [values7, values7List, rt2_8]⟩
      · exact ⟨⟨3, by decide⟩, by simp [values7, values7List, rt2_4]⟩
      · exact ⟨⟨4, by decide⟩, by simp [values7, values7List, rt3_4]⟩
      · exact ⟨⟨5, by decide⟩, by simp [values7, values7List]⟩
      · exact ⟨⟨6, by decide⟩, by simp [values7, values7List, sqrt_one_add_sqrt_two]⟩
      · exact ⟨⟨7, by decide⟩, by simp [values7, values7List]⟩
    · rcases h with ⟨k, a, ha, b, hb, rfl⟩
      fin_cases k
      · simp [recursiveValueSet] at ha
        have hb' : b ∈ recursiveValueSet 5 := by simpa using hb
        rw [recursiveValueSet_five] at hb'
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb'
        rcases ha with rfl
        rcases hb' with rfl | rfl | rfl | rfl | rfl
        · exact ⟨⟨8, by decide⟩, by norm_num [values7, values7List]⟩
        · exact ⟨⟨9, by decide⟩, by simp [values7, values7List, rt2_4]⟩
        · exact ⟨⟨10, by decide⟩, by simp [values7, values7List]⟩
        · exact ⟨⟨11, by decide⟩, by norm_num [values7, values7List]⟩
        · exact ⟨⟨12, by decide⟩, by norm_num [values7, values7List]⟩
      · rw [recursiveValueSet_two] at ha
        have hb' : b ∈ recursiveValueSet 4 := by simpa using hb
        rw [recursiveValueSet_four] at hb'
        simp only [Set.mem_singleton_iff] at ha
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb'
        rcases ha with rfl
        rcases hb' with rfl | rfl | rfl
        · exact ⟨⟨8, by decide⟩, by norm_num [values7, values7List]⟩
        · exact ⟨⟨10, by decide⟩, by simp [values7, values7List]⟩
        · exact ⟨⟨11, by decide⟩, by norm_num [values7, values7List]⟩
      · rw [recursiveValueSet_three] at ha
        have hb' : b ∈ recursiveValueSet 3 := by simpa using hb
        rw [recursiveValueSet_three] at hb'
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
        rcases ha with rfl | rfl
        · rcases hb' with rfl | rfl
          · exact ⟨⟨8, by decide⟩, by norm_num [values7, values7List]⟩
          · exact ⟨⟨11, by decide⟩, by norm_num [values7, values7List]⟩
        · rcases hb' with rfl | rfl
          · exact ⟨⟨11, by decide⟩, by norm_num [values7, values7List]⟩
          · exact ⟨⟨12, by decide⟩, by norm_num [values7, values7List]⟩
      · rw [recursiveValueSet_four] at ha
        have hb' : b ∈ recursiveValueSet 2 := by simpa using hb
        rw [recursiveValueSet_two] at hb'
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        simp only [Set.mem_singleton_iff] at hb'
        rcases ha with rfl | rfl | rfl
        · rcases hb' with rfl
          exact ⟨⟨8, by decide⟩, by norm_num [values7, values7List]⟩
        · rcases hb' with rfl
          exact ⟨⟨10, by decide⟩, by simp [values7, values7List, add_comm]⟩
        · rcases hb' with rfl
          exact ⟨⟨11, by decide⟩, by norm_num [values7, values7List]⟩
      · rw [recursiveValueSet_five] at ha
        simp [recursiveValueSet] at hb
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl
        · rcases hb with rfl
          exact ⟨⟨8, by decide⟩, by norm_num [values7, values7List]⟩
        · rcases hb with rfl
          exact ⟨⟨9, by decide⟩, by simp [values7, values7List, rt2_4, add_comm]⟩
        · rcases hb with rfl
          exact ⟨⟨10, by decide⟩, by simp [values7, values7List, add_comm]⟩
        · rcases hb with rfl
          exact ⟨⟨11, by decide⟩, by norm_num [values7, values7List]⟩
        · rcases hb with rfl
          exact ⟨⟨12, by decide⟩, by norm_num [values7, values7List]⟩
  · rintro ⟨i, rfl⟩
    fin_cases i
    · simp [values7, values7List, recursiveValueSet]
    · rw [recursiveValueSet]
      left
      refine ⟨rt2_8, ?_, by simp [values7, values7List, rt2_16]⟩
      rw [recursiveValueSet_six]
      simp
    · rw [recursiveValueSet]
      left
      refine ⟨rt2_4, ?_, by simp [values7, values7List, rt2_8]⟩
      rw [recursiveValueSet_six]
      simp
    · rw [recursiveValueSet]
      left
      refine ⟨Real.sqrt 2, ?_, by simp [values7, values7List, rt2_4]⟩
      rw [recursiveValueSet_six]
      simp
    · rw [recursiveValueSet]
      left
      refine ⟨Real.sqrt 3, ?_, by simp [values7, values7List, rt3_4]⟩
      rw [recursiveValueSet_six]
      simp
    · rw [recursiveValueSet]
      left
      refine ⟨2, ?_, by simp [values7, values7List]⟩
      rw [recursiveValueSet_six]
      simp
    · rw [recursiveValueSet]
      left
      refine ⟨1 + Real.sqrt 2, ?_, by simp [values7, values7List, sqrt_one_add_sqrt_two]⟩
      rw [recursiveValueSet_six]
      simp
    · rw [recursiveValueSet]
      left
      refine ⟨3, ?_, by simp [values7, values7List]⟩
      rw [recursiveValueSet_six]
      simp
    · change (2 : ℝ) ∈ recursiveValueSet 7
      rw [recursiveValueSet]
      right
      refine ⟨⟨0, by decide⟩, 1, ?_, 1, ?_, by norm_num⟩
      · simp [recursiveValueSet]
      · change (1 : ℝ) ∈ recursiveValueSet 5
        rw [recursiveValueSet_five]
        simp
    · change 1 + rt2_4 ∈ recursiveValueSet 7
      rw [recursiveValueSet]
      right
      refine ⟨⟨0, by decide⟩, 1, ?_, rt2_4, ?_, rfl⟩
      · simp [recursiveValueSet]
      · change rt2_4 ∈ recursiveValueSet 5
        rw [recursiveValueSet_five]
        simp [rt2_4]
    · change 1 + Real.sqrt 2 ∈ recursiveValueSet 7
      rw [recursiveValueSet]
      right
      refine ⟨⟨0, by decide⟩, 1, ?_, Real.sqrt 2, ?_, rfl⟩
      · simp [recursiveValueSet]
      · change Real.sqrt 2 ∈ recursiveValueSet 5
        rw [recursiveValueSet_five]
        simp
    · change (3 : ℝ) ∈ recursiveValueSet 7
      rw [recursiveValueSet]
      right
      refine ⟨⟨0, by decide⟩, 1, ?_, 2, ?_, by norm_num⟩
      · simp [recursiveValueSet]
      · change (2 : ℝ) ∈ recursiveValueSet 5
        rw [recursiveValueSet_five]
        simp
    · change (4 : ℝ) ∈ recursiveValueSet 7
      rw [recursiveValueSet]
      right
      refine ⟨⟨0, by decide⟩, 1, ?_, 3, ?_, by norm_num⟩
      · simp [recursiveValueSet]
      · change (3 : ℝ) ∈ recursiveValueSet 5
        rw [recursiveValueSet_five]
        simp

theorem recursiveValueSet_seven_ncard :
    (recursiveValueSet 7).ncard = 13 := by
  rw [recursiveValueSet_seven]
  rw [Set.ncard_range_of_injective values7_strictMono.injective]
  norm_num

noncomputable abbrev rt2_32 : ℝ := Real.sqrt rt2_16

noncomputable abbrev rt3_8 : ℝ := Real.sqrt rt3_4

noncomputable abbrev sqrt_sqrt_one_add_sqrt_two : ℝ :=
  Real.sqrt sqrt_one_add_sqrt_two

noncomputable abbrev sqrt_one_add_rt2_4 : ℝ := Real.sqrt (1 + rt2_4)

theorem rt2_32_lt_rt2_16 : rt2_32 < rt2_16 := by
  rw [rt2_32]
  exact sqrt_lt_self_of_one_lt one_lt_rt2_16

theorem one_lt_rt2_32 : (1 : ℝ) < rt2_32 := by
  rw [rt2_32]
  simpa using
    (Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) one_lt_rt2_16)

theorem rt2_8_lt_rt3_8 : rt2_8 < rt3_8 := by
  rw [rt2_8, rt3_8]
  have hnon : (0 : ℝ) ≤ rt2_4 := by
    rw [rt2_4]
    exact Real.sqrt_nonneg (Real.sqrt 2)
  exact Real.sqrt_lt_sqrt hnon rt2_4_lt_rt3_4

theorem rt3_8_lt_rt2_4 : rt3_8 < rt2_4 := by
  rw [rt3_8]
  have hnon3 : (0 : ℝ) ≤ rt3_4 := by
    rw [rt3_4]
    exact Real.sqrt_nonneg (Real.sqrt 3)
  have hnon2 : (0 : ℝ) ≤ rt2_4 := by
    rw [rt2_4]
    exact Real.sqrt_nonneg (Real.sqrt 2)
  exact
    (Real.sqrt_lt (x := rt3_4) (y := rt2_4) hnon3 hnon2).2 (by
      rw [rt2_4, Real.sq_sqrt (Real.sqrt_nonneg 2)]
      exact rt3_4_lt_sqrt_two)

theorem rt2_4_lt_sqrt_sqrt_one_add_sqrt_two :
    rt2_4 < sqrt_sqrt_one_add_sqrt_two := by
  rw [rt2_4, sqrt_sqrt_one_add_sqrt_two]
  exact
    Real.sqrt_lt_sqrt (Real.sqrt_nonneg 2) sqrt_two_lt_sqrt_one_add_sqrt_two

theorem sqrt_sqrt_one_add_sqrt_two_lt_rt3_4 :
    sqrt_sqrt_one_add_sqrt_two < rt3_4 := by
  rw [sqrt_sqrt_one_add_sqrt_two, rt3_4]
  exact
    Real.sqrt_lt_sqrt (Real.sqrt_nonneg (1 + Real.sqrt 2))
      sqrt_one_add_sqrt_two_lt_sqrt_three

theorem sqrt_two_lt_sqrt_one_add_rt2_4 :
    Real.sqrt 2 < sqrt_one_add_rt2_4 := by
  rw [sqrt_one_add_rt2_4]
  exact Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 2) two_lt_one_add_rt2_4

theorem sqrt_one_add_rt2_4_lt_sqrt_one_add_sqrt_two :
    sqrt_one_add_rt2_4 < sqrt_one_add_sqrt_two := by
  rw [sqrt_one_add_rt2_4, sqrt_one_add_sqrt_two]
  have hnon : (0 : ℝ) ≤ 1 + rt2_4 := by
    have h : (0 : ℝ) ≤ rt2_4 := by
      rw [rt2_4]
      exact Real.sqrt_nonneg (Real.sqrt 2)
    linarith
  exact
    Real.sqrt_lt_sqrt hnon
      one_add_rt2_4_lt_one_add_sqrt_two

theorem two_lt_one_add_rt2_8 : (2 : ℝ) < 1 + rt2_8 := by
  linarith [one_lt_rt2_8]

theorem one_add_rt2_8_lt_one_add_rt2_4 : 1 + rt2_8 < 1 + rt2_4 := by
  linarith [rt2_8_lt_rt2_4]

theorem one_add_sqrt_two_lt_one_add_sqrt_three :
    1 + Real.sqrt 2 < 1 + Real.sqrt 3 := by
  linarith [sqrt_two_lt_sqrt_three]

theorem one_add_sqrt_three_lt_three : 1 + Real.sqrt 3 < (3 : ℝ) := by
  linarith [sqrt_three_lt_two]

theorem three_lt_two_add_sqrt_two : (3 : ℝ) < 2 + Real.sqrt 2 := by
  linarith [Real.one_lt_sqrt_two]

theorem two_add_sqrt_two_lt_four : 2 + Real.sqrt 2 < (4 : ℝ) := by
  linarith [sqrt_two_lt_two]

noncomputable def values8List : List ℝ :=
  [1, rt2_32, rt2_16, rt2_8, rt3_8, rt2_4,
    sqrt_sqrt_one_add_sqrt_two, rt3_4, Real.sqrt 2, sqrt_one_add_rt2_4,
    sqrt_one_add_sqrt_two, Real.sqrt 3, 2, 1 + rt2_8, 1 + rt2_4,
    1 + Real.sqrt 2, 1 + Real.sqrt 3, 3, 2 + Real.sqrt 2, 4]

noncomputable def values8 (i : Fin 20) : ℝ :=
  values8List.getD i.1 0

theorem values8_strictMono : StrictMono values8 := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  have h34 : (3 : ℝ) < 4 := by norm_num
  fin_cases i <;>
    simp [values8, values8List] <;>
    linarith [one_lt_rt2_32, rt2_32_lt_rt2_16, rt2_16_lt_rt2_8,
      rt2_8_lt_rt3_8, rt3_8_lt_rt2_4,
      rt2_4_lt_sqrt_sqrt_one_add_sqrt_two,
      sqrt_sqrt_one_add_sqrt_two_lt_rt3_4, rt3_4_lt_sqrt_two,
      sqrt_two_lt_sqrt_one_add_rt2_4,
      sqrt_one_add_rt2_4_lt_sqrt_one_add_sqrt_two,
      sqrt_one_add_sqrt_two_lt_sqrt_three, sqrt_three_lt_two,
      two_lt_one_add_rt2_8, one_add_rt2_8_lt_one_add_rt2_4,
      one_add_rt2_4_lt_one_add_sqrt_two,
      one_add_sqrt_two_lt_one_add_sqrt_three, one_add_sqrt_three_lt_three,
      three_lt_two_add_sqrt_two, two_add_sqrt_two_lt_four, h34,
      Real.one_lt_sqrt_two, one_lt_sqrt_sqrt_two, one_lt_rt2_8,
      one_lt_rt2_16, sqrt_sqrt_two_lt_sqrt_two, sqrt_two_lt_two,
      sqrt_two_lt_sqrt_three, two_lt_one_add_sqrt_two,
      one_add_sqrt_two_lt_three]

theorem recursiveValueSet_eight :
    recursiveValueSet 8 = Set.range values8 := by
  ext x
  constructor
  · intro hx
    rw [recursiveValueSet] at hx
    rcases hx with h | h
    · rcases h with ⟨y, hy, rfl⟩
      rw [recursiveValueSet_seven] at hy
      rcases hy with ⟨i, rfl⟩
      fin_cases i
      · exact ⟨⟨0, by decide⟩, by norm_num [values7, values7List, values8, values8List]⟩
      · exact ⟨⟨1, by decide⟩, by simp [values7, values7List, values8, values8List, rt2_32]⟩
      · exact ⟨⟨2, by decide⟩, by simp [values7, values7List, values8, values8List, rt2_16]⟩
      · exact ⟨⟨3, by decide⟩, by simp [values7, values7List, values8, values8List, rt2_8]⟩
      · exact ⟨⟨4, by decide⟩, by simp [values7, values7List, values8, values8List, rt3_8]⟩
      · exact ⟨⟨5, by decide⟩, by simp [values7, values7List, values8, values8List, rt2_4]⟩
      · exact ⟨⟨6, by decide⟩, by
          simp [values7, values7List, values8, values8List,
            sqrt_sqrt_one_add_sqrt_two]⟩
      · exact ⟨⟨7, by decide⟩, by simp [values7, values7List, values8, values8List, rt3_4]⟩
      · exact ⟨⟨8, by decide⟩, by simp [values7, values7List, values8, values8List]⟩
      · exact ⟨⟨9, by decide⟩, by
          simp [values7, values7List, values8, values8List, sqrt_one_add_rt2_4]⟩
      · exact ⟨⟨10, by decide⟩, by
          simp [values7, values7List, values8, values8List, sqrt_one_add_sqrt_two]⟩
      · exact ⟨⟨11, by decide⟩, by simp [values7, values7List, values8, values8List]⟩
      · exact ⟨⟨12, by decide⟩, by
          simp [values7, values7List, values8, values8List, sqrt_four]⟩
    · rcases h with ⟨k, a, ha, b, hb, rfl⟩
      fin_cases k
      · simp [recursiveValueSet] at ha
        have hb' : b ∈ recursiveValueSet 6 := by simpa using hb
        rw [recursiveValueSet_six] at hb'
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb'
        rcases ha with rfl
        rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨⟨12, by decide⟩, by norm_num [values8, values8List]⟩
        · exact ⟨⟨13, by decide⟩, by simp [values8, values8List]⟩
        · exact ⟨⟨14, by decide⟩, by simp [values8, values8List]⟩
        · exact ⟨⟨15, by decide⟩, by simp [values8, values8List]⟩
        · exact ⟨⟨16, by decide⟩, by simp [values8, values8List]⟩
        · exact ⟨⟨17, by decide⟩, by norm_num [values8, values8List]⟩
        · exact ⟨⟨18, by decide⟩, by
            norm_num [values8, values8List]
            linarith⟩
        · exact ⟨⟨19, by decide⟩, by norm_num [values8, values8List]⟩
      · rw [recursiveValueSet_two] at ha
        have hb' : b ∈ recursiveValueSet 5 := by simpa using hb
        rw [recursiveValueSet_five] at hb'
        simp only [Set.mem_singleton_iff] at ha
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb'
        rcases ha with rfl
        rcases hb' with rfl | rfl | rfl | rfl | rfl
        · exact ⟨⟨12, by decide⟩, by norm_num [values8, values8List]⟩
        · exact ⟨⟨14, by decide⟩, by simp [values8, values8List, rt2_4]⟩
        · exact ⟨⟨15, by decide⟩, by simp [values8, values8List]⟩
        · exact ⟨⟨17, by decide⟩, by norm_num [values8, values8List]⟩
        · exact ⟨⟨19, by decide⟩, by norm_num [values8, values8List]⟩
      · rw [recursiveValueSet_three] at ha
        have hb' : b ∈ recursiveValueSet 4 := by simpa using hb
        rw [recursiveValueSet_four] at hb'
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb'
        rcases ha with rfl | rfl
        · rcases hb' with rfl | rfl | rfl
          · exact ⟨⟨12, by decide⟩, by norm_num [values8, values8List]⟩
          · exact ⟨⟨15, by decide⟩, by simp [values8, values8List]⟩
          · exact ⟨⟨17, by decide⟩, by norm_num [values8, values8List]⟩
        · rcases hb' with rfl | rfl | rfl
          · exact ⟨⟨17, by decide⟩, by norm_num [values8, values8List]⟩
          · exact ⟨⟨18, by decide⟩, by simp [values8, values8List]⟩
          · exact ⟨⟨19, by decide⟩, by norm_num [values8, values8List]⟩
      · rw [recursiveValueSet_four] at ha
        have hb' : b ∈ recursiveValueSet 3 := by simpa using hb
        rw [recursiveValueSet_three] at hb'
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb'
        rcases ha with rfl | rfl | rfl
        · rcases hb' with rfl | rfl
          · exact ⟨⟨12, by decide⟩, by norm_num [values8, values8List]⟩
          · exact ⟨⟨17, by decide⟩, by norm_num [values8, values8List]⟩
        · rcases hb' with rfl | rfl
          · exact ⟨⟨15, by decide⟩, by simp [values8, values8List, add_comm]⟩
          · exact ⟨⟨18, by decide⟩, by simp [values8, values8List, add_comm]⟩
        · rcases hb' with rfl | rfl
          · exact ⟨⟨17, by decide⟩, by norm_num [values8, values8List]⟩
          · exact ⟨⟨19, by decide⟩, by norm_num [values8, values8List]⟩
      · rw [recursiveValueSet_five] at ha
        have hb' : b ∈ recursiveValueSet 2 := by simpa using hb
        rw [recursiveValueSet_two] at hb'
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        simp only [Set.mem_singleton_iff] at hb'
        rcases ha with rfl | rfl | rfl | rfl | rfl
        · rcases hb' with rfl
          exact ⟨⟨12, by decide⟩, by norm_num [values8, values8List]⟩
        · rcases hb' with rfl
          exact ⟨⟨14, by decide⟩, by simp [values8, values8List, rt2_4, add_comm]⟩
        · rcases hb' with rfl
          exact ⟨⟨15, by decide⟩, by simp [values8, values8List, add_comm]⟩
        · rcases hb' with rfl
          exact ⟨⟨17, by decide⟩, by norm_num [values8, values8List]⟩
        · rcases hb' with rfl
          exact ⟨⟨19, by decide⟩, by norm_num [values8, values8List]⟩
      · rw [recursiveValueSet_six] at ha
        simp [recursiveValueSet] at hb
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · rcases hb with rfl
          exact ⟨⟨12, by decide⟩, by norm_num [values8, values8List]⟩
        · rcases hb with rfl
          exact ⟨⟨13, by decide⟩, by simp [values8, values8List, add_comm]⟩
        · rcases hb with rfl
          exact ⟨⟨14, by decide⟩, by simp [values8, values8List, add_comm]⟩
        · rcases hb with rfl
          exact ⟨⟨15, by decide⟩, by simp [values8, values8List, add_comm]⟩
        · rcases hb with rfl
          exact ⟨⟨16, by decide⟩, by simp [values8, values8List, add_comm]⟩
        · rcases hb with rfl
          exact ⟨⟨17, by decide⟩, by norm_num [values8, values8List]⟩
        · rcases hb with rfl
          exact ⟨⟨18, by decide⟩, by
            norm_num [values8, values8List]
            linarith⟩
        · rcases hb with rfl
          exact ⟨⟨19, by decide⟩, by norm_num [values8, values8List]⟩
  · rintro ⟨i, rfl⟩
    fin_cases i
    · change (1 : ℝ) ∈ recursiveValueSet 8
      rw [recursiveValueSet]
      left
      refine ⟨1, ?_, by norm_num⟩
      rw [recursiveValueSet_seven]
      exact ⟨⟨0, by decide⟩, by simp [values7, values7List]⟩
    · change rt2_32 ∈ recursiveValueSet 8
      rw [recursiveValueSet]
      left
      refine ⟨rt2_16, ?_, by simp [rt2_32]⟩
      rw [recursiveValueSet_seven]
      exact ⟨⟨1, by decide⟩, by simp [values7, values7List]⟩
    · change rt2_16 ∈ recursiveValueSet 8
      rw [recursiveValueSet]
      left
      refine ⟨rt2_8, ?_, by simp [rt2_16]⟩
      rw [recursiveValueSet_seven]
      exact ⟨⟨2, by decide⟩, by simp [values7, values7List]⟩
    · change rt2_8 ∈ recursiveValueSet 8
      rw [recursiveValueSet]
      left
      refine ⟨rt2_4, ?_, by simp [rt2_8]⟩
      rw [recursiveValueSet_seven]
      exact ⟨⟨3, by decide⟩, by simp [values7, values7List]⟩
    · change rt3_8 ∈ recursiveValueSet 8
      rw [recursiveValueSet]
      left
      refine ⟨rt3_4, ?_, by simp [rt3_8]⟩
      rw [recursiveValueSet_seven]
      exact ⟨⟨4, by decide⟩, by simp [values7, values7List]⟩
    · change rt2_4 ∈ recursiveValueSet 8
      rw [recursiveValueSet]
      left
      refine ⟨Real.sqrt 2, ?_, by simp [rt2_4]⟩
      rw [recursiveValueSet_seven]
      exact ⟨⟨5, by decide⟩, by simp [values7, values7List]⟩
    · change sqrt_sqrt_one_add_sqrt_two ∈ recursiveValueSet 8
      rw [recursiveValueSet]
      left
      refine ⟨sqrt_one_add_sqrt_two, ?_, by simp [sqrt_sqrt_one_add_sqrt_two]⟩
      rw [recursiveValueSet_seven]
      exact ⟨⟨6, by decide⟩, by simp [values7, values7List]⟩
    · change rt3_4 ∈ recursiveValueSet 8
      rw [recursiveValueSet]
      left
      refine ⟨Real.sqrt 3, ?_, by simp [rt3_4]⟩
      rw [recursiveValueSet_seven]
      exact ⟨⟨7, by decide⟩, by simp [values7, values7List]⟩
    · change Real.sqrt 2 ∈ recursiveValueSet 8
      rw [recursiveValueSet]
      left
      refine ⟨2, ?_, by simp⟩
      rw [recursiveValueSet_seven]
      exact ⟨⟨8, by decide⟩, by simp [values7, values7List]⟩
    · change sqrt_one_add_rt2_4 ∈ recursiveValueSet 8
      rw [recursiveValueSet]
      left
      refine ⟨1 + rt2_4, ?_, by simp [sqrt_one_add_rt2_4]⟩
      rw [recursiveValueSet_seven]
      exact ⟨⟨9, by decide⟩, by simp [values7, values7List]⟩
    · change sqrt_one_add_sqrt_two ∈ recursiveValueSet 8
      rw [recursiveValueSet]
      left
      refine ⟨1 + Real.sqrt 2, ?_, by simp [sqrt_one_add_sqrt_two]⟩
      rw [recursiveValueSet_seven]
      exact ⟨⟨10, by decide⟩, by simp [values7, values7List]⟩
    · change Real.sqrt 3 ∈ recursiveValueSet 8
      rw [recursiveValueSet]
      left
      refine ⟨3, ?_, by simp⟩
      rw [recursiveValueSet_seven]
      exact ⟨⟨11, by decide⟩, by simp [values7, values7List]⟩
    · change (2 : ℝ) ∈ recursiveValueSet 8
      rw [recursiveValueSet]
      left
      refine ⟨4, ?_, by simp [sqrt_four]⟩
      rw [recursiveValueSet_seven]
      exact ⟨⟨12, by decide⟩, by simp [values7, values7List]⟩
    · change 1 + rt2_8 ∈ recursiveValueSet 8
      rw [recursiveValueSet]
      right
      refine ⟨⟨0, by decide⟩, 1, ?_, rt2_8, ?_, rfl⟩
      · simp [recursiveValueSet]
      · change rt2_8 ∈ recursiveValueSet 6
        rw [recursiveValueSet_six]
        simp
    · change 1 + rt2_4 ∈ recursiveValueSet 8
      rw [recursiveValueSet]
      right
      refine ⟨⟨0, by decide⟩, 1, ?_, rt2_4, ?_, rfl⟩
      · simp [recursiveValueSet]
      · change rt2_4 ∈ recursiveValueSet 6
        rw [recursiveValueSet_six]
        simp
    · change 1 + Real.sqrt 2 ∈ recursiveValueSet 8
      rw [recursiveValueSet]
      right
      refine ⟨⟨0, by decide⟩, 1, ?_, Real.sqrt 2, ?_, rfl⟩
      · simp [recursiveValueSet]
      · change Real.sqrt 2 ∈ recursiveValueSet 6
        rw [recursiveValueSet_six]
        simp
    · change 1 + Real.sqrt 3 ∈ recursiveValueSet 8
      rw [recursiveValueSet]
      right
      refine ⟨⟨0, by decide⟩, 1, ?_, Real.sqrt 3, ?_, rfl⟩
      · simp [recursiveValueSet]
      · change Real.sqrt 3 ∈ recursiveValueSet 6
        rw [recursiveValueSet_six]
        simp
    · change (3 : ℝ) ∈ recursiveValueSet 8
      rw [recursiveValueSet]
      right
      refine ⟨⟨0, by decide⟩, 1, ?_, 2, ?_, by norm_num⟩
      · simp [recursiveValueSet]
      · change (2 : ℝ) ∈ recursiveValueSet 6
        rw [recursiveValueSet_six]
        simp
    · change 2 + Real.sqrt 2 ∈ recursiveValueSet 8
      rw [recursiveValueSet]
      right
      refine ⟨⟨2, by decide⟩, 2, ?_, Real.sqrt 2, ?_, rfl⟩
      · change (2 : ℝ) ∈ recursiveValueSet 3
        rw [recursiveValueSet_three]
        simp
      · change Real.sqrt 2 ∈ recursiveValueSet 4
        rw [recursiveValueSet_four]
        simp
    · change (4 : ℝ) ∈ recursiveValueSet 8
      rw [recursiveValueSet]
      right
      refine ⟨⟨0, by decide⟩, 1, ?_, 3, ?_, by norm_num⟩
      · simp [recursiveValueSet]
      · change (3 : ℝ) ∈ recursiveValueSet 6
        rw [recursiveValueSet_six]
        simp

theorem recursiveValueSet_eight_ncard :
    (recursiveValueSet 8).ncard = 20 := by
  rw [recursiveValueSet_eight]
  rw [Set.ncard_range_of_injective values8_strictMono.injective]
  norm_num

noncomputable abbrev rt2_64 : ℝ := Real.sqrt rt2_32

noncomputable abbrev rt3_16 : ℝ := Real.sqrt rt3_8

noncomputable abbrev sqrt_sqrt_sqrt_one_add_sqrt_two : ℝ :=
  Real.sqrt sqrt_sqrt_one_add_sqrt_two

noncomputable abbrev sqrt_sqrt_one_add_rt2_4 : ℝ :=
  Real.sqrt sqrt_one_add_rt2_4

noncomputable abbrev sqrt_one_add_rt2_8 : ℝ := Real.sqrt (1 + rt2_8)

noncomputable abbrev sqrt_one_add_sqrt_three : ℝ := Real.sqrt (1 + Real.sqrt 3)

noncomputable abbrev sqrt_two_add_sqrt_two : ℝ := Real.sqrt (2 + Real.sqrt 2)

theorem rt2_64_lt_rt2_32 : rt2_64 < rt2_32 := by
  rw [rt2_64]
  exact sqrt_lt_self_of_one_lt one_lt_rt2_32

theorem one_lt_rt2_64 : (1 : ℝ) < rt2_64 := by
  rw [rt2_64]
  simpa using
    (Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) one_lt_rt2_32)

theorem rt2_16_lt_rt3_16 : rt2_16 < rt3_16 := by
  rw [rt2_16, rt3_16]
  have hnon : (0 : ℝ) ≤ rt2_8 := by
    rw [rt2_8]
    exact Real.sqrt_nonneg rt2_4
  exact Real.sqrt_lt_sqrt hnon rt2_8_lt_rt3_8

theorem rt3_16_lt_rt2_8 : rt3_16 < rt2_8 := by
  rw [rt3_16]
  have hnon3 : (0 : ℝ) ≤ rt3_8 := by
    rw [rt3_8]
    exact Real.sqrt_nonneg rt3_4
  have hnon2 : (0 : ℝ) ≤ rt2_8 := by
    rw [rt2_8]
    exact Real.sqrt_nonneg rt2_4
  exact
    (Real.sqrt_lt (x := rt3_8) (y := rt2_8) hnon3 hnon2).2 (by
      rw [rt2_8, Real.sq_sqrt]
      · exact rt3_8_lt_rt2_4
      · rw [rt2_4]
        exact Real.sqrt_nonneg (Real.sqrt 2))

theorem rt2_8_lt_sqrt_sqrt_sqrt_one_add_sqrt_two :
    rt2_8 < sqrt_sqrt_sqrt_one_add_sqrt_two := by
  rw [rt2_8, sqrt_sqrt_sqrt_one_add_sqrt_two]
  have hnon : (0 : ℝ) ≤ rt2_4 := by
    rw [rt2_4]
    exact Real.sqrt_nonneg (Real.sqrt 2)
  exact Real.sqrt_lt_sqrt hnon rt2_4_lt_sqrt_sqrt_one_add_sqrt_two

theorem sqrt_sqrt_sqrt_one_add_sqrt_two_lt_rt3_8 :
    sqrt_sqrt_sqrt_one_add_sqrt_two < rt3_8 := by
  rw [sqrt_sqrt_sqrt_one_add_sqrt_two, rt3_8]
  have hnon : (0 : ℝ) ≤ sqrt_sqrt_one_add_sqrt_two := by
    rw [sqrt_sqrt_one_add_sqrt_two]
    exact Real.sqrt_nonneg sqrt_one_add_sqrt_two
  exact
    Real.sqrt_lt_sqrt hnon
      sqrt_sqrt_one_add_sqrt_two_lt_rt3_4

theorem rt2_4_lt_sqrt_sqrt_one_add_rt2_4 :
    rt2_4 < sqrt_sqrt_one_add_rt2_4 := by
  rw [rt2_4, sqrt_sqrt_one_add_rt2_4]
  exact
    Real.sqrt_lt_sqrt (Real.sqrt_nonneg 2) sqrt_two_lt_sqrt_one_add_rt2_4

theorem sqrt_sqrt_one_add_rt2_4_lt_sqrt_sqrt_one_add_sqrt_two :
    sqrt_sqrt_one_add_rt2_4 < sqrt_sqrt_one_add_sqrt_two := by
  rw [sqrt_sqrt_one_add_rt2_4, sqrt_sqrt_one_add_sqrt_two]
  have hnon : (0 : ℝ) ≤ sqrt_one_add_rt2_4 := by
    rw [sqrt_one_add_rt2_4]
    exact Real.sqrt_nonneg (1 + rt2_4)
  exact
    Real.sqrt_lt_sqrt hnon
      sqrt_one_add_rt2_4_lt_sqrt_one_add_sqrt_two

theorem sqrt_two_lt_sqrt_one_add_rt2_8 :
    Real.sqrt 2 < sqrt_one_add_rt2_8 := by
  rw [sqrt_one_add_rt2_8]
  exact Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 2) two_lt_one_add_rt2_8

theorem sqrt_one_add_rt2_8_lt_sqrt_one_add_rt2_4 :
    sqrt_one_add_rt2_8 < sqrt_one_add_rt2_4 := by
  rw [sqrt_one_add_rt2_8, sqrt_one_add_rt2_4]
  have hnon : (0 : ℝ) ≤ 1 + rt2_8 := by
    have h : (0 : ℝ) ≤ rt2_8 := by
      rw [rt2_8]
      exact Real.sqrt_nonneg rt2_4
    linarith
  exact Real.sqrt_lt_sqrt hnon one_add_rt2_8_lt_one_add_rt2_4

theorem sqrt_one_add_sqrt_two_lt_sqrt_one_add_sqrt_three :
    sqrt_one_add_sqrt_two < sqrt_one_add_sqrt_three := by
  rw [sqrt_one_add_sqrt_two, sqrt_one_add_sqrt_three]
  exact
    Real.sqrt_lt_sqrt (by nlinarith [Real.sqrt_nonneg 2])
      one_add_sqrt_two_lt_one_add_sqrt_three

theorem sqrt_one_add_sqrt_three_lt_sqrt_three :
    sqrt_one_add_sqrt_three < Real.sqrt 3 := by
  rw [sqrt_one_add_sqrt_three]
  exact
    Real.sqrt_lt_sqrt (by nlinarith [Real.sqrt_nonneg 3])
      one_add_sqrt_three_lt_three

theorem sqrt_three_lt_sqrt_two_add_sqrt_two :
    Real.sqrt 3 < sqrt_two_add_sqrt_two := by
  rw [sqrt_two_add_sqrt_two]
  exact
    Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 3) three_lt_two_add_sqrt_two

theorem sqrt_two_add_sqrt_two_lt_two : sqrt_two_add_sqrt_two < (2 : ℝ) := by
  rw [sqrt_two_add_sqrt_two]
  have h :
      Real.sqrt (2 + Real.sqrt 2) < Real.sqrt 4 := by
    exact
      Real.sqrt_lt_sqrt (by nlinarith [Real.sqrt_nonneg 2])
        two_add_sqrt_two_lt_four
  simpa [sqrt_four] using h

theorem two_lt_one_add_rt2_16 : (2 : ℝ) < 1 + rt2_16 := by
  linarith [one_lt_rt2_16]

theorem one_add_rt2_16_lt_one_add_rt2_8 : 1 + rt2_16 < 1 + rt2_8 := by
  linarith [rt2_16_lt_rt2_8]

theorem one_add_rt2_4_lt_one_add_rt3_4 : 1 + rt2_4 < 1 + rt3_4 := by
  linarith [rt2_4_lt_rt3_4]

theorem one_add_rt3_4_lt_one_add_sqrt_two : 1 + rt3_4 < 1 + Real.sqrt 2 := by
  linarith [rt3_4_lt_sqrt_two]

theorem one_add_sqrt_two_lt_one_add_sqrt_one_add_sqrt_two :
    1 + Real.sqrt 2 < 1 + sqrt_one_add_sqrt_two := by
  linarith [sqrt_two_lt_sqrt_one_add_sqrt_two]

theorem one_add_sqrt_one_add_sqrt_two_lt_one_add_sqrt_three :
    1 + sqrt_one_add_sqrt_two < 1 + Real.sqrt 3 := by
  linarith [sqrt_one_add_sqrt_two_lt_sqrt_three]

theorem one_add_sqrt_three_lt_two_mul_sqrt_two :
    1 + Real.sqrt 3 < 2 * Real.sqrt 2 := by
  have hleft : (0 : ℝ) ≤ 1 + Real.sqrt 3 := by
    have h : (0 : ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
    linarith
  have hright : (0 : ℝ) ≤ 2 * Real.sqrt 2 := by
    have h : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    nlinarith
  apply (sq_lt_sq₀ hleft hright).1
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), sqrt_three_lt_two]

theorem two_mul_sqrt_two_lt_three : 2 * Real.sqrt 2 < (3 : ℝ) := by
  linarith [Real.sqrt_two_lt_three_halves]

theorem three_lt_two_add_rt2_4 : (3 : ℝ) < 2 + rt2_4 := by
  linarith [one_lt_sqrt_sqrt_two]

theorem two_add_rt2_4_lt_two_add_sqrt_two : 2 + rt2_4 < 2 + Real.sqrt 2 := by
  linarith [sqrt_sqrt_two_lt_sqrt_two]

theorem four_lt_five : (4 : ℝ) < 5 := by
  norm_num

noncomputable def values9List : List ℝ :=
  [1, rt2_64, rt2_32, rt2_16, rt3_16, rt2_8,
    sqrt_sqrt_sqrt_one_add_sqrt_two, rt3_8, rt2_4,
    sqrt_sqrt_one_add_rt2_4, sqrt_sqrt_one_add_sqrt_two, rt3_4,
    Real.sqrt 2, sqrt_one_add_rt2_8, sqrt_one_add_rt2_4,
    sqrt_one_add_sqrt_two, sqrt_one_add_sqrt_three, Real.sqrt 3,
    sqrt_two_add_sqrt_two, 2, 1 + rt2_16, 1 + rt2_8, 1 + rt2_4,
    1 + rt3_4, 1 + Real.sqrt 2, 1 + sqrt_one_add_sqrt_two,
    1 + Real.sqrt 3, 2 * Real.sqrt 2, 3, 2 + rt2_4, 2 + Real.sqrt 2, 4, 5]

noncomputable def values9 (i : Fin 33) : ℝ :=
  values9List.getD i.1 0

theorem values9_strictMono : StrictMono values9 := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  have h34 : (3 : ℝ) < 4 := by norm_num
  fin_cases i <;>
    simp [values9, values9List] <;>
    linarith [one_lt_rt2_64, rt2_64_lt_rt2_32, rt2_32_lt_rt2_16,
      rt2_16_lt_rt3_16, rt3_16_lt_rt2_8,
      rt2_8_lt_sqrt_sqrt_sqrt_one_add_sqrt_two,
      sqrt_sqrt_sqrt_one_add_sqrt_two_lt_rt3_8, rt3_8_lt_rt2_4,
      rt2_4_lt_sqrt_sqrt_one_add_rt2_4,
      sqrt_sqrt_one_add_rt2_4_lt_sqrt_sqrt_one_add_sqrt_two,
      sqrt_sqrt_one_add_sqrt_two_lt_rt3_4, rt3_4_lt_sqrt_two,
      sqrt_two_lt_sqrt_one_add_rt2_8,
      sqrt_one_add_rt2_8_lt_sqrt_one_add_rt2_4,
      sqrt_one_add_rt2_4_lt_sqrt_one_add_sqrt_two,
      sqrt_one_add_sqrt_two_lt_sqrt_one_add_sqrt_three,
      sqrt_one_add_sqrt_three_lt_sqrt_three,
      sqrt_three_lt_sqrt_two_add_sqrt_two, sqrt_two_add_sqrt_two_lt_two,
      two_lt_one_add_rt2_16, one_add_rt2_16_lt_one_add_rt2_8,
      one_add_rt2_8_lt_one_add_rt2_4, one_add_rt2_4_lt_one_add_rt3_4,
      one_add_rt3_4_lt_one_add_sqrt_two,
      one_add_sqrt_two_lt_one_add_sqrt_one_add_sqrt_two,
      one_add_sqrt_one_add_sqrt_two_lt_one_add_sqrt_three,
      one_add_sqrt_three_lt_two_mul_sqrt_two, two_mul_sqrt_two_lt_three,
      three_lt_two_add_rt2_4, two_add_rt2_4_lt_two_add_sqrt_two,
      two_add_sqrt_two_lt_four, h34, four_lt_five, Real.one_lt_sqrt_two,
      one_lt_sqrt_sqrt_two, one_lt_rt2_8, one_lt_rt2_16,
      one_lt_rt2_32, sqrt_sqrt_two_lt_sqrt_two, sqrt_two_lt_two,
      sqrt_two_lt_sqrt_three, two_lt_one_add_sqrt_two,
      one_add_sqrt_two_lt_three]

theorem recursiveValueSet_nine :
    recursiveValueSet 9 = Set.range values9 := by
  ext x
  constructor
  · intro hx
    rw [recursiveValueSet] at hx
    rcases hx with h | h
    · rcases h with ⟨y, hy, rfl⟩
      rw [recursiveValueSet_eight] at hy
      rcases hy with ⟨i, rfl⟩
      fin_cases i
      · exact ⟨⟨0, by decide⟩, by norm_num [values8, values8List, values9, values9List]⟩
      · exact ⟨⟨1, by decide⟩, by simp [values8, values8List, values9, values9List, rt2_64]⟩
      · exact ⟨⟨2, by decide⟩, by simp [values8, values8List, values9, values9List, rt2_32]⟩
      · exact ⟨⟨3, by decide⟩, by simp [values8, values8List, values9, values9List, rt2_16]⟩
      · exact ⟨⟨4, by decide⟩, by simp [values8, values8List, values9, values9List, rt3_16]⟩
      · exact ⟨⟨5, by decide⟩, by simp [values8, values8List, values9, values9List, rt2_8]⟩
      · exact ⟨⟨6, by decide⟩, by
          simp [values8, values8List, values9, values9List,
            sqrt_sqrt_sqrt_one_add_sqrt_two]⟩
      · exact ⟨⟨7, by decide⟩, by simp [values8, values8List, values9, values9List, rt3_8]⟩
      · exact ⟨⟨8, by decide⟩, by simp [values8, values8List, values9, values9List, rt2_4]⟩
      · exact ⟨⟨9, by decide⟩, by
          simp [values8, values8List, values9, values9List, sqrt_sqrt_one_add_rt2_4]⟩
      · exact ⟨⟨10, by decide⟩, by
          simp [values8, values8List, values9, values9List,
            sqrt_sqrt_one_add_sqrt_two]⟩
      · exact ⟨⟨11, by decide⟩, by simp [values8, values8List, values9, values9List, rt3_4]⟩
      · exact ⟨⟨12, by decide⟩, by simp [values8, values8List, values9, values9List]⟩
      · exact ⟨⟨13, by decide⟩, by
          simp [values8, values8List, values9, values9List, sqrt_one_add_rt2_8]⟩
      · exact ⟨⟨14, by decide⟩, by
          simp [values8, values8List, values9, values9List, sqrt_one_add_rt2_4]⟩
      · exact ⟨⟨15, by decide⟩, by
          simp [values8, values8List, values9, values9List, sqrt_one_add_sqrt_two]⟩
      · exact ⟨⟨16, by decide⟩, by
          simp [values8, values8List, values9, values9List, sqrt_one_add_sqrt_three]⟩
      · exact ⟨⟨17, by decide⟩, by simp [values8, values8List, values9, values9List]⟩
      · exact ⟨⟨18, by decide⟩, by
          simp [values8, values8List, values9, values9List, sqrt_two_add_sqrt_two]⟩
      · exact ⟨⟨19, by decide⟩, by
          simp [values8, values8List, values9, values9List, sqrt_four]⟩
    · rcases h with ⟨k, a, ha, b, hb, rfl⟩
      fin_cases k
      · simp [recursiveValueSet] at ha
        have hb' : b ∈ recursiveValueSet 7 := by simpa using hb
        rw [recursiveValueSet_seven] at hb'
        rcases ha with rfl
        rcases hb' with ⟨i, rfl⟩
        fin_cases i
        · exact ⟨⟨19, by decide⟩, by norm_num [values7, values7List, values9, values9List]⟩
        · exact ⟨⟨20, by decide⟩, by simp [values7, values7List, values9, values9List]⟩
        · exact ⟨⟨21, by decide⟩, by simp [values7, values7List, values9, values9List]⟩
        · exact ⟨⟨22, by decide⟩, by simp [values7, values7List, values9, values9List]⟩
        · exact ⟨⟨23, by decide⟩, by simp [values7, values7List, values9, values9List]⟩
        · exact ⟨⟨24, by decide⟩, by simp [values7, values7List, values9, values9List]⟩
        · exact ⟨⟨25, by decide⟩, by simp [values7, values7List, values9, values9List]⟩
        · exact ⟨⟨26, by decide⟩, by simp [values7, values7List, values9, values9List]⟩
        · exact ⟨⟨28, by decide⟩, by norm_num [values7, values7List, values9, values9List]⟩
        · exact ⟨⟨29, by decide⟩, by
            simp [values7, values7List, values9, values9List]
            ring⟩
        · exact ⟨⟨30, by decide⟩, by
            simp [values7, values7List, values9, values9List]
            ring⟩
        · exact ⟨⟨31, by decide⟩, by norm_num [values7, values7List, values9, values9List]⟩
        · exact ⟨⟨32, by decide⟩, by norm_num [values7, values7List, values9, values9List]⟩
      · rw [recursiveValueSet_two] at ha
        have hb' : b ∈ recursiveValueSet 6 := by simpa using hb
        rw [recursiveValueSet_six] at hb'
        simp only [Set.mem_singleton_iff] at ha
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb'
        rcases ha with rfl
        rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨⟨19, by decide⟩, by norm_num [values9, values9List]⟩
        · exact ⟨⟨21, by decide⟩, by simp [values9, values9List]⟩
        · exact ⟨⟨22, by decide⟩, by simp [values9, values9List]⟩
        · exact ⟨⟨24, by decide⟩, by simp [values9, values9List]⟩
        · exact ⟨⟨26, by decide⟩, by simp [values9, values9List]⟩
        · exact ⟨⟨28, by decide⟩, by norm_num [values9, values9List]⟩
        · exact ⟨⟨30, by decide⟩, by
            simp [values9, values9List]
            ring⟩
        · exact ⟨⟨31, by decide⟩, by norm_num [values9, values9List]⟩
      · rw [recursiveValueSet_three] at ha
        have hb' : b ∈ recursiveValueSet 5 := by simpa using hb
        rw [recursiveValueSet_five] at hb'
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb'
        rcases ha with rfl | rfl
        · rcases hb' with rfl | rfl | rfl | rfl | rfl
          · exact ⟨⟨19, by decide⟩, by norm_num [values9, values9List]⟩
          · exact ⟨⟨22, by decide⟩, by simp [values9, values9List, rt2_4]⟩
          · exact ⟨⟨24, by decide⟩, by simp [values9, values9List]⟩
          · exact ⟨⟨28, by decide⟩, by norm_num [values9, values9List]⟩
          · exact ⟨⟨31, by decide⟩, by norm_num [values9, values9List]⟩
        · rcases hb' with rfl | rfl | rfl | rfl | rfl
          · exact ⟨⟨28, by decide⟩, by norm_num [values9, values9List]⟩
          · exact ⟨⟨29, by decide⟩, by simp [values9, values9List, rt2_4]⟩
          · exact ⟨⟨30, by decide⟩, by simp [values9, values9List]⟩
          · exact ⟨⟨31, by decide⟩, by norm_num [values9, values9List]⟩
          · exact ⟨⟨32, by decide⟩, by norm_num [values9, values9List]⟩
      · rw [recursiveValueSet_four] at ha
        have hb' : b ∈ recursiveValueSet 4 := by simpa using hb
        rw [recursiveValueSet_four] at hb'
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb'
        rcases ha with rfl | rfl | rfl
        · rcases hb' with rfl | rfl | rfl
          · exact ⟨⟨19, by decide⟩, by norm_num [values9, values9List]⟩
          · exact ⟨⟨24, by decide⟩, by simp [values9, values9List]⟩
          · exact ⟨⟨28, by decide⟩, by norm_num [values9, values9List]⟩
        · rcases hb' with rfl | rfl | rfl
          · exact ⟨⟨24, by decide⟩, by simp [values9, values9List, add_comm]⟩
          · exact ⟨⟨27, by decide⟩, by simp [values9, values9List, two_mul]⟩
          · exact ⟨⟨30, by decide⟩, by simp [values9, values9List, add_comm]⟩
        · rcases hb' with rfl | rfl | rfl
          · exact ⟨⟨28, by decide⟩, by norm_num [values9, values9List]⟩
          · exact ⟨⟨30, by decide⟩, by simp [values9, values9List]⟩
          · exact ⟨⟨31, by decide⟩, by norm_num [values9, values9List]⟩
      · rw [recursiveValueSet_five] at ha
        have hb' : b ∈ recursiveValueSet 3 := by simpa using hb
        rw [recursiveValueSet_three] at hb'
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb'
        rcases ha with rfl | rfl | rfl | rfl | rfl
        · rcases hb' with rfl | rfl
          · exact ⟨⟨19, by decide⟩, by norm_num [values9, values9List]⟩
          · exact ⟨⟨28, by decide⟩, by norm_num [values9, values9List]⟩
        · rcases hb' with rfl | rfl
          · exact ⟨⟨22, by decide⟩, by simp [values9, values9List, rt2_4, add_comm]⟩
          · exact ⟨⟨29, by decide⟩, by simp [values9, values9List, rt2_4, add_comm]⟩
        · rcases hb' with rfl | rfl
          · exact ⟨⟨24, by decide⟩, by simp [values9, values9List, add_comm]⟩
          · exact ⟨⟨30, by decide⟩, by simp [values9, values9List, add_comm]⟩
        · rcases hb' with rfl | rfl
          · exact ⟨⟨28, by decide⟩, by norm_num [values9, values9List]⟩
          · exact ⟨⟨31, by decide⟩, by norm_num [values9, values9List]⟩
        · rcases hb' with rfl | rfl
          · exact ⟨⟨31, by decide⟩, by norm_num [values9, values9List]⟩
          · exact ⟨⟨32, by decide⟩, by norm_num [values9, values9List]⟩
      · rw [recursiveValueSet_six] at ha
        have hb' : b ∈ recursiveValueSet 2 := by simpa using hb
        rw [recursiveValueSet_two] at hb'
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        simp only [Set.mem_singleton_iff] at hb'
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · rcases hb' with rfl
          exact ⟨⟨19, by decide⟩, by norm_num [values9, values9List]⟩
        · rcases hb' with rfl
          exact ⟨⟨21, by decide⟩, by simp [values9, values9List, add_comm]⟩
        · rcases hb' with rfl
          exact ⟨⟨22, by decide⟩, by simp [values9, values9List, add_comm]⟩
        · rcases hb' with rfl
          exact ⟨⟨24, by decide⟩, by simp [values9, values9List, add_comm]⟩
        · rcases hb' with rfl
          exact ⟨⟨26, by decide⟩, by simp [values9, values9List, add_comm]⟩
        · rcases hb' with rfl
          exact ⟨⟨28, by decide⟩, by norm_num [values9, values9List]⟩
        · rcases hb' with rfl
          exact ⟨⟨30, by decide⟩, by
            simp [values9, values9List]
            ring⟩
        · rcases hb' with rfl
          exact ⟨⟨31, by decide⟩, by norm_num [values9, values9List]⟩
      · rw [recursiveValueSet_seven] at ha
        simp [recursiveValueSet] at hb
        rcases ha with ⟨i, rfl⟩
        rcases hb with rfl
        fin_cases i
        · exact ⟨⟨19, by decide⟩, by norm_num [values7, values7List, values9, values9List]⟩
        · exact ⟨⟨20, by decide⟩, by simp [values7, values7List, values9, values9List, add_comm]⟩
        · exact ⟨⟨21, by decide⟩, by simp [values7, values7List, values9, values9List, add_comm]⟩
        · exact ⟨⟨22, by decide⟩, by simp [values7, values7List, values9, values9List, add_comm]⟩
        · exact ⟨⟨23, by decide⟩, by simp [values7, values7List, values9, values9List, add_comm]⟩
        · exact ⟨⟨24, by decide⟩, by simp [values7, values7List, values9, values9List, add_comm]⟩
        · exact ⟨⟨25, by decide⟩, by simp [values7, values7List, values9, values9List, add_comm]⟩
        · exact ⟨⟨26, by decide⟩, by simp [values7, values7List, values9, values9List, add_comm]⟩
        · exact ⟨⟨28, by decide⟩, by norm_num [values7, values7List, values9, values9List]⟩
        · exact ⟨⟨29, by decide⟩, by
            simp [values7, values7List, values9, values9List]
            ring⟩
        · exact ⟨⟨30, by decide⟩, by
            simp [values7, values7List, values9, values9List]
            ring⟩
        · exact ⟨⟨31, by decide⟩, by norm_num [values7, values7List, values9, values9List]⟩
        · exact ⟨⟨32, by decide⟩, by norm_num [values7, values7List, values9, values9List]⟩
  · rintro ⟨i, rfl⟩
    fin_cases i
    · change (1 : ℝ) ∈ recursiveValueSet 9
      rw [recursiveValueSet]
      left
      refine ⟨1, ?_, by norm_num⟩
      rw [recursiveValueSet_eight]
      exact ⟨⟨0, by decide⟩, by simp [values8, values8List]⟩
    · change rt2_64 ∈ recursiveValueSet 9
      rw [recursiveValueSet]
      left
      refine ⟨rt2_32, ?_, by simp [rt2_64]⟩
      rw [recursiveValueSet_eight]
      exact ⟨⟨1, by decide⟩, by simp [values8, values8List]⟩
    · change rt2_32 ∈ recursiveValueSet 9
      rw [recursiveValueSet]
      left
      refine ⟨rt2_16, ?_, by simp [rt2_32]⟩
      rw [recursiveValueSet_eight]
      exact ⟨⟨2, by decide⟩, by simp [values8, values8List]⟩
    · change rt2_16 ∈ recursiveValueSet 9
      rw [recursiveValueSet]
      left
      refine ⟨rt2_8, ?_, by simp [rt2_16]⟩
      rw [recursiveValueSet_eight]
      exact ⟨⟨3, by decide⟩, by simp [values8, values8List]⟩
    · change rt3_16 ∈ recursiveValueSet 9
      rw [recursiveValueSet]
      left
      refine ⟨rt3_8, ?_, by simp [rt3_16]⟩
      rw [recursiveValueSet_eight]
      exact ⟨⟨4, by decide⟩, by simp [values8, values8List]⟩
    · change rt2_8 ∈ recursiveValueSet 9
      rw [recursiveValueSet]
      left
      refine ⟨rt2_4, ?_, by simp [rt2_8]⟩
      rw [recursiveValueSet_eight]
      exact ⟨⟨5, by decide⟩, by simp [values8, values8List]⟩
    · change sqrt_sqrt_sqrt_one_add_sqrt_two ∈ recursiveValueSet 9
      rw [recursiveValueSet]
      left
      refine ⟨sqrt_sqrt_one_add_sqrt_two, ?_, by
        simp [sqrt_sqrt_sqrt_one_add_sqrt_two]⟩
      rw [recursiveValueSet_eight]
      exact ⟨⟨6, by decide⟩, by simp [values8, values8List]⟩
    · change rt3_8 ∈ recursiveValueSet 9
      rw [recursiveValueSet]
      left
      refine ⟨rt3_4, ?_, by simp [rt3_8]⟩
      rw [recursiveValueSet_eight]
      exact ⟨⟨7, by decide⟩, by simp [values8, values8List]⟩
    · change rt2_4 ∈ recursiveValueSet 9
      rw [recursiveValueSet]
      left
      refine ⟨Real.sqrt 2, ?_, by simp [rt2_4]⟩
      rw [recursiveValueSet_eight]
      exact ⟨⟨8, by decide⟩, by simp [values8, values8List]⟩
    · change sqrt_sqrt_one_add_rt2_4 ∈ recursiveValueSet 9
      rw [recursiveValueSet]
      left
      refine ⟨sqrt_one_add_rt2_4, ?_, by simp [sqrt_sqrt_one_add_rt2_4]⟩
      rw [recursiveValueSet_eight]
      exact ⟨⟨9, by decide⟩, by simp [values8, values8List]⟩
    · change sqrt_sqrt_one_add_sqrt_two ∈ recursiveValueSet 9
      rw [recursiveValueSet]
      left
      refine ⟨sqrt_one_add_sqrt_two, ?_, by simp [sqrt_sqrt_one_add_sqrt_two]⟩
      rw [recursiveValueSet_eight]
      exact ⟨⟨10, by decide⟩, by simp [values8, values8List]⟩
    · change rt3_4 ∈ recursiveValueSet 9
      rw [recursiveValueSet]
      left
      refine ⟨Real.sqrt 3, ?_, by simp [rt3_4]⟩
      rw [recursiveValueSet_eight]
      exact ⟨⟨11, by decide⟩, by simp [values8, values8List]⟩
    · change Real.sqrt 2 ∈ recursiveValueSet 9
      rw [recursiveValueSet]
      left
      refine ⟨2, ?_, by simp⟩
      rw [recursiveValueSet_eight]
      exact ⟨⟨12, by decide⟩, by simp [values8, values8List]⟩
    · change sqrt_one_add_rt2_8 ∈ recursiveValueSet 9
      rw [recursiveValueSet]
      left
      refine ⟨1 + rt2_8, ?_, by simp [sqrt_one_add_rt2_8]⟩
      rw [recursiveValueSet_eight]
      exact ⟨⟨13, by decide⟩, by simp [values8, values8List]⟩
    · change sqrt_one_add_rt2_4 ∈ recursiveValueSet 9
      rw [recursiveValueSet]
      left
      refine ⟨1 + rt2_4, ?_, by simp [sqrt_one_add_rt2_4]⟩
      rw [recursiveValueSet_eight]
      exact ⟨⟨14, by decide⟩, by simp [values8, values8List]⟩
    · change sqrt_one_add_sqrt_two ∈ recursiveValueSet 9
      rw [recursiveValueSet]
      left
      refine ⟨1 + Real.sqrt 2, ?_, by simp [sqrt_one_add_sqrt_two]⟩
      rw [recursiveValueSet_eight]
      exact ⟨⟨15, by decide⟩, by simp [values8, values8List]⟩
    · change sqrt_one_add_sqrt_three ∈ recursiveValueSet 9
      rw [recursiveValueSet]
      left
      refine ⟨1 + Real.sqrt 3, ?_, by simp [sqrt_one_add_sqrt_three]⟩
      rw [recursiveValueSet_eight]
      exact ⟨⟨16, by decide⟩, by simp [values8, values8List]⟩
    · change Real.sqrt 3 ∈ recursiveValueSet 9
      rw [recursiveValueSet]
      left
      refine ⟨3, ?_, by simp⟩
      rw [recursiveValueSet_eight]
      exact ⟨⟨17, by decide⟩, by simp [values8, values8List]⟩
    · change sqrt_two_add_sqrt_two ∈ recursiveValueSet 9
      rw [recursiveValueSet]
      left
      refine ⟨2 + Real.sqrt 2, ?_, by simp [sqrt_two_add_sqrt_two]⟩
      rw [recursiveValueSet_eight]
      exact ⟨⟨18, by decide⟩, by simp [values8, values8List]⟩
    · change (2 : ℝ) ∈ recursiveValueSet 9
      rw [recursiveValueSet]
      left
      refine ⟨4, ?_, by simp [sqrt_four]⟩
      rw [recursiveValueSet_eight]
      exact ⟨⟨19, by decide⟩, by simp [values8, values8List]⟩
    · change 1 + rt2_16 ∈ recursiveValueSet 9
      rw [recursiveValueSet]
      right
      refine ⟨⟨0, by decide⟩, 1, ?_, rt2_16, ?_, rfl⟩
      · simp [recursiveValueSet]
      · change rt2_16 ∈ recursiveValueSet 7
        rw [recursiveValueSet_seven]
        exact ⟨⟨1, by decide⟩, by simp [values7, values7List]⟩
    · change 1 + rt2_8 ∈ recursiveValueSet 9
      rw [recursiveValueSet]
      right
      refine ⟨⟨0, by decide⟩, 1, ?_, rt2_8, ?_, rfl⟩
      · simp [recursiveValueSet]
      · change rt2_8 ∈ recursiveValueSet 7
        rw [recursiveValueSet_seven]
        exact ⟨⟨2, by decide⟩, by simp [values7, values7List]⟩
    · change 1 + rt2_4 ∈ recursiveValueSet 9
      rw [recursiveValueSet]
      right
      refine ⟨⟨0, by decide⟩, 1, ?_, rt2_4, ?_, rfl⟩
      · simp [recursiveValueSet]
      · change rt2_4 ∈ recursiveValueSet 7
        rw [recursiveValueSet_seven]
        exact ⟨⟨3, by decide⟩, by simp [values7, values7List]⟩
    · change 1 + rt3_4 ∈ recursiveValueSet 9
      rw [recursiveValueSet]
      right
      refine ⟨⟨0, by decide⟩, 1, ?_, rt3_4, ?_, rfl⟩
      · simp [recursiveValueSet]
      · change rt3_4 ∈ recursiveValueSet 7
        rw [recursiveValueSet_seven]
        exact ⟨⟨4, by decide⟩, by simp [values7, values7List]⟩
    · change 1 + Real.sqrt 2 ∈ recursiveValueSet 9
      rw [recursiveValueSet]
      right
      refine ⟨⟨0, by decide⟩, 1, ?_, Real.sqrt 2, ?_, rfl⟩
      · simp [recursiveValueSet]
      · change Real.sqrt 2 ∈ recursiveValueSet 7
        rw [recursiveValueSet_seven]
        exact ⟨⟨5, by decide⟩, by simp [values7, values7List]⟩
    · change 1 + sqrt_one_add_sqrt_two ∈ recursiveValueSet 9
      rw [recursiveValueSet]
      right
      refine ⟨⟨0, by decide⟩, 1, ?_, sqrt_one_add_sqrt_two, ?_, rfl⟩
      · simp [recursiveValueSet]
      · change sqrt_one_add_sqrt_two ∈ recursiveValueSet 7
        rw [recursiveValueSet_seven]
        exact ⟨⟨6, by decide⟩, by simp [values7, values7List]⟩
    · change 1 + Real.sqrt 3 ∈ recursiveValueSet 9
      rw [recursiveValueSet]
      right
      refine ⟨⟨0, by decide⟩, 1, ?_, Real.sqrt 3, ?_, rfl⟩
      · simp [recursiveValueSet]
      · change Real.sqrt 3 ∈ recursiveValueSet 7
        rw [recursiveValueSet_seven]
        exact ⟨⟨7, by decide⟩, by simp [values7, values7List]⟩
    · change 2 * Real.sqrt 2 ∈ recursiveValueSet 9
      rw [recursiveValueSet]
      right
      refine ⟨⟨3, by decide⟩, Real.sqrt 2, ?_, Real.sqrt 2, ?_, by ring⟩
      · change Real.sqrt 2 ∈ recursiveValueSet 4
        rw [recursiveValueSet_four]
        simp
      · change Real.sqrt 2 ∈ recursiveValueSet 4
        rw [recursiveValueSet_four]
        simp
    · change (3 : ℝ) ∈ recursiveValueSet 9
      rw [recursiveValueSet]
      right
      refine ⟨⟨0, by decide⟩, 1, ?_, 2, ?_, by norm_num⟩
      · simp [recursiveValueSet]
      · change (2 : ℝ) ∈ recursiveValueSet 7
        rw [recursiveValueSet_seven]
        exact ⟨⟨8, by decide⟩, by simp [values7, values7List]⟩
    · change 2 + rt2_4 ∈ recursiveValueSet 9
      rw [recursiveValueSet]
      right
      refine ⟨⟨0, by decide⟩, 1, ?_, 1 + rt2_4, ?_, by ring⟩
      · simp [recursiveValueSet]
      · change 1 + rt2_4 ∈ recursiveValueSet 7
        rw [recursiveValueSet_seven]
        exact ⟨⟨9, by decide⟩, by simp [values7, values7List]⟩
    · change 2 + Real.sqrt 2 ∈ recursiveValueSet 9
      rw [recursiveValueSet]
      right
      refine ⟨⟨0, by decide⟩, 1, ?_, 1 + Real.sqrt 2, ?_, by ring⟩
      · simp [recursiveValueSet]
      · change 1 + Real.sqrt 2 ∈ recursiveValueSet 7
        rw [recursiveValueSet_seven]
        exact ⟨⟨10, by decide⟩, by simp [values7, values7List]⟩
    · change (4 : ℝ) ∈ recursiveValueSet 9
      rw [recursiveValueSet]
      right
      refine ⟨⟨0, by decide⟩, 1, ?_, 3, ?_, by norm_num⟩
      · simp [recursiveValueSet]
      · change (3 : ℝ) ∈ recursiveValueSet 7
        rw [recursiveValueSet_seven]
        exact ⟨⟨11, by decide⟩, by simp [values7, values7List]⟩
    · change (5 : ℝ) ∈ recursiveValueSet 9
      rw [recursiveValueSet]
      right
      refine ⟨⟨0, by decide⟩, 1, ?_, 4, ?_, by norm_num⟩
      · simp [recursiveValueSet]
      · change (4 : ℝ) ∈ recursiveValueSet 7
        rw [recursiveValueSet_seven]
        exact ⟨⟨12, by decide⟩, by simp [values7, values7List]⟩

theorem recursiveValueSet_nine_ncard :
    (recursiveValueSet 9).ncard = 33 := by
  rw [recursiveValueSet_nine]
  rw [Set.ncard_range_of_injective values9_strictMono.injective]
  norm_num

/-- OEIS A158415 has value `1` at `n = 1`. -/
theorem a158415_one : a158415 1 = 1 := by
  rw [a158415_eq_recursiveValueSet_ncard]
  simp [recursiveValueSet]

/-- OEIS A158415 has value `1` at `n = 2`. -/
theorem a158415_two : a158415 2 = 1 := by
  rw [a158415_eq_recursiveValueSet_ncard, recursiveValueSet_two]
  simp

/-- OEIS A158415 has value `2` at `n = 3`. -/
theorem a158415_three : a158415 3 = 2 := by
  rw [a158415_eq_recursiveValueSet_ncard, recursiveValueSet_three]
  exact Set.ncard_pair one_ne_two

/-- OEIS A158415 has value `3` at `n = 4`. -/
theorem a158415_four : a158415 4 = 3 := by
  rw [a158415_eq_recursiveValueSet_ncard]
  exact recursiveValueSet_four_ncard

/-- OEIS A158415 has value `5` at `n = 5`. -/
theorem a158415_five : a158415 5 = 5 := by
  rw [a158415_eq_recursiveValueSet_ncard]
  exact recursiveValueSet_five_ncard

/-- OEIS A158415 has value `8` at `n = 6`. -/
theorem a158415_six : a158415 6 = 8 := by
  rw [a158415_eq_recursiveValueSet_ncard]
  exact recursiveValueSet_six_ncard

/-- OEIS A158415 has value `13` at `n = 7`. -/
theorem a158415_seven : a158415 7 = 13 := by
  rw [a158415_eq_recursiveValueSet_ncard]
  exact recursiveValueSet_seven_ncard

/-- OEIS A158415 has value `20` at `n = 8`. -/
theorem a158415_eight : a158415 8 = 20 := by
  rw [a158415_eq_recursiveValueSet_ncard]
  exact recursiveValueSet_eight_ncard

/-- OEIS A158415 has value `33` at `n = 9`. -/
theorem a158415_nine : a158415 9 = 33 := by
  rw [a158415_eq_recursiveValueSet_ncard]
  exact recursiveValueSet_nine_ncard

end Expr

export Expr (a158415 a158415_eq_recursiveValueSet_ncard a158415_one a158415_two
  a158415_three a158415_four a158415_five a158415_six a158415_seven a158415_eight
  a158415_nine)

end A158415

end LeanProofs
