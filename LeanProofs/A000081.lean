import LeanProofs.PowTower
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Initial values of OEIS A000081 from exponent functions

OEIS A000081 counts the distinct functions of a positive real variable obtained
from all binary parenthesizations of `x^x^...^x`.  The primary definition in
this module is the shared lexical syntax from `PowTower.Expr`, interpreted as
functions `{x : ℝ // 0 < x} -> {x : ℝ // 0 < x}` by positive-real
exponentiation.

The first values are proved by enumerating the legal parenthesizations,
collapsing only identities proved over positive reals, and separating the
remaining functions by exact logarithmic/exponent tests.  The local `PowExpr`
syntax is retained as a compatibility view for those finite proofs.
-/

namespace LeanProofs

namespace A000081

set_option maxHeartbeats 1000000

/-- Positive real numbers as the domain and codomain of the exponent functions. -/
abbrev PosReal := {x : ℝ // 0 < x}

/-- Positive-real exponentiation, bundled with its positivity proof. -/
noncomputable def PosReal.rpow (x : PosReal) (y : ℝ) : PosReal :=
  ⟨x.1 ^ y, Real.rpow_pos_of_pos x.2 y⟩

/-- A000081's shared-lexical atom interpretation: the positive-real identity function. -/
noncomputable def atomFunction : PosReal -> PosReal :=
  fun t => t

/-- A000081's shared-lexical binary interpretation: pointwise positive-real exponentiation. -/
noncomputable def powFunction (f g : PosReal -> PosReal) : PosReal -> PosReal :=
  fun t => PosReal.rpow (f t) (g t).1

/-- Binary parenthesized expressions built from copies of the variable `x`. -/
inductive PowExpr where
  | x
  | pow (a b : PowExpr)
deriving Repr, DecidableEq

namespace PowExpr

open PowExpr

/-- Translate the existing A000081 syntax into the shared one-token lexical syntax. -/
def toSharedLex : PowExpr -> PowTower.Expr
  | x => PowTower.Expr.atom
  | pow a b => PowTower.Expr.pow (toSharedLex a) (toSharedLex b)

/-- Translate the shared one-token lexical syntax back to the existing A000081 syntax. -/
def ofSharedLex : PowTower.Expr -> PowExpr
  | .atom => x
  | .pow a b => pow (ofSharedLex a) (ofSharedLex b)

theorem toSharedLex_ofSharedLex (e : PowTower.Expr) :
    toSharedLex (ofSharedLex e) = e := by
  induction e with
  | atom => rfl
  | pow a b iha ihb =>
      simp [toSharedLex, ofSharedLex, iha, ihb]

theorem ofSharedLex_toSharedLex (e : PowExpr) :
    ofSharedLex (toSharedLex e) = e := by
  induction e with
  | x => rfl
  | pow a b iha ihb =>
      simp [toSharedLex, ofSharedLex, iha, ihb]

/-- Evaluate a parenthesized power expression as a function on positive reals. -/
noncomputable def eval : PowExpr -> PosReal -> PosReal
  | x, t => t
  | pow a b, t => PosReal.rpow (eval a t) (eval b t).1

/--
Shared lexical interpretation for A000081: the atom is the identity function
on positive reals, and the binary node exponentiates pointwise.
-/
noncomputable def sharedEval : PowTower.Expr -> PosReal -> PosReal :=
  PowTower.Expr.eval atomFunction powFunction

/-- The existing A000081 syntax evaluates the same way as the shared lexical syntax. -/
theorem eval_eq_sharedEval_toSharedLex (e : PowExpr) :
    eval e = sharedEval (toSharedLex e) := by
  induction e with
  | x =>
      rfl
  | pow a b iha ihb =>
      funext t
      simp [eval, sharedEval, toSharedLex, powFunction, iha, ihb]

/--
The shared canonical lexical value set for A000081.
-/
def canonicalValueSet (n : Nat) : Set (PosReal -> PosReal) :=
  PowTower.Expr.valueSet atomFunction powFunction n

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

/-- Translating a local parenthesization gives a shared lexical parenthesization. -/
theorem toSharedLex_mem_parenthesizations {n : Nat} {e : PowExpr}
    (he : e ∈ parenthesizations n) : toSharedLex e ∈ PowTower.Expr.parenthesizations n := by
  exact PowTower.Expr.toExpr_mem_parenthesizations
    parenthesizations x pow toSharedLex rfl rfl (fun _ => rfl) rfl (fun _ _ => rfl) he

/-- Translating a shared lexical parenthesization back gives a local parenthesization. -/
theorem ofSharedLex_mem_parenthesizations {n : Nat} {e : PowTower.Expr}
    (he : e ∈ PowTower.Expr.parenthesizations n) : ofSharedLex e ∈ parenthesizations n := by
  exact PowTower.Expr.ofExpr_mem_parenthesizations
    parenthesizations x pow ofSharedLex rfl rfl (fun _ => rfl) rfl (fun _ _ => rfl) he

/-- Compatibility value set computed through the old local variable syntax. -/
def valueSet (n : Nat) : Set (PosReal -> PosReal) :=
  {f | ∃ e ∈ parenthesizations n, eval e = f}

/-- The existing A000081 value set is the shared canonical lexical value set. -/
theorem valueSet_eq_canonicalValueSet (n : Nat) :
    valueSet n = canonicalValueSet n := by
  ext f
  constructor
  · rintro ⟨e, he, hf⟩
    refine ⟨toSharedLex e, ?_, ?_⟩
    · exact toSharedLex_mem_parenthesizations he
    · change sharedEval (toSharedLex e) = f
      rw [← eval_eq_sharedEval_toSharedLex, hf]
  · rintro ⟨e, he, hf⟩
    refine ⟨ofSharedLex e, ofSharedLex_mem_parenthesizations he, ?_⟩
    rw [eval_eq_sharedEval_toSharedLex, toSharedLex_ofSharedLex]
    exact hf

/-- OEIS A000081, defined as the cardinality of the shared lexical exponent-function set. -/
noncomputable def a000081 (n : Nat) : Nat :=
  PowTower.Expr.valueCard atomFunction powFunction n

/-- A000081 can equivalently be read from the shared canonical lexical syntax. -/
theorem a000081_eq_canonicalValueSet_ncard (n : Nat) :
    a000081 n = (canonicalValueSet n).ncard := by
  rfl

/-- The old local value-set presentation computes the shared canonical A000081 count. -/
theorem a000081_eq_valueSet_ncard (n : Nat) :
    a000081 n = (valueSet n).ncard := by
  rw [a000081_eq_canonicalValueSet_ncard, valueSet_eq_canonicalValueSet]

/--
A000081 also equals the cardinality of the split-recursive value set induced
by the same shared lexical interpretation.  This is a proved bridge from the
canonical lexical definition to the recursive value-set presentation; it is
not a replacement definition.
-/
theorem a000081_eq_recursiveValueSet_ncard (n : Nat) :
    a000081 n =
      (PowTower.Expr.recursiveValueSet atomFunction powFunction n).ncard := by
  exact PowTower.Expr.valueCard_eq_recursiveValueSet_ncard atomFunction powFunction n

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

def e5a : PowExpr :=
  pow x e4a

def e5b : PowExpr :=
  pow x e4b

def e5c : PowExpr :=
  pow x e4c

def e5d : PowExpr :=
  pow x e4d

def e5e : PowExpr :=
  pow x e4e

def e5f : PowExpr :=
  pow e2 e3a

def e5g : PowExpr :=
  pow e2 e3b

def e5h : PowExpr :=
  pow e3a e2

def e5i : PowExpr :=
  pow e3b e2

def e5j : PowExpr :=
  pow e4a x

def e5k : PowExpr :=
  pow e4b x

def e5l : PowExpr :=
  pow e4c x

def e5m : PowExpr :=
  pow e4d x

def e5n : PowExpr :=
  pow e4e x

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

theorem parenthesizations_five :
    parenthesizations 5 =
      [e5a, e5b, e5c, e5d, e5e, e5f, e5g, e5h, e5i, e5j, e5k, e5l, e5m, e5n] := by
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

/-- Equal outer exponents give equal positive-real exponent functions. -/
theorem eval_eq_of_exponent_eq {e₁ e₂ : PowExpr}
    (h : ∀ t : PosReal, exponent e₁ t = exponent e₂ t) : eval e₁ = eval e₂ := by
  funext t
  apply Subtype.ext
  rw [eval_eq_rpow_exponent e₁ t, eval_eq_rpow_exponent e₂ t, h t]

theorem valueSet_four :
    valueSet 4 =
      ({eval e4a, eval e4b, eval e4d, eval e4e} : Set (PosReal -> PosReal)) := by
  ext f
  rw [valueSet, parenthesizations_four]
  simp [e4c_eq_e4d, eq_comm]

theorem e5c_eq_e5d : eval e5c = eval e5d := by
  apply eval_eq_of_exponent_eq
  intro t
  have h := congrArg (fun f : PosReal -> PosReal => (f t).1) e4c_eq_e4d
  simpa [exponent, e5c, e5d] using h

theorem e5f_eq_e5j : eval e5f = eval e5j := by
  apply eval_eq_of_exponent_eq
  intro t
  simp [exponent, e5f, e5j, e4a, e3a, e2]
  ring

theorem e5g_eq_e5k : eval e5g = eval e5k := by
  apply eval_eq_of_exponent_eq
  intro t
  simp [exponent, e5g, e5k, e4b, e3b, e2]
  ring

theorem e5i_eq_e5l : eval e5i = eval e5l := by
  apply eval_eq_of_exponent_eq
  intro t
  simp [exponent, e5i, e5l, e4c, e3b, e2]
  ring

theorem e5i_eq_e5m : eval e5i = eval e5m := by
  apply eval_eq_of_exponent_eq
  intro t
  simp [exponent, e5i, e5m, e4d, e3b, e2]
  ring

theorem e5l_eq_e5m : eval e5l = eval e5m :=
  e5i_eq_e5l.symm.trans e5i_eq_e5m

theorem valueSet_five :
    valueSet 5 =
      ({eval e5a, eval e5b, eval e5d, eval e5e, eval e5j,
        eval e5k, eval e5h, eval e5m, eval e5n} : Set (PosReal -> PosReal)) := by
  ext f
  rw [valueSet, parenthesizations_five]
  simp [e5c_eq_e5d, e5f_eq_e5j, e5g_eq_e5k, e5i_eq_e5m, e5l_eq_e5m, eq_comm]
  tauto

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

/-- The `n = 5` representatives, ordered by their exponent at `x = 3`. -/
def repFive : Fin 9 -> PowExpr
  | ⟨0, _⟩ => e5n
  | ⟨1, _⟩ => e5m
  | ⟨2, _⟩ => e5h
  | ⟨3, _⟩ => e5k
  | ⟨4, _⟩ => e5e
  | ⟨5, _⟩ => e5j
  | ⟨6, _⟩ => e5d
  | ⟨7, _⟩ => e5b
  | ⟨8, _⟩ => e5a

/-- The semantic function represented by a chosen `n = 5` representative. -/
noncomputable def repFiveEval (i : Fin 9) : PosReal -> PosReal :=
  eval (repFive i)

theorem e5n_exponent_lt_e5m :
    exponent e5n three < exponent e5m three := by
  norm_num [exponent, eval, PosReal.rpow, three, e5n, e5m, e4e, e4d, e3b, e3a, e2]

theorem e5m_exponent_lt_e5h :
    exponent e5m three < exponent e5h three := by
  norm_num [exponent, eval, PosReal.rpow, three, e5m, e5h, e4d, e3b, e3a, e2]

theorem e5h_exponent_lt_e5k :
    exponent e5h three < exponent e5k three := by
  norm_num [exponent, eval, PosReal.rpow, three, e5h, e5k, e4b, e3b, e3a, e2]

theorem e5k_exponent_lt_e5e :
    exponent e5k three < exponent e5e three := by
  rw [show exponent e5k three = ((3 : ℝ) ^ (10 : ℝ)) by
    norm_num [exponent, eval, PosReal.rpow, three, e5k, e4b, e3b, e2]]
  rw [show exponent e5e three = ((3 : ℝ) ^ (27 : ℝ)) by
    norm_num [exponent, eval, PosReal.rpow, three, e5e, e4e, e3b, e2]]
  exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 3)
    (by norm_num : (10 : ℝ) < 27)

theorem e5e_exponent_lt_e5j :
    exponent e5e three < exponent e5j three := by
  rw [show exponent e5e three = ((3 : ℝ) ^ (27 : ℝ)) by
    norm_num [exponent, eval, PosReal.rpow, three, e5e, e4e, e3b, e2]]
  rw [show exponent e5j three = ((3 : ℝ) ^ (28 : ℝ)) by
    norm_num [exponent, eval, PosReal.rpow, three, e5j, e4a, e3a, e2]]
  exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 3)
    (by norm_num : (27 : ℝ) < 28)

theorem e5j_exponent_lt_e5d :
    exponent e5j three < exponent e5d three := by
  rw [show exponent e5j three = ((3 : ℝ) ^ (28 : ℝ)) by
    norm_num [exponent, eval, PosReal.rpow, three, e5j, e4a, e3a, e2]]
  rw [show exponent e5d three = ((3 : ℝ) ^ (81 : ℝ)) by
    norm_num [exponent, eval, PosReal.rpow, three, e5d, e4d, e3a, e2]]
  exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 3)
    (by norm_num : (28 : ℝ) < 81)

theorem e5d_exponent_lt_e5b :
    exponent e5d three < exponent e5b three := by
  rw [show exponent e5d three = ((3 : ℝ) ^ (81 : ℝ)) by
    norm_num [exponent, eval, PosReal.rpow, three, e5d, e4d, e3a, e2]]
  rw [show exponent e5b three = ((3 : ℝ) ^ (19683 : ℝ)) by
    norm_num [exponent, eval, PosReal.rpow, three, e5b, e4b, e3b, e2]]
  exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 3)
    (by norm_num : (81 : ℝ) < 19683)

theorem e5b_exponent_lt_e5a :
    exponent e5b three < exponent e5a three := by
  rw [show exponent e5b three = ((3 : ℝ) ^ (19683 : ℝ)) by
    norm_num [exponent, eval, PosReal.rpow, three, e5b, e4b, e3b, e2]]
  rw [show exponent e5a three = ((3 : ℝ) ^ (7625597484987 : ℝ)) by
    norm_num [exponent, eval, PosReal.rpow, three, e5a, e4a, e3a, e2]]
  exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 3)
    (by norm_num : (19683 : ℝ) < 7625597484987)

theorem repFiveEval_injective : Function.Injective repFiveEval := by
  intro i j h
  have hexp : exponent (repFive i) three = exponent (repFive j) three := by
    have hval := congrArg (fun f : PosReal -> PosReal => (f three).1) h
    dsimp [repFiveEval] at hval
    rw [eval_eq_rpow_exponent (repFive i) three,
      eval_eq_rpow_exponent (repFive j) three] at hval
    exact three_rpow_inj hval
  have h01 := e5n_exponent_lt_e5m
  have h12 := e5m_exponent_lt_e5h
  have h23 := e5h_exponent_lt_e5k
  have h34 := e5k_exponent_lt_e5e
  have h45 := e5e_exponent_lt_e5j
  have h56 := e5j_exponent_lt_e5d
  have h67 := e5d_exponent_lt_e5b
  have h78 := e5b_exponent_lt_e5a
  fin_cases i <;> fin_cases j <;> simp [repFive] at hexp ⊢
  all_goals first | rfl | nlinarith [h01, h12, h23, h34, h45, h56, h67, h78]

theorem repFiveEval_range :
    Set.range repFiveEval =
      ({eval e5a, eval e5b, eval e5d, eval e5e, eval e5j,
        eval e5k, eval e5h, eval e5m, eval e5n} : Set (PosReal -> PosReal)) := by
  ext f
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [repFiveEval, repFive]
  · intro hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨8, by simp [repFiveEval, repFive]⟩
    · exact ⟨7, by simp [repFiveEval, repFive]⟩
    · exact ⟨6, by simp [repFiveEval, repFive]⟩
    · exact ⟨4, by simp [repFiveEval, repFive]⟩
    · exact ⟨5, by simp [repFiveEval, repFive]⟩
    · exact ⟨3, by simp [repFiveEval, repFive]⟩
    · exact ⟨2, by simp [repFiveEval, repFive]⟩
    · exact ⟨1, by simp [repFiveEval, repFive]⟩
    · exact ⟨0, by simp [repFiveEval, repFive]⟩

theorem valueSet_five_ncard :
    ({eval e5a, eval e5b, eval e5d, eval e5e, eval e5j,
      eval e5k, eval e5h, eval e5m, eval e5n} : Set (PosReal -> PosReal)).ncard = 9 := by
  rw [← repFiveEval_range]
  rw [Set.ncard_range_of_injective repFiveEval_injective]
  simp

theorem valueSet_four_ncard :
    ({eval e4a, eval e4b, eval e4d, eval e4e} : Set (PosReal -> PosReal)).ncard = 4 := by
  rw [Set.ncard_insert_of_notMem]
  · rw [Set.ncard_insert_of_notMem]
    · rw [Set.ncard_pair e4d_ne_e4e]
    · simp [e4b_ne_e4d, e4b_ne_e4e]
  · simp [e4a_ne_e4b, e4a_ne_e4d, e4a_ne_e4e]

/-- `A000081(0) = 0`. -/
theorem a000081_zero : a000081 0 = 0 := by
  rw [a000081_eq_valueSet_ncard]
  simp [valueSet, parenthesizations]

/-- `A000081(1) = 1`. -/
theorem a000081_one : a000081 1 = 1 := by
  rw [a000081_eq_valueSet_ncard, valueSet_one, Set.ncard_singleton]

/-- `A000081(2) = 1`. -/
theorem a000081_two : a000081 2 = 1 := by
  rw [a000081_eq_valueSet_ncard, valueSet_two, Set.ncard_singleton]

/-- `A000081(3) = 2`. -/
theorem a000081_three : a000081 3 = 2 := by
  rw [a000081_eq_valueSet_ncard, valueSet_three, Set.ncard_pair e3a_ne_e3b]

/-- `A000081(4) = 4`. -/
theorem a000081_four : a000081 4 = 4 := by
  rw [a000081_eq_valueSet_ncard, valueSet_four, valueSet_four_ncard]

/-- `A000081(5) = 9`. -/
theorem a000081_five : a000081 5 = 9 := by
  rw [a000081_eq_valueSet_ncard, valueSet_five, valueSet_five_ncard]

end PowExpr

export PowExpr (a000081 a000081_eq_recursiveValueSet_ncard a000081_zero a000081_one
  a000081_two a000081_three a000081_four a000081_five)

end A000081

end LeanProofs
