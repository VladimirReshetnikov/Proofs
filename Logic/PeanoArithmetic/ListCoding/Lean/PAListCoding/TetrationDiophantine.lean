import PAListCoding.ExponentiationDiophantine

/-!
# Natural-number tetration is Diophantine

This file uses the height convention

```
tetration a 0       = 1
tetration a (h + 1) = a ^ tetration a h.
```

The final Diophantine certificate is necessarily more than a fixed
composition of Mathlib's `Dioph.pow_dioph`: the height is an input, so the
certificate must describe a finite trace of input-dependent length.  The
semantic layer below isolates that trace argument from its arithmetic coding.

As in the independent Rocq proof, a trace state carries both the fixed base
and the current value.  The polynomial code

```
(a, x) ↦ (a + x)² + x
```

is injective.  Thus iterating the parameter-free relation
`(a,x) ↦ (a,a^x)` cannot silently change the base between two steps.
-/

namespace PAListCoding

open Fin2
open scoped Dioph

/-! ## Tetration and its exact-step semantics -/

/-- The right-associated natural power tower of base `a` and height `h`.
Height zero is the empty tower and therefore has value one. -/
def tetration (a : ℕ) : ℕ → ℕ
  | 0 => 1
  | h + 1 => a ^ tetration a h

@[simp] theorem tetration_zero (a : ℕ) : tetration a 0 = 1 := rfl

@[simp] theorem tetration_succ (a h : ℕ) :
    tetration a (h + 1) = a ^ tetration a h := rfl

/-- Exact iteration of a binary relation.  The successor clause exposes the
last transition; this orientation makes induction on a completed trace
especially convenient. -/
def ExactIter (R : ℕ → ℕ → Prop) : ℕ → ℕ → ℕ → Prop
  | 0, x, y => x = y
  | h + 1, x, z => ∃ y, ExactIter R h x y ∧ R y z

@[simp] theorem exactIter_zero (R : ℕ → ℕ → Prop) (x y : ℕ) :
    ExactIter R 0 x y ↔ x = y := Iff.rfl

@[simp] theorem exactIter_succ (R : ℕ → ℕ → Prop) (h x z : ℕ) :
    ExactIter R (h + 1) x z ↔ ∃ y, ExactIter R h x y ∧ R y z := Iff.rfl

/-! ## A polynomial code for base/value states -/

/-- An injective polynomial encoding of a trace state `(base, value)`. -/
def tetrationStateCode (a x : ℕ) : ℕ :=
  (a + x) * (a + x) + x

/-- The intervals occupied by two different values of `a+x` are disjoint:
the states with sum `s` have codes from `s²` through `s²+s`, strictly below
the first code `(s+1)²` with the next sum. -/
theorem tetrationStateCode_injective {a x b y : ℕ}
    (hcode : tetrationStateCode a x = tetrationStateCode b y) :
    a = b ∧ x = y := by
  let s := a + x
  let t := b + y
  have hx : x ≤ s := by simp [s]
  have hy : y ≤ t := by simp [t]
  by_cases hst : s = t
  · have hxy : x = y := by
      have hsquare : s * s = t * t := congrArg (fun n => n * n) hst
      have hcode' : s * s + x = t * t + y := by
        simpa [s, t, tetrationStateCode] using hcode
      omega
    exact ⟨by omega, hxy⟩
  · rcases lt_or_gt_of_ne hst with hlt | hgt
    · have hstrict : s * s + x < t * t + y := by
        nlinarith
      exact False.elim <| hstrict.ne hcode
    · have hstrict : t * t + y < s * s + x := by
        nlinarith
      exact False.elim <| hstrict.ne hcode.symm

/-- One parameter-free tower transition on encoded states. -/
def TetrationStep (source target : ℕ) : Prop :=
  ∃ a x,
    source = tetrationStateCode a x ∧
    target = tetrationStateCode a (a ^ x)

theorem tetrationStep_from_code (a x target : ℕ) :
    TetrationStep (tetrationStateCode a x) target ↔
      target = tetrationStateCode a (a ^ x) := by
  constructor
  · rintro ⟨b, y, hsource, htarget⟩
    obtain ⟨rfl, rfl⟩ := tetrationStateCode_injective hsource.symm
    exact htarget
  · intro htarget
    exact ⟨a, x, rfl, htarget⟩

/-- After exactly `h` encoded transitions from `(a,1)`, the unique endpoint
is `(a,tetration a h)`. -/
theorem exactIter_tetrationStep (a h endpoint : ℕ) :
    ExactIter TetrationStep h (tetrationStateCode a 1) endpoint ↔
      endpoint = tetrationStateCode a (tetration a h) := by
  induction h generalizing endpoint with
  | zero =>
      change tetrationStateCode a 1 = endpoint ↔
        endpoint = tetrationStateCode a 1
      exact eq_comm
  | succ h ih =>
      rw [exactIter_succ]
      constructor
      · rintro ⟨middle, hprefix, hlast⟩
        rw [ih] at hprefix
        subst middle
        simpa using (tetrationStep_from_code a (tetration a h) endpoint).mp hlast
      · intro hendpoint
        refine ⟨tetrationStateCode a (tetration a h), ?_, ?_⟩
        · exact (ih _).mpr rfl
        · exact (tetrationStep_from_code a (tetration a h) endpoint).mpr <| by
            simpa using hendpoint

/-- The recursive function and its finite encoded trace have exactly the same
result-first graph. -/
theorem tetration_eq_iff_exactIter (result base height : ℕ) :
    result = tetration base height ↔
      ExactIter TetrationStep height
        (tetrationStateCode base 1)
        (tetrationStateCode base result) := by
  rw [exactIter_tetrationStep]
  constructor
  · exact fun h => congrArg (tetrationStateCode base) h
  · intro hcode
    exact (tetrationStateCode_injective hcode).2

/-! ## Public graph -/

/-- The binary tetration function, with base followed by height. -/
def NaturalTetrationFunction (v : Vector3 ℕ 2) : ℕ :=
  tetration (v &0) (v &1)

/-- Result-first graph: `(m,a,h)` belongs exactly when `m = tetration a h`. -/
def NaturalTetrationGraph : Set (Vector3 ℕ 3) :=
  {v | v &0 = tetration (v &1) (v &2)}

end PAListCoding
