import PAListCoding.BoundedDioph
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

/-- Extensional semantics for exact iteration: a run of length `h` is a
function containing its `h+1` states and satisfying every adjacent step. -/
theorem exactIter_iff_exists_sequence (R : ℕ → ℕ → Prop) (h x y : ℕ) :
    ExactIter R h x y ↔
      ∃ f : ℕ → ℕ,
        f 0 = x ∧ f h = y ∧ ∀ i, i < h → R (f i) (f (i + 1)) := by
  induction h generalizing x y with
  | zero =>
      constructor
      · intro hxy
        exact ⟨fun _ => x, rfl, hxy, by omega⟩
      · rintro ⟨f, hf0, hfy, _hstep⟩
        exact hf0.symm.trans hfy
  | succ h ih =>
      rw [exactIter_succ]
      constructor
      · rintro ⟨middle, hprefix, hlast⟩
        obtain ⟨f, hf0, hfh, hfstep⟩ := (ih x middle).mp hprefix
        let g : ℕ → ℕ := fun i => if i = h + 1 then y else f i
        refine ⟨g, ?_, ?_, ?_⟩
        · simp [g, hf0]
        · simp [g]
        · intro i hi
          have hile : i ≤ h := by omega
          rcases Nat.lt_or_eq_of_le hile with hil | rfl
          · have hi_ne : i ≠ h + 1 := by omega
            have his_ne : i + 1 ≠ h + 1 := by omega
            have hi_h : i ≠ h := Nat.ne_of_lt hil
            simpa [g, hi_ne, his_ne, hi_h] using hfstep i hil
          · simpa [g, hfh] using hlast
      · rintro ⟨f, hf0, hfend, hfstep⟩
        refine ⟨f h, ?_, ?_⟩
        · apply (ih x (f h)).mpr
          exact ⟨f, hf0, rfl, fun i hi => hfstep i (by omega)⟩
        · simpa [hfend] using hfstep h (Nat.lt_succ_self h)

/-! ## Arithmetic coding of finite traces

`BoundedDioph.BetaEntry` uses Goedel's beta moduli.  Unlike a dependent
vector, the pair `(code,step)` is a fixed finite tuple of natural numbers and
can therefore become part of one Diophantine certificate.  The bound still
occurs in the universal adjacency clause; eliminating precisely that clause
is the substantive bounded-universal theorem developed in `BoundedDioph`.
-/

/-- A beta-coded exact trace for a binary relation. -/
def BetaTrace (R : ℕ → ℕ → Prop)
    (code step height start finish : ℕ) : Prop :=
  BoundedDioph.BetaEntry code step 0 start ∧
  BoundedDioph.BetaEntry code step height finish ∧
  ∀ i, i < height →
    ∃ current next,
      BoundedDioph.BetaEntry code step i current ∧
      BoundedDioph.BetaEntry code step (i + 1) next ∧
      R current next

/-- Goedel-beta codes are semantically complete for finite exact traces.  The
forward direction applies finite CRT to the sequence supplied above; the
reverse direction decodes each position by remainder and uses lookup
functionality to recover every transition. -/
theorem exactIter_iff_exists_betaTrace (R : ℕ → ℕ → Prop) (height start finish : ℕ) :
    ExactIter R height start finish ↔
      ∃ code step, BetaTrace R code step height start finish := by
  constructor
  · intro hiter
    obtain ⟨f, hf0, hfh, hfstep⟩ :=
      (exactIter_iff_exists_sequence R height start finish).mp hiter
    obtain ⟨code, step, hentry⟩ :=
      BoundedDioph.exists_beta_prefix f (height + 1)
    refine ⟨code, step, ?_, ?_, ?_⟩
    · simpa [hf0] using hentry 0 (by omega)
    · simpa [hfh] using hentry height (by omega)
    · intro i hi
      exact ⟨f i, f (i + 1), hentry i (by omega),
        hentry (i + 1) (by omega), hfstep i hi⟩
  · rintro ⟨code, step, hstart, hfinish, hsteps⟩
    apply (exactIter_iff_exists_sequence R height start finish).mpr
    let f : ℕ → ℕ := fun i => code % BoundedDioph.BetaModulus step i
    refine ⟨f, ?_, ?_, ?_⟩
    · simpa [f] using hstart.1
    · simpa [f] using hfinish.1
    · intro i hi
      obtain ⟨current, next, hcurrent, hnext, hrel⟩ := hsteps i hi
      have hc : f i = current := by simpa [f] using hcurrent.1
      have hn : f (i + 1) = next := by simpa [f] using hnext.1
      simpa [hc, hn] using hrel

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

/-- Substituting Diophantine functions for the two arguments of the state
code again gives a Diophantine function. -/
theorem tetrationStateCode_diophFn {α : Type}
    {a x : (α → ℕ) → ℕ}
    (da : Dioph.DiophFn a) (dx : Dioph.DiophFn x) :
    Dioph.DiophFn fun v => tetrationStateCode (a v) (x v) := by
  have dsum : Dioph.DiophFn fun v => a v + x v :=
    Dioph.add_dioph da dx
  simpa [tetrationStateCode] using
    Dioph.add_dioph (Dioph.mul_dioph dsum dsum) dx

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

/-- A single encoded tower step is Diophantine.  This uses Matiyasevich's
exponentiation theorem only once; all surrounding state-code operations are
polynomial. -/
theorem tetrationStep_diophantine :
    Dioph {v : Vector3 ℕ 2 | TetrationStep (v &0) (v &1)} := by
  have da : Dioph.DiophFn (fun v : Vector3 ℕ 4 => v &0) := D&0
  have dx : Dioph.DiophFn (fun v : Vector3 ℕ 4 => v &1) := D&1
  have dpow : Dioph.DiophFn (fun v : Vector3 ℕ 4 => v &0 ^ v &1) :=
    Dioph.pow_dioph da dx
  have dsource : Dioph.DiophFn
      (fun v : Vector3 ℕ 4 => tetrationStateCode (v &0) (v &1)) :=
    tetrationStateCode_diophFn da dx
  have dtarget : Dioph.DiophFn
      (fun v : Vector3 ℕ 4 => tetrationStateCode (v &0) (v &0 ^ v &1)) :=
    tetrationStateCode_diophFn da dpow
  have hfour : Dioph {v : Vector3 ℕ 4 |
      v &2 = tetrationStateCode (v &0) (v &1) ∧
      v &3 = tetrationStateCode (v &0) (v &0 ^ v &1)} :=
    Dioph.inter
      (Dioph.eq_dioph (Dioph.proj_dioph (&2 : Fin2 4)) dsource)
      (Dioph.eq_dioph (Dioph.proj_dioph (&3 : Fin2 4)) dtarget)
  apply Dioph.ext ((D∃) 2 <| (D∃) 3 hfour)
  intro v
  change
    (∃ x a,
      v &0 = tetrationStateCode a x ∧
      v &1 = tetrationStateCode a (a ^ x)) ↔
    TetrationStep (v &0) (v &1)
  constructor
  · rintro ⟨x, a, hsource, htarget⟩
    exact ⟨a, x, hsource, htarget⟩
  · rintro ⟨a, x, hsource, htarget⟩
    exact ⟨x, a, hsource, htarget⟩

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
