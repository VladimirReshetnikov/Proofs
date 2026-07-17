import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.NumberTheory.Dioph

/-!
# Bounded universal quantification for Diophantine relations

This file develops the infrastructure needed to port the bounded-universal
elimination theorem used by the vendored Rocq development
`Undecidability.H10.Dio.dio_bounded`.  That theorem is the nontrivial bridge
from a Diophantine one-step relation to a Diophantine trace of
input-dependent length.

There are two superficially similar closure principles which it is important
not to confuse:

* a conjunction with a *fixed* externally known number of clauses is an
  elementary closure property of `Dioph`; and
* `forall i < b(v), R(i,v)`, where the bound is part of the input, is
  Matiyasevich's bounded-universal theorem and requires a finite-sequence
  cipher.

The first principle, finite support of polynomial witnesses, and the
elementary Goedel-beta lookup relation are proved below.  They are useful
independently and fix the indexing conventions for the variable-bound
construction.  The companion sparse-cipher layer follows the Rocq source's
invariant: finitely many witness columns are packed into arithmetic ciphers,
polynomial operations are simulated pointwise, and the resulting zero column
certifies every instance below the bound.
-/

namespace PAListCoding

open Function Fin2
open scoped Dioph
open scoped BigOperators

namespace BoundedDioph

universe u

/-! ## Environments with one distinguished coordinate

`Option.elim' i v` is Mathlib's standard convention for adjoining one
coordinate to a valuation: `none` contains the new value `i`, while `some a`
contains the old parameter `v a`.  This is the same convention used in the
definition of `DiophFn`.
-/

/-- Adjoin a distinguished natural-number coordinate to a valuation. -/
def consValue {alpha : Type u} (i : Nat) (v : alpha -> Nat) : Option alpha -> Nat :=
  Option.elim' i v

@[simp] theorem consValue_none {alpha : Type u} (i : Nat) (v : alpha -> Nat) :
    consValue i v none = i := rfl

@[simp] theorem consValue_some {alpha : Type u} (i : Nat) (v : alpha -> Nat)
    (a : alpha) : consValue i v (some a) = v a := rfl

/-- Mathlib's convenience theorem `Dioph.const_dioph` is accidentally
restricted to small (`Type 0`) index types.  The underlying polynomial proof
is universe-polymorphic, so we expose that version here. -/
theorem constFn_dioph {alpha : Type u} (n : Nat) :
    Dioph.DiophFn (Function.const (alpha -> Nat) n) := by
  change Dioph.DiophFn (fun _ : alpha -> Nat => n)
  simpa using (Dioph.abs_poly_dioph (Poly.const (α := alpha) (n : Int)))

/-- The variable-bound predicate whose closure under `Dioph` is the goal of
the Matiyasevich construction. -/
def BoundedForall {alpha : Type u} (bound : (alpha -> Nat) -> Nat)
    (R : Set (Option alpha -> Nat)) : Set (alpha -> Nat) :=
  {v | forall i, i < bound v -> consValue i v ∈ R}

/-! ## Fixed finite conjunctions

This is the easy finite analogue of bounded-universal elimination.  It is
still worth exposing explicitly: it provides a small regression theorem for
the environment convention above, and prevents an accidental use of
`Dioph.DiophList.forall` as though it handled an input-dependent list.
-/

/-- Substituting a fixed numeral for the distinguished coordinate preserves
Diophantineness. -/
theorem specializeIndex_dioph {alpha : Type u} {R : Set (Option alpha -> Nat)}
    (dR : Dioph R) (i : Nat) :
    Dioph {v : alpha -> Nat | consValue i v ∈ R} := by
  simpa [consValue] using
    (Dioph.diophFn_comp1 dR (constFn_dioph i))

/-- A conjunction over `0, ..., n-1` is Diophantine when `n` is fixed in the
metatheory.  This theorem does *not* eliminate a variable bound. -/
theorem fixedBoundedForall_dioph {alpha : Type u}
    {R : Set (Option alpha -> Nat)} (dR : Dioph R) (n : Nat) :
    Dioph {v : alpha -> Nat | forall i, i < n -> consValue i v ∈ R} := by
  let clauses : List (Set (alpha -> Nat)) :=
    (List.range n).map fun i => {v | consValue i v ∈ R}
  have hclauses : clauses.Forall Dioph := by
    apply List.forall_iff_forall_mem.mpr
    intro S hS
    rcases List.mem_map.mp hS with ⟨i, hi, rfl⟩
    exact specializeIndex_dioph dR i
  apply Dioph.ext (Dioph.DiophList.forall clauses hclauses)
  intro v
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h i hi
    apply List.forall_iff_forall_mem.mp h
    apply List.mem_map.mpr
    exact ⟨i, List.mem_range.mpr hi, rfl⟩
  · intro h
    apply List.forall_iff_forall_mem.mpr
    intro S hS
    rcases List.mem_map.mp hS with ⟨i, hi, rfl⟩
    exact h i (List.mem_range.mp hi)

/-! ## Finite support of Mathlib's polynomial functions

The cipher construction only needs one sequence for each variable actually
mentioned by a polynomial.  Although `Poly alpha` permits an arbitrary index
type, its `IsPoly` derivation is finite.  The following lemma makes that
finiteness available without changing Mathlib's polynomial representation.
-/

/-- Every `IsPoly` function depends on finitely many coordinates. -/
theorem IsPoly.exists_finset_support {alpha : Type u}
    {f : (alpha -> Nat) -> Int} (hf : IsPoly f) :
    exists s : Finset alpha, forall v w : alpha -> Nat,
      (forall a, a ∈ s -> v a = w a) -> f v = f w := by
  classical
  induction hf with
  | proj a =>
      refine ⟨{a}, ?_⟩
      intro v w h
      simpa using h a (by simp)
  | const z =>
      exact ⟨∅, fun _v _w _h => rfl⟩
  | sub _ _ hf hg =>
      rcases hf with ⟨sf, hsf⟩
      rcases hg with ⟨sg, hsg⟩
      refine ⟨sf ∪ sg, ?_⟩
      intro v w h
      apply congrArg₂ (fun x y : Int => x - y)
      · exact hsf v w (fun a ha => h a (Finset.mem_union_left sg ha))
      · exact hsg v w (fun a ha => h a (Finset.mem_union_right sf ha))
  | mul _ _ hf hg =>
      rcases hf with ⟨sf, hsf⟩
      rcases hg with ⟨sg, hsg⟩
      refine ⟨sf ∪ sg, ?_⟩
      intro v w h
      apply congrArg₂ (fun x y : Int => x * y)
      · exact hsf v w (fun a ha => h a (Finset.mem_union_left sg ha))
      · exact hsg v w (fun a ha => h a (Finset.mem_union_right sf ha))

/-- A bundled polynomial has a finite semantic support. -/
theorem Poly.exists_finset_support {alpha : Type u} (p : Poly alpha) :
    exists s : Finset alpha, forall v w : alpha -> Nat,
      (forall a, a ∈ s -> v a = w a) -> p v = p w :=
  IsPoly.exists_finset_support p.isPoly

/-! ## Goedel-beta entries are Diophantine

The construction is intentionally defined here rather than imported from the
independent `PAHF` project.  This keeps the list-coding library's dependency
graph acyclic and makes the exact arithmetic certificate visible.  Our
convention is

`BetaModulus step index = 1 + (index + 1) * step`.

An entry says both that `value` is the appropriate remainder and that it is
strictly below the modulus.  The latter conjunct is redundant for a computed
remainder, but indispensable when a formula treats `value` as an independent
variable.
-/

/-- The positive modulus used for position `index` in a Goedel-beta code. -/
def BetaModulus (step index : Nat) : Nat :=
  1 + (index + 1) * step

theorem BetaModulus_pos (step index : Nat) : 0 < BetaModulus step index := by
  simp [BetaModulus]

/-- Semantic lookup in a Goedel-beta code. -/
def BetaEntry (code step index value : Nat) : Prop :=
  code % BetaModulus step index = value ∧ value < BetaModulus step index

theorem BetaEntry_mod_eq {code step index value : Nat}
    (h : BetaEntry code step index value) :
    code % BetaModulus step index = value :=
  h.1

theorem BetaEntry_value_lt {code step index value : Nat}
    (h : BetaEntry code step index value) :
    value < BetaModulus step index :=
  h.2

theorem BetaEntry_of_mod_eq {code step index value : Nat}
    (hmod : code % BetaModulus step index = value) :
    BetaEntry code step index value := by
  refine ⟨hmod, ?_⟩
  rw [← hmod]
  exact Nat.mod_lt _ (BetaModulus_pos _ _)

/-- Beta lookup is functional at fixed code, step, and index. -/
theorem BetaEntry_functional {code step index x y : Nat}
    (hx : BetaEntry code step index x) (hy : BetaEntry code step index y) :
    x = y := by
  rw [← hx.1, ← hy.1]

/-- The beta modulus, viewed as a function on a valuation. -/
def betaModulusFn {alpha : Type}
    (step index : (alpha -> Nat) -> Nat) (v : alpha -> Nat) : Nat :=
  BetaModulus (step v) (index v)

/-- `BetaModulus` is built from constants, addition, and multiplication. -/
theorem betaModulusFn_dioph {alpha : Type}
    {step index : (alpha -> Nat) -> Nat}
    (dstep : Dioph.DiophFn step) (dindex : Dioph.DiophFn index) :
    Dioph.DiophFn (betaModulusFn step index) := by
  unfold betaModulusFn BetaModulus
  exact Dioph.add_dioph (constFn_dioph 1)
    (Dioph.mul_dioph (Dioph.add_dioph dindex (constFn_dioph 1)) dstep)

/-- A single Goedel-beta lookup is a Diophantine relation after substituting
arbitrary Diophantine functions for its four arguments. -/
theorem betaEntry_dioph {alpha : Type}
    {code step index value : (alpha -> Nat) -> Nat}
    (dcode : Dioph.DiophFn code) (dstep : Dioph.DiophFn step)
    (dindex : Dioph.DiophFn index) (dvalue : Dioph.DiophFn value) :
    Dioph {v : alpha -> Nat | BetaEntry (code v) (step v) (index v) (value v)} := by
  let modulus : (alpha -> Nat) -> Nat := betaModulusFn step index
  have dmodulus : Dioph.DiophFn modulus := betaModulusFn_dioph dstep dindex
  have drem : Dioph.DiophFn (fun v => code v % modulus v) :=
    Dioph.mod_dioph dcode dmodulus
  apply Dioph.ext
    (Dioph.inter (Dioph.eq_dioph drem dvalue) (Dioph.lt_dioph dvalue dmodulus))
  intro v
  simp [BetaEntry, modulus, betaModulusFn]

/-! ## Semantic beta certificates

The remaining lemmas establish that every finite sequence really has such a
code.  The common step is a multiple of a factorial: differences of indices
then divide the step, which makes the finitely many beta moduli pairwise
coprime.  Mathlib's finite Chinese remainder theorem supplies the code.
-/

/-- A local factorial used only to choose a sufficiently divisible step. -/
def betaFact : Nat -> Nat
  | 0 => 1
  | n + 1 => (n + 1) * betaFact n

theorem betaFact_pos : forall n, 0 < betaFact n
  | 0 => by simp [betaFact]
  | n + 1 => by simp [betaFact, betaFact_pos n]

/-- Every positive number at most `n` divides the local factorial. -/
theorem dvd_betaFact_of_pos_le {k n : Nat} (hk : 0 < k) (hkn : k ≤ n) :
    k ∣ betaFact n := by
  induction n with
  | zero => omega
  | succ n ih =>
      rcases Nat.lt_or_eq_of_le hkn with hlt | rfl
      · exact Nat.dvd_trans (ih (Nat.lt_succ_iff.mp hlt)) (by
          change betaFact n ∣ (n + 1) * betaFact n
          exact Nat.dvd_mul_left _ _)
      · change n + 1 ∣ (n + 1) * betaFact n
        exact Nat.dvd_mul_right _ _

/-- A beta modulus is coprime to the common step. -/
theorem BetaModulus_coprime_step (step index : Nat) :
    (BetaModulus step index).Coprime step := by
  apply (Nat.coprime_iff_gcd_eq_one).mpr
  let d := Nat.gcd (BetaModulus step index) step
  have hdm : d ∣ BetaModulus step index := Nat.gcd_dvd_left _ _
  have hds : d ∣ step := Nat.gcd_dvd_right _ _
  have hdp : d ∣ (index + 1) * step :=
    Nat.dvd_trans hds (Nat.dvd_mul_left _ _)
  have hd1 : d ∣ 1 := by
    have hsub := Nat.dvd_sub hdm hdp
    simpa [BetaModulus] using hsub
  exact Nat.dvd_one.mp hd1

theorem BetaModulus_sub {step i j : Nat} (hij : i ≤ j) :
    BetaModulus step j - BetaModulus step i = (j - i) * step := by
  have hj : j + 1 = (j - i) + (i + 1) := by omega
  simp [BetaModulus, hj, Nat.add_mul]
  omega

/-- Distinct beta moduli are coprime whenever the index difference divides
the common step.  This is the arithmetic invariant behind beta coding. -/
theorem BetaModulus_pair_coprime_of_dvd_step {step i j : Nat}
    (hij : i < j) (hdiff : j - i ∣ step) :
    (BetaModulus step i).Coprime (BetaModulus step j) := by
  apply (Nat.coprime_iff_gcd_eq_one).mpr
  let d := Nat.gcd (BetaModulus step i) (BetaModulus step j)
  have hdi : d ∣ BetaModulus step i := Nat.gcd_dvd_left _ _
  have hdj : d ∣ BetaModulus step j := Nat.gcd_dvd_right _ _
  have hcopStep : d.Coprime step :=
    Nat.Coprime.coprime_dvd_left hdi (BetaModulus_coprime_step step i)
  have hddiffStep : d ∣ (j - i) * step := by
    have hsub := Nat.dvd_sub hdj hdi
    simpa [d, BetaModulus_sub (Nat.le_of_lt hij)] using hsub
  have hddiff : d ∣ j - i := by
    apply hcopStep.dvd_of_dvd_mul_left
    simpa [Nat.mul_comm] using hddiffStep
  have hdstep : d ∣ step := Nat.dvd_trans hddiff hdiff
  exact hcopStep.eq_one_of_dvd hdstep

theorem BetaModulus_pair_coprime_mul_betaFact {i j n scale : Nat}
    (hij : i < j) (hj : j < n) :
    (BetaModulus (betaFact n * scale) i).Coprime
      (BetaModulus (betaFact n * scale) j) := by
  apply BetaModulus_pair_coprime_of_dvd_step hij
  have hfactorial : j - i ∣ betaFact n := by
    apply dvd_betaFact_of_pos_le
    · omega
    · omega
  exact Nat.dvd_trans hfactorial (Nat.dvd_mul_right _ _)

/-- Every finite prefix of a natural-number sequence has a common beta code
and step.  The proof is constructive up to Mathlib's constructive finite CRT. -/
theorem exists_beta_prefix (values : Nat -> Nat) (n : Nat) :
    exists code step, forall i, i < n -> BetaEntry code step i (values i) := by
  let scale := 1 + ∑ i ∈ Finset.range n, values i
  let step := betaFact n * scale
  have hscale : forall i, i < n -> values i < scale := by
    intro i hi
    have hle : values i ≤ ∑ j ∈ Finset.range n, values j := by
      exact Finset.single_le_sum (fun j _hj => Nat.zero_le (values j))
        (Finset.mem_range.mpr hi)
    simp only [scale]
    omega
  have hfact : 1 ≤ betaFact n := by
    exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (betaFact_pos n))
  have hstep : scale ≤ step := by
    simp only [step]
    simpa [Nat.one_mul] using Nat.mul_le_mul_right scale hfact
  have hsmall : forall i, i < n -> values i < BetaModulus step i := by
    intro i hi
    have hi1 : 1 ≤ i + 1 := by omega
    have hmul : step ≤ (i + 1) * step := by
      simpa [Nat.one_mul] using Nat.mul_le_mul_right step hi1
    have := hscale i hi
    simp only [BetaModulus]
    omega
  have hnonzero : forall i, i ∈ Finset.range n -> BetaModulus step i ≠ 0 := by
    intro i _hi
    exact Nat.ne_of_gt (BetaModulus_pos step i)
  have hpair : Set.Pairwise (↑(Finset.range n) : Set Nat)
      (Function.onFun Nat.Coprime (BetaModulus step)) := by
    intro i hi j hj hij
    have hi' : i < n := Finset.mem_range.mp hi
    have hj' : j < n := Finset.mem_range.mp hj
    rcases lt_or_gt_of_ne hij with hij' | hji'
    · simpa [step] using
        BetaModulus_pair_coprime_mul_betaFact (n := n) (scale := scale) hij' hj'
    · exact (by
        simpa [step, Nat.coprime_comm] using
          BetaModulus_pair_coprime_mul_betaFact
            (n := n) (scale := scale) hji' hi')
  let code := Nat.chineseRemainderOfFinset values (BetaModulus step)
    (Finset.range n) hnonzero hpair
  refine ⟨code, step, ?_⟩
  intro i hi
  apply BetaEntry_of_mod_eq
  have hc := code.property i (Finset.mem_range.mpr hi)
  simpa [Nat.ModEq, Nat.mod_eq_of_lt (hsmall i hi)] using hc

end BoundedDioph

end PAListCoding
