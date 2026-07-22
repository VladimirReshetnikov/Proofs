import PAListCoding.Aggregates
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.NumberTheory.Divisors

/-!
# Number-theoretic data represented by PA list codes

The relations in the first half of this file are stated uniformly in an
arbitrary model of `IΣ₁`.  In particular, none of the PA formula witnesses is
obtained by importing a Lean computation as an oracle.  Powers, products of
prime powers, and base expansions are certified by coded running traces.

The standard-model results in the second half identify those internal
relations with the usual Lean notions.  Prime indices are **one-based**:
`NthPrime 2 1` holds and no prime has index zero.
-/

namespace PAListCoding

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.HierarchySymbol

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Relations interpreted in every model of arithmetic -/

/-- `c` is the code of the two-entry list `[a, b]`. -/
def PairCode (c a b : V) : Prop :=
  Seq c ∧ lh c = 2 ∧ znth c 0 = a ∧ znth c 1 = b

/-- A valid coded list whose entries are strictly increasing. -/
def StrictlyIncreasing (v : V) : Prop :=
  Seq v ∧ ∀ i < lh v, ∀ j < lh v, i < j → znth v i < znth v j

/--
`m = n ^ k`, witnessed by the trace `1, n, n*n, ...` of length `k+1`.
The trace formulation is important because exponentiation is not a primitive
symbol of the language of PA.
-/
def Pow (m n k : V) : Prop :=
  ∃ trace, Seq trace ∧ lh trace = k + 1 ∧ znth trace 0 = 1 ∧
    (∀ i < k, znth trace (i + 1) = znth trace i * n) ∧
    znth trace k = m

/--
`p` is the `n`th prime using the one-based convention.  The witness lists all
and only primes below `p`, in strict order; consequently its length plus one
is the requested index.
-/
def NthPrime (p n : V) : Prop :=
  IsPrime p ∧ ∃ below,
    StrictlyIncreasing below ∧ n = lh below + 1 ∧
      (∀ i < lh below, IsPrime (znth below i) ∧ znth below i < p) ∧
      ∀ q < p, IsPrime q → ∃ i < lh below, znth below i = q

/--
`f` is the canonical prime factorization of nonzero `m`.  Every entry of `f`
is itself a PA-list code `[prime, positiveExponent]`; primes increase strictly,
and the second witness trace multiplies the corresponding prime powers.
-/
def PrimeFactorization (f m : V) : Prop :=
  m ≠ 0 ∧ Seq f ∧
    (∀ i < lh f, ∃ p e, PairCode (znth f i) p e ∧ IsPrime p ∧ 0 < e) ∧
    (∀ i < lh f, ∀ j < lh f, i < j →
      znth (znth f i) 0 < znth (znth f j) 0) ∧
    ∃ trace, Seq trace ∧ lh trace = lh f + 1 ∧ znth trace 0 = 1 ∧
      (∀ i < lh f, ∃ p e pe,
        PairCode (znth f i) p e ∧ Pow pe p e ∧
          znth trace (i + 1) = znth trace i * pe) ∧
      znth trace (lh f) = m

/--
`v` is the canonical most-significant-digit-first base-`b` representation of
`m`.  Zero is represented by `[0]`; positive values have a nonzero first
digit.  The Horner trace evaluates the list without using exponentiation.
-/
def BaseDigits (v m b : V) : Prop :=
  Seq v ∧ 2 ≤ b ∧ 0 < lh v ∧
    (∀ i < lh v, znth v i < b) ∧
    ((m = 0 ∧ lh v = 1 ∧ znth v 0 = 0) ∨
      (0 < m ∧ znth v 0 ≠ 0)) ∧
    ∃ trace, Seq trace ∧ lh trace = lh v + 1 ∧ znth trace 0 = 0 ∧
      (∀ i < lh v,
        znth trace (i + 1) = znth trace i * b + znth v i) ∧
      znth trace (lh v) = m

/--
`v` is the strictly increasing list of exactly the positive divisors of the
nonzero number `m`.  The bound `d < m+1` makes completeness bounded while
still ranging over every positive divisor.
-/
def DivisorList (v m : V) : Prop :=
  m ≠ 0 ∧ StrictlyIncreasing v ∧
    (∀ i < lh v, 0 < znth v i ∧ znth v i ∣ m) ∧
    ∀ d < m + 1, 0 < d → d ∣ m → ∃ i < lh v, znth v i = d

/-- Public spelling matching the mathematical statement of exponentiation. -/
abbrev Power (m n k : V) : Prop := Pow m n k

/-- Public spelling emphasizing that zero is deliberately not included. -/
abbrev PositiveDivisors (v m : V) : Prop := DivisorList v m

/-! ### Definability and concrete formula witnesses -/

@[simp, definability] instance pairCode_definable :
    𝚺-[2]-Relation₃ (PairCode : V → V → V → Prop) := by definability

@[simp, definability] instance strictlyIncreasing_definable :
    𝚺-[2]-Predicate (StrictlyIncreasing : V → Prop) := by definability

@[simp, definability] instance pow_definable :
    𝚺-[2]-Relation₃ (Pow : V → V → V → Prop) := by definability

@[simp, definability] instance nthPrime_definable :
    𝚺-[2]-Relation (NthPrime : V → V → Prop) := by definability

@[simp, definability] instance primeFactorization_definable :
    𝚺-[2]-Relation (PrimeFactorization : V → V → Prop) := by definability

@[simp, definability] instance baseDigits_definable :
    𝚺-[2]-Relation₃ (BaseDigits : V → V → V → Prop) := by definability

@[simp, definability] instance divisorList_definable :
    𝚺-[2]-Relation (DivisorList : V → V → Prop) := by definability

noncomputable def pairCodeFormula : PAFormula 3 :=
  formulaOf (pairCode_definable (V := ℕ))

@[simp] theorem pairCodeFormula_spec (c a b : ℕ) :
    pairCodeFormula.Eval ![c, a, b] id ↔ PairCode c a b :=
  formulaOf_spec (pairCode_definable (V := ℕ)) ![c, a, b]

noncomputable def strictlyIncreasingFormula : PAFormula 1 :=
  formulaOf (strictlyIncreasing_definable (V := ℕ))

@[simp] theorem strictlyIncreasingFormula_spec (v : ℕ) :
    strictlyIncreasingFormula.Eval ![v] id ↔ StrictlyIncreasing v :=
  formulaOf_spec (strictlyIncreasing_definable (V := ℕ)) ![v]

noncomputable def powFormula : PAFormula 3 := formulaOf (pow_definable (V := ℕ))

@[simp] theorem powFormula_spec (m n k : ℕ) :
    powFormula.Eval ![m, n, k] id ↔ Pow m n k :=
  formulaOf_spec (pow_definable (V := ℕ)) ![m, n, k]

/-- Compatibility name for the concrete PA formula defining `Power`. -/
noncomputable abbrev powerFormula : PAFormula 3 := powFormula

@[simp] theorem powerFormula_spec (m n k : ℕ) :
    powerFormula.Eval ![m, n, k] id ↔ Power m n k :=
  powFormula_spec m n k

noncomputable def nthPrimeFormula : PAFormula 2 :=
  formulaOf (nthPrime_definable (V := ℕ))

@[simp] theorem nthPrimeFormula_spec (p n : ℕ) :
    nthPrimeFormula.Eval ![p, n] id ↔ NthPrime p n :=
  formulaOf_spec (nthPrime_definable (V := ℕ)) ![p, n]

noncomputable def primeFactorizationFormula : PAFormula 2 :=
  formulaOf (primeFactorization_definable (V := ℕ))

@[simp] theorem primeFactorizationFormula_spec (f m : ℕ) :
    primeFactorizationFormula.Eval ![f, m] id ↔ PrimeFactorization f m :=
  formulaOf_spec (primeFactorization_definable (V := ℕ)) ![f, m]

noncomputable def baseDigitsFormula : PAFormula 3 :=
  formulaOf (baseDigits_definable (V := ℕ))

@[simp] theorem baseDigitsFormula_spec (v m b : ℕ) :
    baseDigitsFormula.Eval ![v, m, b] id ↔ BaseDigits v m b :=
  formulaOf_spec (baseDigits_definable (V := ℕ)) ![v, m, b]

noncomputable def divisorListFormula : PAFormula 2 :=
  formulaOf (divisorList_definable (V := ℕ))

@[simp] theorem divisorListFormula_spec (v m : ℕ) :
    divisorListFormula.Eval ![v, m] id ↔ DivisorList v m :=
  formulaOf_spec (divisorList_definable (V := ℕ)) ![v, m]

/-- Compatibility name for the PA formula listing all positive divisors. -/
noncomputable abbrev positiveDivisorsFormula : PAFormula 2 :=
  divisorListFormula

@[simp] theorem positiveDivisorsFormula_spec (v m : ℕ) :
    positiveDivisorsFormula.Eval ![v, m] id ↔ PositiveDivisors v m :=
  divisorListFormula_spec v m

/-! ## Standard-model bridges -/

/-- Foundation's bounded arithmetic primality predicate is ordinary primality on `ℕ`. -/
@[simp] theorem isPrime_iff_natPrime (p : ℕ) :
    IsPrime p ↔ Nat.Prime p := by
  rw [IsPrime, Nat.prime_def]
  constructor
  · rintro ⟨hp, hdiv⟩
    refine ⟨by omega, fun d hd ↦ ?_⟩
    have hdp : d ≤ p := Nat.le_of_dvd (by omega) hd
    exact hdiv d ((Nat.lt_or_eq_of_le hdp).elim Or.inr Or.inl) hd
  · rintro ⟨hp, hdiv⟩
    refine ⟨by omega, fun d _ hd ↦ hdiv d hd⟩

@[simp] theorem pairCode_encode_pair (a b : ℕ) :
    PairCode (encode [a, b]) a b := by
  refine ⟨encode_valid _, by simp, ?_, ?_⟩
  · exact encode_nth [a, b] ⟨0, by simp⟩
  · exact encode_nth [a, b] ⟨1, by simp⟩

@[simp] theorem strictlyIncreasing_encode_iff (xs : List ℕ) :
    StrictlyIncreasing (encode xs) ↔ xs.SortedLT := by
  simpa only [StrictlyIncreasing, IncreasingIndices] using
    increasingIndices_encode_iff xs

/-! ### Powers -/

/-- The internal multiplication trace computes exactly the ordinary power. -/
@[simp] theorem pow_iff (m n k : ℕ) : Pow m n k ↔ m = n ^ k := by
  constructor
  · rintro ⟨trace, htrace, hlen, hzero, hstep, hlast⟩
    have hpow : ∀ i, i < k + 1 → znth trace i = n ^ i := by
      intro i hi
      induction i with
      | zero => simpa using hzero
      | succ i ih =>
          have hik : i < k := by omega
          rw [hstep i hik, ih (by omega), pow_succ]
    exact hlast.symm.trans (hpow k (Nat.lt_succ_self k))
  · intro hm
    let values : List ℕ := List.ofFn fun i : Fin (k + 1) ↦ n ^ (i : ℕ)
    have hvalue (i : ℕ) (hi : i < k + 1) :
        znth (encode values) i = n ^ i := by
      let ii : Fin values.length := ⟨i, by simpa [values] using hi⟩
      calc
        znth (encode values) i = values.get ii := encode_nth values ii
        _ = n ^ i := by
          change (List.ofFn fun j : Fin (k + 1) ↦ n ^ (j : ℕ)).get ii = n ^ i
          rw [List.get_ofFn]
          rfl
    refine ⟨encode values, encode_valid values, by simp [values], ?_, ?_, ?_⟩
    · simpa using hvalue 0 (by omega)
    · intro i hi
      rw [hvalue (i + 1) (by omega), hvalue i (by omega), pow_succ]
    · rw [hvalue k (Nat.lt_succ_self k)]
      exact hm.symm

theorem pow_existsUnique (n k : ℕ) : ∃! m, Pow m n k := by
  exact ⟨n ^ k, (pow_iff (n ^ k) n k).2 rfl,
    fun m hm ↦ (pow_iff m n k).1 hm⟩

@[simp] theorem pow_zero_exponent (n : ℕ) : Pow 1 n 0 := by simp

@[simp] theorem pow_zero_base_succ (k : ℕ) : Pow 0 0 (k + 1) := by simp

/-! ### One-based prime enumeration -/

private theorem primePrefix_length_eq_count {p n below : ℕ}
    (hinc : StrictlyIncreasing below) (hlen : n = lh below + 1)
    (hsound : ∀ i < lh below, IsPrime (znth below i) ∧ znth below i < p)
    (hcomplete : ∀ q < p, IsPrime q → ∃ i < lh below, znth below i = q) :
    n = Nat.count Nat.Prime p + 1 := by
  let xs := decode below
  have hcode : encode xs = below := encode_decode hinc.1
  have hsorted : xs.SortedLT := by
    rw [← hcode] at hinc
    exact (strictlyIncreasing_encode_iff xs).1 hinc
  have hsets : xs.toFinset = (Finset.range p).filter Nat.Prime := by
    ext q
    constructor
    · intro hq
      have hmem : q ∈ xs := by simpa using hq
      rcases List.mem_iff_get.mp hmem with ⟨i, rfl⟩
      have hiBelow : (i : ℕ) < lh below := by
        rw [← hcode]
        simpa using i.isLt
      have hi := hsound (i : ℕ) hiBelow
      have hnth : znth below (i : ℕ) = xs.get i := by
        rw [← hcode]
        exact encode_nth xs i
      rw [hnth] at hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi.2,
        (isPrime_iff_natPrime _).mp hi.1⟩
    · intro hq
      rcases Finset.mem_filter.mp hq with ⟨hqp, hprime⟩
      rcases hcomplete q (Finset.mem_range.mp hqp)
        ((isPrime_iff_natPrime q).mpr hprime) with ⟨i, hi, heq⟩
      have hi' : i < xs.length := by
        rw [← hcode] at hi
        simpa using hi
      have hnth := encode_nth xs ⟨i, hi'⟩
      rw [hcode] at hnth
      exact List.mem_toFinset.mpr (List.mem_iff_get.mpr
        ⟨⟨i, hi'⟩, hnth.symm.trans heq⟩)
  calc
    n = xs.length + 1 := by
      rw [← hcode] at hlen
      simpa using hlen
    _ = xs.toFinset.card + 1 := by rw [List.toFinset_card_of_nodup hsorted.nodup]
    _ = ((Finset.range p).filter Nat.Prime).card + 1 := by rw [hsets]
    _ = Nat.count Nat.Prime p + 1 := by rw [Nat.count_eq_card_filter_range]

@[simp] theorem nthPrime_iff_count (p n : ℕ) :
    NthPrime p n ↔ Nat.Prime p ∧ n = Nat.count Nat.Prime p + 1 := by
  constructor
  · rintro ⟨hp, below, hinc, hlen, hsound, hcomplete⟩
    exact ⟨(isPrime_iff_natPrime p).mp hp,
      primePrefix_length_eq_count hinc hlen hsound hcomplete⟩
  · rintro ⟨hp, rfl⟩
    let xs := (List.range p).filter Nat.Prime
    refine ⟨(isPrime_iff_natPrime p).mpr hp, encode xs, ?_, ?_, ?_, ?_⟩
    · apply (strictlyIncreasing_encode_iff xs).2
      exact (List.pairwise_lt_range.filter _).sortedLT
    · simp [xs, Nat.count, List.countP_eq_length_filter]
    · intro i hi
      have hi' : i < xs.length := by simpa [xs] using hi
      have hmem := List.getElem_mem (l := xs) hi'
      simp only [xs, List.mem_filter, List.mem_range] at hmem
      rw [encode_nth xs ⟨i, hi'⟩]
      exact ⟨(isPrime_iff_natPrime _).2 (of_decide_eq_true hmem.2), hmem.1⟩
    · intro q hqp hq
      have hmem : q ∈ xs := by
        simp [xs, hqp, (isPrime_iff_natPrime q).mp hq]
      rcases List.mem_iff_get.mp hmem with ⟨i, hi⟩
      refine ⟨i, by simpa [xs] using i.isLt, ?_⟩
      simpa only [encode_nth xs i] using hi

/-- The public one-based interpretation, avoiding truncated subtraction. -/
theorem nthPrime_iff_nth (p n : ℕ) :
    NthPrime p n ↔ ∃ k, n = k + 1 ∧ p = Nat.nth Nat.Prime k := by
  rw [nthPrime_iff_count]
  constructor
  · rintro ⟨hp, hn⟩
    exact ⟨Nat.count Nat.Prime p, hn,
      (Nat.nth_count hp).symm⟩
  · rintro ⟨k, rfl, rfl⟩
    have hp : Nat.Prime (Nat.nth Nat.Prime k) :=
      Nat.nth_mem_of_infinite Nat.infinite_setOf_prime k
    exact ⟨hp, by rw [Nat.count_nth_of_infinite Nat.infinite_setOf_prime]⟩

theorem nthPrime_functional_index {p n₁ n₂ : ℕ}
    (h₁ : NthPrime p n₁) (h₂ : NthPrime p n₂) : n₁ = n₂ := by
  have hn₁ := ((nthPrime_iff_count p n₁).1 h₁).2
  have hn₂ := ((nthPrime_iff_count p n₂).1 h₂).2
  omega

theorem nthPrime_functional_prime {p₁ p₂ n : ℕ}
    (h₁ : NthPrime p₁ n) (h₂ : NthPrime p₂ n) : p₁ = p₂ := by
  rcases (nthPrime_iff_nth p₁ n).1 h₁ with ⟨k₁, hn₁, hp₁⟩
  rcases (nthPrime_iff_nth p₂ n).1 h₂ with ⟨k₂, hn₂, hp₂⟩
  have : k₁ = k₂ := by omega
  simpa [hp₁, hp₂, this]

theorem nthPrime_existsUnique (n : ℕ) (hn : 0 < n) :
    ∃! p, NthPrime p n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hcanonical : NthPrime (Nat.nth Nat.Prime k) (k + 1) :=
    (nthPrime_iff_nth _ _).2 ⟨k, rfl, rfl⟩
  refine ⟨Nat.nth Nat.Prime k, hcanonical, ?_⟩
  intro p hp
  exact nthPrime_functional_prime hp hcanonical

/-- Every ordinary prime occurs at exactly one one-based index. -/
theorem nthPrime_index_existsUnique (p : ℕ) (hp : Nat.Prime p) :
    ∃! n, NthPrime p n := by
  let n := Nat.count Nat.Prime p + 1
  have hcanonical : NthPrime p n :=
    (nthPrime_iff_count p n).2 ⟨hp, rfl⟩
  refine ⟨n, hcanonical, ?_⟩
  intro k hk
  exact nthPrime_functional_index hk hcanonical

@[simp] theorem nthPrime_zero_false (p : ℕ) : ¬NthPrime p 0 := by
  rw [nthPrime_iff_nth]
  omega

@[simp] theorem nthPrime_two_one : NthPrime 2 1 := by
  rw [nthPrime_iff_nth]
  exact ⟨0, rfl, Nat.nth_prime_zero_eq_two.symm⟩

/-! ### Positive divisors -/

/-- A convenient external spelling of the unique requested divisor list. -/
def canonicalDivisors (m : ℕ) : List ℕ :=
  (List.range (m + 1)).filter fun d ↦ 0 < d ∧ d ∣ m

@[simp] theorem mem_canonicalDivisors {d m : ℕ} :
    d ∈ canonicalDivisors m ↔ d ≤ m ∧ 0 < d ∧ d ∣ m := by
  simp [canonicalDivisors]

theorem canonicalDivisors_sorted (m : ℕ) :
    (canonicalDivisors m).SortedLT := by
  exact (List.pairwise_lt_range.filter _).sortedLT

/-- The PA relation says precisely "strictly sorted, and exactly the divisors". -/
@[simp] theorem divisorList_encode_iff (xs : List ℕ) (m : ℕ) :
    DivisorList (encode xs) m ↔
      m ≠ 0 ∧ xs.SortedLT ∧
        ∀ d, d ∈ xs ↔ 0 < d ∧ d ∣ m := by
  constructor
  · rintro ⟨hm, hsorted, hsound, hcomplete⟩
    refine ⟨hm, (strictlyIncreasing_encode_iff xs).1 hsorted, fun d ↦ ?_⟩
    constructor
    · intro hd
      rcases List.mem_iff_get.mp hd with ⟨i, rfl⟩
      have hi := hsound (i : ℕ) (by simpa using i.isLt)
      simpa only [encode_nth xs i] using hi
    · rintro ⟨hdpos, hdm⟩
      have hle : d ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hdm
      rcases hcomplete d (by omega) hdpos hdm with ⟨i, hi, heq⟩
      have hi' : i < xs.length := by simpa using hi
      have hnth := encode_nth xs ⟨i, hi'⟩
      exact List.mem_iff_get.mpr ⟨⟨i, hi'⟩, hnth.symm.trans heq⟩
  · rintro ⟨hm, hsorted, hmem⟩
    refine ⟨hm, (strictlyIncreasing_encode_iff xs).2 hsorted, ?_, ?_⟩
    · intro i hi
      have hi' : i < xs.length := by simpa using hi
      have hentry := (hmem xs[i]).1 (List.getElem_mem hi')
      change 0 < xs.get ⟨i, hi'⟩ ∧ xs.get ⟨i, hi'⟩ ∣ m at hentry
      simpa only [encode_nth xs ⟨i, hi'⟩] using hentry
    · intro d _ hdpos hdm
      rcases List.mem_iff_get.mp ((hmem d).2 ⟨hdpos, hdm⟩) with ⟨i, hi⟩
      refine ⟨i, by simpa using i.isLt, ?_⟩
      simpa only [encode_nth xs i] using hi

@[simp] theorem divisorList_canonical (m : ℕ) (hm : m ≠ 0) :
    DivisorList (encode (canonicalDivisors m)) m := by
  rw [divisorList_encode_iff]
  refine ⟨hm, canonicalDivisors_sorted m, fun d ↦ ?_⟩
  rw [mem_canonicalDivisors]
  constructor
  · exact fun h ↦ ⟨h.2.1, h.2.2⟩
  · rintro ⟨hdpos, hdm⟩
    exact ⟨Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hdm, hdpos, hdm⟩

private theorem sortedLT_eq_of_mem_iff {xs ys : List ℕ}
    (hxs : xs.SortedLT) (hys : ys.SortedLT)
    (hmem : ∀ d, d ∈ xs ↔ d ∈ ys) : xs = ys := by
  have hp : List.Perm xs ys :=
    (List.perm_ext_iff_of_nodup hxs.nodup hys.nodup).2 hmem
  exact hp.eq_of_sortedLE hxs.sortedLE hys.sortedLE

theorem divisorList_functional {v w m : ℕ}
    (hv : DivisorList v m) (hw : DivisorList w m) : v = w := by
  let xs := decode v
  let ys := decode w
  have hvcode : encode xs = v := encode_decode hv.2.1.1
  have hwcode : encode ys = w := encode_decode hw.2.1.1
  have hv' : DivisorList (encode xs) m := by simpa only [hvcode] using hv
  have hw' : DivisorList (encode ys) m := by simpa only [hwcode] using hw
  have hx := (divisorList_encode_iff xs m).1 hv'
  have hy := (divisorList_encode_iff ys m).1 hw'
  have hxy : xs = ys := sortedLT_eq_of_mem_iff hx.2.1 hy.2.1 fun d ↦
    (hx.2.2 d).trans (hy.2.2 d).symm
  rw [← hvcode, ← hwcode, hxy]

theorem divisorList_existsUnique (m : ℕ) (hm : m ≠ 0) :
    ∃! v, DivisorList v m := by
  refine ⟨encode (canonicalDivisors m), divisorList_canonical m hm, ?_⟩
  intro v hv
  exact divisorList_functional hv (divisorList_canonical m hm)

@[simp] theorem divisorList_zero_false (v : ℕ) : ¬DivisorList v 0 := by
  intro h
  exact h.1 rfl

@[simp] theorem divisorList_twelve_example :
    DivisorList (encode [1, 2, 3, 4, 6, 12]) 12 := by
  have h : canonicalDivisors 12 = [1, 2, 3, 4, 6, 12] := by
    decide
  rw [← h]
  exact divisorList_canonical 12 (by omega)

@[simp] theorem divisorList_one_example : DivisorList (encode [1]) 1 := by
  have h : canonicalDivisors 1 = [1] := by decide
  rw [← h]
  exact divisorList_canonical 1 (by omega)

/-! ### Canonical prime factorizations -/

/-- Encode an external list of `(prime, exponent)` pairs using nested PA lists. -/
noncomputable def encodeFactorPairs (fs : List (ℕ × ℕ)) : ℕ :=
  encode (fs.map fun pe ↦ encode [pe.1, pe.2])

@[simp] theorem encodeFactorPairs_valid (fs : List (ℕ × ℕ)) :
    Seq (encodeFactorPairs fs) := encode_valid _

@[simp] theorem encodeFactorPairs_length (fs : List (ℕ × ℕ)) :
    lh (encodeFactorPairs fs) = fs.length := by
  simp [encodeFactorPairs]

private theorem encodeFactorPairs_nth (fs : List (ℕ × ℕ))
    (i : Fin fs.length) :
    znth (encodeFactorPairs fs) i = encode [(fs.get i).1, (fs.get i).2] := by
  rw [encodeFactorPairs]
  have hi : (i : ℕ) < (fs.map fun pe ↦ encode [pe.1, pe.2]).length := by
    simpa using i.isLt
  rw [encode_nth _ ⟨i, hi⟩]
  simp

@[simp] theorem pairCode_encode_pair_iff (a b p e : ℕ) :
    PairCode (encode [a, b]) p e ↔ p = a ∧ e = b := by
  constructor
  · rintro ⟨-, -, hp, he⟩
    have ha := encode_nth [a, b] ⟨0, by simp⟩
    have hb := encode_nth [a, b] ⟨1, by simp⟩
    exact ⟨hp.symm.trans ha, he.symm.trans hb⟩
  · rintro ⟨hp, he⟩
    subst p
    subst e
    exact pairCode_encode_pair _ _

/-- A valid two-entry PA code is the canonical code of its two entries. -/
theorem pairCode_eq_encode_pair {c p e : ℕ} (h : PairCode c p e) :
    c = encode [p, e] := by
  let xs := decode c
  have hcode : encode xs = c := encode_decode h.1
  have hpair : PairCode (encode xs) p e := by simpa only [hcode] using h
  have hlen : xs.length = Nat.succ (Nat.succ Nat.zero) :=
    (encode_length xs).symm.trans hpair.2.1
  rcases List.length_eq_two.mp hlen with ⟨a, b, hab⟩
  have hp := (pairCode_encode_pair_iff a b p e).1 (by simpa [hab] using hpair)
  calc
    c = encode xs := hcode.symm
    _ = encode [a, b] := congrArg encode hab
    _ = encode [p, e] := by rw [hp.1, hp.2]

/-- Transparent ordinary-list semantics for a canonical factor-pair list. -/
def CanonicalFactorization (fs : List (ℕ × ℕ)) (m : ℕ) : Prop :=
  m ≠ 0 ∧
    (∀ pe ∈ fs, Nat.Prime pe.1 ∧ 0 < pe.2) ∧
    (fs.map Prod.fst).SortedLT ∧
    (fs.map fun pe ↦ pe.1 ^ pe.2).prod = m

private theorem factor_values_nth (fs : List (ℕ × ℕ))
    (i : Fin fs.length) :
    znth (encode (fs.map fun pe ↦ pe.1 ^ pe.2)) i =
      (fs.get i).1 ^ (fs.get i).2 := by
  have hi : (i : ℕ) < (fs.map fun pe ↦ pe.1 ^ pe.2).length := by
    simpa using i.isLt
  rw [encode_nth _ ⟨i, hi⟩]
  simp

/--
The nested PA relation is exactly prime/positive/strict factor data whose
prime powers multiply to `m`.  Product equality plus primality is the usual
FTA completeness condition, not merely soundness of a subset of factors.
-/
@[simp] theorem primeFactorization_encode_iff (fs : List (ℕ × ℕ)) (m : ℕ) :
    PrimeFactorization (encodeFactorPairs fs) m ↔ CanonicalFactorization fs m := by
  let values := fs.map fun pe ↦ pe.1 ^ pe.2
  constructor
  · rintro ⟨hm, -, hall, horder, trace, htrace, htlen, htzero,
      htstep, htlast⟩
    have hgood : ∀ pe ∈ fs, Nat.Prime pe.1 ∧ 0 < pe.2 := by
      intro pe hpe
      rcases List.mem_iff_get.mp hpe with ⟨i, rfl⟩
      rcases hall (i : ℕ) (by simpa using i.isLt) with
        ⟨p, e, hpair, hp, he⟩
      rw [encodeFactorPairs_nth fs i, pairCode_encode_pair_iff] at hpair
      rcases hpair with ⟨rfl, rfl⟩
      exact ⟨(isPrime_iff_natPrime _).1 hp, he⟩
    have hsorted : (fs.map Prod.fst).SortedLT := by
      rw [List.sortedLT_iff_pairwise, List.pairwise_iff_get]
      intro i j hij
      let ii : Fin fs.length := ⟨i, by simpa using i.isLt⟩
      let jj : Fin fs.length := ⟨j, by simpa using j.isLt⟩
      have hij' := horder (ii : ℕ) (by simpa using ii.isLt)
        (jj : ℕ) (by simpa using jj.isLt) (by simpa [ii, jj] using hij)
      rw [encodeFactorPairs_nth fs ii, encodeFactorPairs_nth fs jj,
        encode_nth [(fs.get ii).1, (fs.get ii).2] ⟨0, by simp⟩,
        encode_nth [(fs.get jj).1, (fs.get jj).2] ⟨0, by simp⟩] at hij'
      simpa using hij'
    have hproductRel : ProductElements m (encode values) := by
      refine ⟨encode_valid values, trace, htrace, ?_, htzero, ?_, ?_⟩
      · simpa [values] using htlen
      · intro i hi
        have hi' : i < fs.length := by simpa [values] using hi
        rcases htstep i (by simpa using hi') with ⟨p, e, pe, hpair, hpow, hacc⟩
        let ii : Fin fs.length := ⟨i, hi'⟩
        rw [encodeFactorPairs_nth fs ii, pairCode_encode_pair_iff] at hpair
        rcases hpair with ⟨rfl, rfl⟩
        have hpe : pe = (fs.get ii).1 ^ (fs.get ii).2 :=
          (pow_iff pe (fs.get ii).1 (fs.get ii).2).1 hpow
        calc
          znth trace (i + 1) = znth trace i * pe := hacc
          _ = znth trace i * znth (encode values) i := by
            rw [hpe]
            congr 1
            simpa [values] using (factor_values_nth fs ii).symm
      · simpa [values] using htlast
    have hprod : values.prod = m :=
      (productElements_encode_iff_prod m values).1 hproductRel
    exact ⟨hm, hgood, hsorted, by simpa [values] using hprod⟩
  · rintro ⟨hm, hgood, hsorted, hprod⟩
    have hproductRel : ProductElements m (encode values) :=
      (productElements_encode_iff_prod m values).2 (by simpa [values] using hprod)
    rcases hproductRel with ⟨-, trace, htrace, htlen, htzero, htstep, htlast⟩
    refine ⟨hm, encodeFactorPairs_valid fs, ?_, ?_, trace, htrace, ?_, htzero, ?_, ?_⟩
    · intro i hi
      have hi' : i < fs.length := by simpa using hi
      let ii : Fin fs.length := ⟨i, hi'⟩
      have hg := hgood (fs.get ii) (List.get_mem fs ii)
      refine ⟨(fs.get ii).1, (fs.get ii).2, ?_,
        (isPrime_iff_natPrime _).2 hg.1, hg.2⟩
      rw [encodeFactorPairs_nth fs ii]
      exact pairCode_encode_pair _ _
    · intro i hi j hj hij
      have hi' : i < fs.length := by simpa using hi
      have hj' : j < fs.length := by simpa using hj
      let ii : Fin fs.length := ⟨i, hi'⟩
      let jj : Fin fs.length := ⟨j, hj'⟩
      have hs : (fs.get ii).1 < (fs.get jj).1 := by
        rw [List.sortedLT_iff_pairwise, List.pairwise_iff_get] at hsorted
        let iii : Fin (fs.map Prod.fst).length := ⟨i, by simpa using hi'⟩
        let jjj : Fin (fs.map Prod.fst).length := ⟨j, by simpa using hj'⟩
        have hs' := hsorted iii jjj (by simpa [iii, jjj] using hij)
        simpa [iii, jjj, ii, jj] using hs'
      rw [encodeFactorPairs_nth fs ii, encodeFactorPairs_nth fs jj,
        encode_nth [(fs.get ii).1, (fs.get ii).2] ⟨0, by simp⟩,
        encode_nth [(fs.get jj).1, (fs.get jj).2] ⟨0, by simp⟩]
      exact hs
    · simpa [values] using htlen
    · intro i hi
      have hi' : i < fs.length := by simpa using hi
      let ii : Fin fs.length := ⟨i, hi'⟩
      refine ⟨(fs.get ii).1, (fs.get ii).2,
        (fs.get ii).1 ^ (fs.get ii).2, ?_, ?_, ?_⟩
      · rw [encodeFactorPairs_nth fs ii]
        exact pairCode_encode_pair _ _
      · exact (pow_iff _ _ _).2 rfl
      · have hs := htstep i (by simpa [values] using hi')
        calc
          znth trace (i + 1) =
              znth trace i * znth (encode values) i := hs
          _ = znth trace i * ((fs.get ii).1 ^ (fs.get ii).2) := by
            congr 1
            simpa [values] using factor_values_nth fs ii
    · simpa [values] using htlast

/-- Expand factor pairs back to the conventional multiset-style prime list. -/
def expandFactorPairs (fs : List (ℕ × ℕ)) : List ℕ :=
  fs.flatMap fun pe ↦ List.replicate pe.2 pe.1

@[simp] theorem prod_expandFactorPairs (fs : List (ℕ × ℕ)) :
    (expandFactorPairs fs).prod = (fs.map fun pe ↦ pe.1 ^ pe.2).prod := by
  induction fs with
  | nil => simp [expandFactorPairs]
  | cons pe fs ih =>
      simp only [expandFactorPairs, List.flatMap_cons, List.prod_append,
        List.prod_replicate, List.map_cons, List.prod_cons]
      change pe.1 ^ pe.2 * (expandFactorPairs fs).prod =
        pe.1 ^ pe.2 * (fs.map fun pe ↦ pe.1 ^ pe.2).prod
      rw [ih]

/-- FTA certifies that the represented pairs contain the complete factorization. -/
theorem canonicalFactorization_expanded_perm {fs : List (ℕ × ℕ)} {m : ℕ}
    (h : CanonicalFactorization fs m) :
    List.Perm (expandFactorPairs fs) m.primeFactorsList := by
  apply Nat.primeFactorsList_unique
  · rw [prod_expandFactorPairs]
    exact h.2.2.2
  · intro p hp
    simp only [expandFactorPairs, List.mem_flatMap, List.mem_replicate] at hp
    rcases hp with ⟨pe, hpe, -, rfl⟩
    exact (h.2.1 pe hpe).1

private theorem mem_fst_of_mem_expandFactorPairs {p : ℕ} {fs : List (ℕ × ℕ)}
    (hp : p ∈ expandFactorPairs fs) : p ∈ fs.map Prod.fst := by
  simp only [expandFactorPairs, List.mem_flatMap, List.mem_replicate] at hp
  rcases hp with ⟨pe, hpe, -, rfl⟩
  exact List.mem_map.mpr ⟨pe, hpe, rfl⟩

private theorem mem_expandFactorPairs_iff_fst {p : ℕ} {fs : List (ℕ × ℕ)}
    (hpos : ∀ pe ∈ fs, 0 < pe.2) :
    p ∈ expandFactorPairs fs ↔ p ∈ fs.map Prod.fst := by
  constructor
  · exact mem_fst_of_mem_expandFactorPairs
  · intro hp
    rcases List.mem_map.mp hp with ⟨pe, hpe, rfl⟩
    simp only [expandFactorPairs, List.mem_flatMap, List.mem_replicate]
    exact ⟨pe, hpe, (hpos pe hpe).ne', rfl⟩

private theorem count_expandFactorPairs_of_mem {fs : List (ℕ × ℕ)}
    (hnodup : (fs.map Prod.fst).Nodup) {p e : ℕ} (hpe : (p, e) ∈ fs) :
    (expandFactorPairs fs).count p = e := by
  induction fs with
  | nil => simp at hpe
  | cons qe fs ih =>
      simp only [List.map_cons, List.nodup_cons] at hnodup
      rcases hnodup with ⟨hq, hnodup⟩
      simp only [List.mem_cons] at hpe
      rcases hpe with hhead | htail
      · cases hhead
        rw [expandFactorPairs, List.flatMap_cons, List.count_append]
        have hzero : (expandFactorPairs fs).count p = 0 := by
          apply List.count_eq_zero.mpr
          intro hp
          exact hq (mem_fst_of_mem_expandFactorPairs hp)
        change (List.replicate e p).count p + (expandFactorPairs fs).count p = e
        rw [hzero]
        simp
      · have hpkey : p ∈ fs.map Prod.fst := by
          exact List.mem_map.mpr ⟨(p, e), htail, rfl⟩
        have hpq : p ≠ qe.1 := by
          intro hpq
          exact hq (hpq ▸ hpkey)
        rw [expandFactorPairs, List.flatMap_cons, List.count_append]
        have hi := ih hnodup htail
        change (List.replicate qe.2 qe.1).count p +
          (expandFactorPairs fs).count p = e
        rw [hi]
        have hzero : (List.replicate qe.2 qe.1).count p = 0 := by
          apply List.count_eq_zero.mpr
          simp [hpq]
        rw [hzero, Nat.zero_add]

/-- The canonical sorted support of Mathlib's factorization finsupp. -/
noncomputable def canonicalFactorPairs (m : ℕ) : List (ℕ × ℕ) :=
  m.factorization.support.sort.map fun p ↦ (p, m.factorization p)

private theorem canonicalFactorPairs_fst (m : ℕ) :
    (canonicalFactorPairs m).map Prod.fst = m.factorization.support.sort := by
  let ps := m.factorization.support.sort
  change (ps.map fun p ↦ (p, m.factorization p)).map Prod.fst = ps
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [ih]

private theorem canonicalFactorPairs_values (m : ℕ) :
    (canonicalFactorPairs m).map (fun pe ↦ pe.1 ^ pe.2) =
      m.factorization.support.sort.map (fun p ↦ p ^ m.factorization p) := by
  let ps := m.factorization.support.sort
  change (ps.map fun p ↦ (p, m.factorization p)).map
      (fun pe ↦ pe.1 ^ pe.2) = ps.map (fun p ↦ p ^ m.factorization p)
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [ih]

theorem canonicalFactorPairs_conditions (m : ℕ) (hm : m ≠ 0) :
    CanonicalFactorization (canonicalFactorPairs m) m := by
  refine ⟨hm, ?_, ?_, ?_⟩
  · intro pe hpe
    simp only [canonicalFactorPairs, List.mem_map] at hpe
    rcases hpe with ⟨p, hp, rfl⟩
    have hps : p ∈ m.factorization.support :=
      (Finset.mem_sort (r := (· ≤ ·))).1 hp
    refine ⟨?_, Finsupp.mem_support_iff.mp hps |>.bot_lt⟩
    exact Nat.prime_of_mem_primeFactors
      (by simpa only [Nat.support_factorization] using hps)
  · rw [canonicalFactorPairs_fst]
    exact Finset.sortedLT_sort m.factorization.support
  · have hperm := (Finset.sort_perm_toList m.factorization.support (· ≤ ·)).map
        (fun p ↦ p ^ m.factorization p)
    calc
      ((canonicalFactorPairs m).map fun pe ↦ pe.1 ^ pe.2).prod =
          ((m.factorization.support.sort).map
            fun p ↦ p ^ m.factorization p).prod := by
              rw [canonicalFactorPairs_values]
      _ = (m.factorization.support.toList.map
            fun p ↦ p ^ m.factorization p).prod := hperm.prod_eq
      _ = m.factorization.support.prod (fun p ↦ p ^ m.factorization p) :=
        Finset.prod_map_toList _ _
      _ = m.factorization.prod (· ^ ·) := rfl
      _ = m := Nat.prod_factorization_pow_eq_self hm

theorem canonicalFactorization_unique {fs : List (ℕ × ℕ)} {m : ℕ}
    (h : CanonicalFactorization fs m) : fs = canonicalFactorPairs m := by
  have hperm := canonicalFactorization_expanded_perm h
  have hkeys : fs.map Prod.fst = m.factorization.support.sort := by
    apply sortedLT_eq_of_mem_iff h.2.2.1 (Finset.sortedLT_sort _)
    intro p
    rw [Finset.mem_sort]
    calc
      p ∈ fs.map Prod.fst ↔ p ∈ expandFactorPairs fs :=
        (mem_expandFactorPairs_iff_fst (fun pe hpe ↦ (h.2.1 pe hpe).2)).symm
      _ ↔ p ∈ m.primeFactorsList := hperm.mem_iff
      _ ↔ p ∈ m.factorization.support := by
        simpa only [Nat.support_factorization] using
          (Nat.mem_primeFactors_iff_mem_primeFactorsList (n := m) (p := p)).symm
  have hnormalize : fs.map (fun pe ↦ (pe.1, m.factorization pe.1)) = fs := by
    simpa only [List.map_id] using List.map_congr_left (l := fs)
      (f := fun pe ↦ (pe.1, m.factorization pe.1)) (g := id) (by
        intro pe hpe
        apply Prod.ext
        · rfl
        · have hc := count_expandFactorPairs_of_mem h.2.2.1.nodup hpe
          have hpcount := hperm.count_eq pe.1
          change m.factorization pe.1 = pe.2
          exact (by
            simpa only [Nat.primeFactorsList_count_eq] using
              (hc.symm.trans hpcount).symm))
  calc
    fs = fs.map (fun pe ↦ (pe.1, m.factorization pe.1)) := hnormalize.symm
    _ = (fs.map Prod.fst).map (fun p ↦ (p, m.factorization p)) := by
      simp [List.map_map]
    _ = canonicalFactorPairs m := by rw [hkeys]; rfl

/-- Every internal factorization code can be re-expressed as nested pair codes. -/
theorem primeFactorization_exists_factorPairs {f m : ℕ}
    (h : PrimeFactorization f m) :
    ∃ fs : List (ℕ × ℕ), encodeFactorPairs fs = f := by
  let cs := decode f
  let fs := cs.map fun c ↦ (znth c 0, znth c 1)
  have hfcode : encode cs = f := encode_decode h.2.1
  have hmap : fs.map (fun pe ↦ encode [pe.1, pe.2]) = cs := by
    have hmapped : cs.map (fun c ↦ encode [znth c 0, znth c 1]) = cs.map id := by
      apply List.map_congr_left
      intro c hc
      rcases List.mem_iff_get.mp hc with ⟨i, rfl⟩
      have hiF : (i : ℕ) < lh f := by
        rw [← hfcode]
        simpa using i.isLt
      rcases h.2.2.1 (i : ℕ) hiF with ⟨p, e, hpair, -, -⟩
      have hnth : znth f (i : ℕ) = cs.get i := by
        rw [← hfcode]
        exact encode_nth cs i
      rw [hnth] at hpair
      calc
        encode [znth (cs.get i) 0, znth (cs.get i) 1] = encode [p, e] := by
          rw [hpair.2.2.1, hpair.2.2.2]
        _ = cs.get i := (pairCode_eq_encode_pair hpair).symm
    change (cs.map fun c ↦ (znth c 0, znth c 1)).map
        (fun pe ↦ encode [pe.1, pe.2]) = cs
    rw [List.map_map]
    change cs.map (fun c ↦ encode [znth c 0, znth c 1]) = cs
    simpa only [List.map_id] using hmapped
  refine ⟨fs, ?_⟩
  rw [encodeFactorPairs, hmap]
  exact hfcode

theorem primeFactorization_functional {f g m : ℕ}
    (hf : PrimeFactorization f m) (hg : PrimeFactorization g m) : f = g := by
  rcases primeFactorization_exists_factorPairs hf with ⟨fs, rfl⟩
  rcases primeFactorization_exists_factorPairs hg with ⟨gs, rfl⟩
  have hfs := (primeFactorization_encode_iff fs m).1 hf
  have hgs := (primeFactorization_encode_iff gs m).1 hg
  have hfg : fs = gs :=
    (canonicalFactorization_unique hfs).trans (canonicalFactorization_unique hgs).symm
  rw [hfg]

theorem primeFactorization_existsUnique (m : ℕ) (hm : m ≠ 0) :
    ∃! f, PrimeFactorization f m := by
  let f := encodeFactorPairs (canonicalFactorPairs m)
  have hf : PrimeFactorization f m :=
    (primeFactorization_encode_iff _ _).2 (canonicalFactorPairs_conditions m hm)
  exact ⟨f, hf, fun g hg ↦ primeFactorization_functional hg hf⟩

@[simp] theorem primeFactorization_zero_false (f : ℕ) :
    ¬PrimeFactorization f 0 := by intro h; exact h.1 rfl

@[simp] theorem primeFactorization_one_empty :
    PrimeFactorization (encodeFactorPairs []) 1 := by
  rw [primeFactorization_encode_iff, CanonicalFactorization]
  refine ⟨by omega, by simp, ?_, by simp⟩
  simp [List.sortedLT_iff_pairwise]

@[simp] theorem primeFactorization_360_example :
    PrimeFactorization (encodeFactorPairs [(2, 3), (3, 2), (5, 1)]) 360 := by
  rw [primeFactorization_encode_iff, CanonicalFactorization]
  refine ⟨by omega, ?_, by decide, by norm_num⟩
  intro pe hpe
  simp at hpe
  rcases hpe with rfl | rfl | rfl
  · exact ⟨Nat.prime_two, by omega⟩
  · exact ⟨Nat.prime_three, by omega⟩
  · exact ⟨Nat.prime_five, by omega⟩

/-! ### Most-significant-digit-first base expansions -/

/-- Evaluate an MSD-first digit list by Horner's rule. -/
def msdValue (b : ℕ) (xs : List ℕ) : ℕ :=
  xs.foldl (fun acc d ↦ acc * b + d) 0

/-- Mathlib's `ofDigits` reads in the opposite (least-significant-first) order. -/
theorem msdValue_eq_ofDigits_reverse (b : ℕ) (xs : List ℕ) :
    msdValue b xs = Nat.ofDigits b xs.reverse := by
  have haux : ∀ acc : ℕ,
      xs.foldl (fun a d ↦ a * b + d) acc =
        acc * b ^ xs.length + Nat.ofDigits b xs.reverse := by
    induction xs with
    | nil => simp
    | cons d ds ih =>
        intro acc
        rw [List.foldl_cons, ih]
        simp only [List.length_cons, List.reverse_cons, Nat.ofDigits_append,
          Nat.ofDigits_singleton, pow_succ, List.length_reverse]
        ring
  simpa [msdValue] using haux 0

/-- External, transparent semantics of the PA digit relation. -/
def CanonicalDigitConditions (xs : List ℕ) (m b : ℕ) : Prop :=
  Nat.le 2 b ∧ xs ≠ [] ∧ (∀ d ∈ xs, d < b) ∧
    ((m = 0 ∧ xs = [0]) ∨ (0 < m ∧ xs.getD 0 0 ≠ 0)) ∧
    msdValue b xs = m

private theorem digit_bounds_iff (xs : List ℕ) (b : ℕ) :
    (∀ i < xs.length, znth (encode xs) i < b) ↔
      ∀ d ∈ xs, d < b := by
  constructor
  · intro h d hd
    rcases List.mem_iff_get.mp hd with ⟨i, rfl⟩
    simpa only [encode_nth xs i] using h (i : ℕ) (by simpa using i.isLt)
  · intro h i hi
    have hentry := h xs[i] (List.getElem_mem hi)
    change xs.get ⟨i, hi⟩ < b at hentry
    simpa only [encode_nth xs ⟨i, hi⟩] using hentry

private theorem digit_zero_shape_iff (xs : List ℕ) (m : ℕ) :
    (m = 0 ∧ xs.length = 1 ∧ znth (encode xs) 0 = 0) ↔
      m = 0 ∧ xs = [0] := by
  constructor
  · rintro ⟨rfl, hlen, hzero⟩
    have hlen' : xs.length = 1 := hlen
    have hindex : 0 < xs.length := by omega
    have hfirst : xs.get ⟨0, hindex⟩ = 0 := by
      exact (encode_nth xs ⟨0, hindex⟩).symm.trans hzero
    refine ⟨rfl, ?_⟩
    calc
      xs = [xs.get ⟨0, by omega⟩] := List.eq_cons_of_length_one hlen'
      _ = [0] := by simp only [hfirst]
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, by simp, by
      simpa using (encode_nth [0] ⟨0, by simp⟩)⟩

private theorem digit_positive_shape_iff (xs : List ℕ) (m : ℕ)
    (hxs : 0 < xs.length) :
    (0 < m ∧ znth (encode xs) 0 ≠ 0) ↔
      0 < m ∧ xs.getD 0 0 ≠ 0 := by
  have hfirst : znth (encode xs) 0 = xs.getD 0 0 := by
    rw [List.getD_eq_getElem xs 0 hxs]
    exact encode_nth xs ⟨0, hxs⟩
  simp only [hfirst]

@[simp] theorem baseDigits_encode_iff_conditions (xs : List ℕ) (m b : ℕ) :
    BaseDigits (encode xs) m b ↔ CanonicalDigitConditions xs m b := by
  rw [BaseDigits, CanonicalDigitConditions]
  simp only [encode_valid, true_and, encode_length]
  constructor
  · rintro ⟨hb, hlen, hbounds, hshape, traceCode, htrace, htlen,
      htzero, htstep, htlast⟩
    have hfold : msdValue b xs = m := by
      rw [msdValue]
      rw [← exists_runningAggregateTrace_iff_foldl 0
        (fun a d : ℕ ↦ a * b + d) xs m]
      rw [← coded_runningAggregate_iff 0
        (fun a d : ℕ ↦ a * b + d) xs m]
      simpa only [encode_length] using
        (show ∃ traceCode, Seq traceCode ∧
            lh traceCode = xs.length + 1 ∧ znth traceCode 0 = 0 ∧
            (∀ i < xs.length, znth traceCode (i + 1) =
              znth traceCode i * b + znth (encode xs) i) ∧
            znth traceCode xs.length = m from
          ⟨traceCode, htrace, htlen, htzero, htstep, htlast⟩)
    have hb' : Nat.le 2 b := by
      rw [LO.FirstOrder.Arithmetic.le_def] at hb
      exact hb.elim Nat.le_of_eq Nat.le_of_lt
    refine ⟨hb', List.ne_nil_of_length_pos hlen,
      (digit_bounds_iff xs b).1 hbounds, ?_, hfold⟩
    rcases hshape with hzero | hpos
    · exact Or.inl ((digit_zero_shape_iff xs m).1 hzero)
    · exact Or.inr ((digit_positive_shape_iff xs m hlen).1 hpos)
  · rintro ⟨hb, hne, hbounds, hshape, hfold⟩
    have hlen : 0 < xs.length := by
      have : xs.length ≠ 0 := fun h ↦ hne (List.length_eq_zero_iff.mp h)
      omega
    have htrace : ∃ traceCode, Seq traceCode ∧
        lh traceCode = lh (encode xs) + 1 ∧ znth traceCode 0 = 0 ∧
        (∀ i < lh (encode xs),
          znth traceCode (i + 1) =
            znth traceCode i * b + znth (encode xs) i) ∧
        znth traceCode (lh (encode xs)) = m := by
      rw [coded_runningAggregate_iff 0
        (fun a d : ℕ ↦ a * b + d) xs m,
        exists_runningAggregateTrace_iff_foldl]
      rw [msdValue] at hfold
      exact hfold
    refine ⟨?_, hlen, (digit_bounds_iff xs b).2 hbounds, ?_, ?_⟩
    · rw [LO.FirstOrder.Arithmetic.le_def]
      exact (Nat.lt_or_eq_of_le hb).elim Or.inr Or.inl
    rcases hshape with hzero | hpos
    · exact Or.inl ((digit_zero_shape_iff xs m).2 hzero)
    · exact Or.inr ((digit_positive_shape_iff xs m hlen).2 hpos)
    · simpa only [encode_length] using htrace

/-- The canonical external MSD-first list, including the stipulated zero digit. -/
def canonicalBaseDigits (m b : ℕ) : List ℕ :=
  if m = 0 then [0] else (Nat.digits b m).reverse

private theorem conditions_eq_canonical {xs : List ℕ} {m b : ℕ}
    (h : CanonicalDigitConditions xs m b) : xs = canonicalBaseDigits m b := by
  rcases h with ⟨hb, hne, hbounds, hshape, hvalue⟩
  rcases hshape with ⟨rfl, rfl⟩ | ⟨hmpos, hfirst⟩
  · simp [canonicalBaseDigits]
  · have hof : Nat.ofDigits b xs.reverse = m := by
      rw [← msdValue_eq_ofDigits_reverse, hvalue]
    have hlast : ∀ hne' : xs.reverse ≠ [], (xs.reverse).getLast hne' ≠ 0 := by
      intro hne'
      cases xs with
      | nil => exact (hne rfl).elim
      | cons d ds => simpa [List.reverse_cons] using hfirst
    have hdigits : Nat.digits b m = xs.reverse := by
      rw [← hof]
      apply Nat.digits_ofDigits b (Nat.lt_of_succ_le hb) xs.reverse
      · intro d hd
        exact hbounds d (by simpa using hd)
      · exact hlast
    have hrev : xs = (Nat.digits b m).reverse := by
      simpa using congrArg List.reverse hdigits.symm
    simpa [canonicalBaseDigits, hmpos.ne'] using hrev

private theorem digits_getLast?_ne_zero {b m : ℕ} (hb : 1 < b) (hm : m ≠ 0) :
    (Nat.digits b m).getLast? ≠ some 0 := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
      rw [Nat.digits_eq_cons_digits_div hb hm]
      by_cases hq : m / b = 0
      · simp [hq]
        intro hmod
        apply hm
        have hdecomp := Nat.mod_add_div m b
        simpa [hmod, hq] using hdecomp.symm
      · have htail : Nat.digits b (m / b) ≠ [] :=
          Nat.digits_ne_nil_iff_ne_zero.mpr hq
        rcases List.exists_cons_of_ne_nil htail with ⟨d, ds, htailEq⟩
        rw [htailEq, List.getLast?_cons_cons]
        have hrec :=
          ih (m / b) (Nat.div_lt_self (Nat.pos_of_ne_zero hm) hb) hq
        rw [htailEq] at hrec
        exact hrec

private theorem digits_getLast_ne_zero {b m : ℕ} (hb : 1 < b) (hm : m ≠ 0)
    (hne : Nat.digits b m ≠ []) : (Nat.digits b m).getLast hne ≠ 0 := by
  intro hzero
  apply digits_getLast?_ne_zero hb hm
  rw [List.getLast?_eq_getLast_of_ne_nil hne, hzero]

private theorem reverse_getD_zero_eq_getLast {xs : List ℕ} (hne : xs ≠ []) :
    xs.reverse.getD 0 0 = xs.getLast hne := by
  have hopt := List.getLast?_eq_getLast_of_ne_nil hne
  rw [← List.head?_reverse] at hopt
  have hgetD := congrArg (fun o : Option ℕ ↦ o.getD 0) hopt
  simpa [List.getD, List.head?_eq_getElem?] using hgetD

private theorem canonical_conditions (m b : ℕ) (hb : Nat.le 2 b) :
    CanonicalDigitConditions (canonicalBaseDigits m b) m b := by
  by_cases hm : m = 0
  · subst m
    refine ⟨hb, by simp [canonicalBaseDigits], ?_, Or.inl ⟨rfl, by
      simp [canonicalBaseDigits]⟩, by simp [canonicalBaseDigits, msdValue]⟩
    intro d hd
    have hd0 : d = 0 := by simpa [canonicalBaseDigits] using hd
    subst d
    exact Nat.lt_of_lt_of_le (by decide : 0 < 2) hb
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hb1 : 1 < b := Nat.lt_of_succ_le hb
    have hneDigits : Nat.digits b m ≠ [] :=
      Nat.digits_ne_nil_iff_ne_zero.mpr hm
    have hbounds : ∀ d ∈ Nat.digits b m, d < b := by
      intro d hd
      exact Nat.digits_lt_base hb1 hd
    refine ⟨hb, by simp [canonicalBaseDigits, hm, hneDigits], ?_, ?_, ?_⟩
    · intro d hd
      exact hbounds d (by simpa [canonicalBaseDigits, hm] using hd)
    · right
      refine ⟨hmpos, ?_⟩
      have hlast := digits_getLast_ne_zero (b := b) (m := m) hb1 hm hneDigits
      rw [canonicalBaseDigits, if_neg hm, reverse_getD_zero_eq_getLast hneDigits]
      exact hlast
    · rw [msdValue_eq_ofDigits_reverse]
      simp [canonicalBaseDigits, hm, Nat.ofDigits_digits]

@[simp] theorem baseDigits_encode_iff (xs : List ℕ) (m b : ℕ) :
    BaseDigits (encode xs) m b ↔
      Nat.le 2 b ∧ xs = canonicalBaseDigits m b := by
  constructor
  · intro h
    have hc := (baseDigits_encode_iff_conditions xs m b).1 h
    exact ⟨hc.1, conditions_eq_canonical hc⟩
  · rintro ⟨hb, rfl⟩
    exact (baseDigits_encode_iff_conditions _ _ _).2
      (canonical_conditions m b hb)

theorem baseDigits_functional {v w m b : ℕ}
    (hv : BaseDigits v m b) (hw : BaseDigits w m b) : v = w := by
  let xs := decode v
  let ys := decode w
  have hvcode : encode xs = v := encode_decode hv.1
  have hwcode : encode ys = w := encode_decode hw.1
  have hx := (baseDigits_encode_iff xs m b).1 (by simpa only [hvcode] using hv)
  have hy := (baseDigits_encode_iff ys m b).1 (by simpa only [hwcode] using hw)
  rw [← hvcode, ← hwcode, hx.2, hy.2]

theorem baseDigits_existsUnique (m b : ℕ) (hb : Nat.le 2 b) :
    ∃! v, BaseDigits v m b := by
  have hcanonical : BaseDigits (encode (canonicalBaseDigits m b)) m b :=
    (baseDigits_encode_iff _ _ _).2 ⟨hb, rfl⟩
  exact ⟨_, hcanonical, fun v hv ↦ baseDigits_functional hv hcanonical⟩

@[simp] theorem baseDigits_invalid_base_zero (v m : ℕ) :
    ¬BaseDigits v m 0 := by
  intro h
  have hb := h.2.1
  rw [LO.FirstOrder.Arithmetic.le_def] at hb
  omega

@[simp] theorem baseDigits_invalid_base_one (v m : ℕ) :
    ¬BaseDigits v m 1 := by
  intro h
  have hb := h.2.1
  rw [LO.FirstOrder.Arithmetic.le_def] at hb
  omega

@[simp] theorem baseDigits_zero (b : ℕ) (hb : Nat.le 2 b) :
    BaseDigits (encode [0]) 0 b := by
  rw [baseDigits_encode_iff]
  exact ⟨hb, by simp [canonicalBaseDigits]⟩

@[simp] theorem baseDigits_13_binary :
    BaseDigits (encode [1, 1, 0, 1]) 13 2 := by
  rw [baseDigits_encode_iff_conditions]
  norm_num [CanonicalDigitConditions, msdValue] <;> simp

end PAListCoding
