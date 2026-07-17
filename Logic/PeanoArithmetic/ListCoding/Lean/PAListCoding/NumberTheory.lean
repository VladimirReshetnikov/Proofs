import PAListCoding.Aggregates
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Factors
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

end PAListCoding
