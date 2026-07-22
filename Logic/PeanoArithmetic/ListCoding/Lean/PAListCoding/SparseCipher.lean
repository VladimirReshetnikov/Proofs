import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.Indexes
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.NumberTheory.Dioph

/-!
# Sparse arithmetic ciphers for bounded sequences

This file is the semantic core of the finite-sequence cipher used in
Matiyasevich's elimination of bounded universal quantifiers.  It follows the
construction in the vendored Rocq development
`Undecidability.H10.Matija.cipher` (in particular its `is_cipher_of` layer).

For a length `len` and spacing parameter `q`, the `i`-th entry is put at the
base-`radix q` digit whose position is `2^(i+1)`.  Thus

```
  encode len q f = ∑ i < len, f i * (2^(4*q))^(2^(i+1)).
```

Powers of two are a *Sidon sequence with multiplicity*: a sum of two places
is itself a place precisely when the two summands are equal.  Consequently a
product of two ciphers has its pointwise products at the next sparse places;
all mixed products occupy positions having two distinct binary bits.  The
large radix leaves enough room to prevent carries.

The definitions below are deliberately arithmetic and the semantic theorems
contain no choice axioms beyond Lean's ordinary classical reasoning.  Later
modules may compile the arithmetic certificate relations to `Dioph` without
ever putting a variable bounded universal quantifier into a definition.
-/

namespace PAListCoding

namespace SparseCipher

open scoped BigOperators

/-- The base used by the Rocq cipher.  Writing it as one power of two makes
the coefficient estimates for products particularly transparent. -/
def radix (q : ℕ) : ℕ := 2 ^ (4 * q)

/-- The sparse digit position occupied by the entry with zero-based index
`i`.  The first entry is at position two, not at position zero. -/
def place (i : ℕ) : ℕ := 2 ^ (i + 1)

/-- Arithmetic encoding of a finite prefix of a sequence. -/
def encode (len q : ℕ) (f : ℕ → ℕ) : ℕ :=
  ∑ i ∈ Finset.range len, f i * radix q ^ place i

/-- A well-formed cipher carries both the spacing condition and the digit
bound used in the no-carry arguments. -/
def IsCipher (len q : ℕ) (f : ℕ → ℕ) (c : ℕ) : Prop :=
  len + 1 < q ∧ (∀ i, i < len → f i < 2 ^ q) ∧ c = encode len q f

/-- Any bounded prefix has its canonical sparse code. -/
theorem exists_isCipher {len q : ℕ} {f : ℕ → ℕ}
    (hlen : len + 1 < q) (hbound : ∀ i, i < len → f i < 2 ^ q) :
    ∃ c, IsCipher len q f c :=
  ⟨encode len q f, hlen, hbound, rfl⟩

/-! ## Dense base expansions used only in semantic proofs

`encode` is the sparse sum above, which is the form needed by arithmetic
certificate relations.  For uniqueness it is convenient to compare it with
an ordinary dense base expansion, filling all unused positions by zero.
-/

/-- `place` is strictly increasing. -/
theorem place_strictMono : StrictMono place := by
  intro i j hij
  unfold place
  exact Nat.pow_lt_pow_right (by omega) (by omega)

theorem place_injective : Function.Injective place :=
  place_strictMono.injective

theorem place_lt_place {i j : ℕ} (h : i < j) : place i < place j :=
  place_strictMono h

theorem place_lt_iff {i j : ℕ} : place i < place j ↔ i < j := by
  unfold place
  rw [Nat.pow_lt_pow_iff_right (by omega : 1 < (2 : ℕ))]
  omega

theorem place_succ (i : ℕ) : place (i + 1) = place i + place i := by
  unfold place
  rw [show i + 1 + 1 = (i + 1) + 1 by omega, Nat.pow_add_one]
  omega

/-- The diagonal positions in a product are isolated: the sum of two sparse
places is the next place exactly when both inputs are the same place. -/
theorem add_places_eq_succ_place_iff {j k i : ℕ} :
    place j + place k = place (i + 1) ↔ j = i ∧ k = i := by
  constructor
  · intro h
    rcases lt_trichotomy j k with hjk | hjk | hkj
    · have hjpk : place j < place k := place_lt_place hjk
      have hlo0 : place k < place j + place k := by
        have : 0 < place j := by simp [place]
        omega
      have hlo : place k < place (i + 1) := by
        rw [← h]
        exact hlo0
      have hhi0 : place j + place k < place k + place k :=
        Nat.add_lt_add_right hjpk _
      have hhi : place (i + 1) < place (k + 1) := by
        rw [← h]
        rw [place_succ]
        exact hhi0
      have hlo' : k < i + 1 := place_lt_iff.mp hlo
      have hhi' : i + 1 < k + 1 := place_lt_iff.mp hhi
      omega
    · subst k
      have hs : place (j + 1) = place (i + 1) := by
        rw [place_succ]
        exact h
      have : j + 1 = i + 1 := place_injective hs
      omega
    · have hkpl : place k < place j := place_lt_place hkj
      have hlo0 : place j < place j + place k := by
        have : 0 < place k := by simp [place]
        omega
      have hlo : place j < place (i + 1) := by
        rw [← h]
        exact hlo0
      have hhi0 : place j + place k < place j + place j :=
        Nat.add_lt_add_left hkpl _
      have hhi : place (i + 1) < place (j + 1) := by
        rw [← h]
        rw [place_succ]
        exact hhi0
      have hlo' : j < i + 1 := place_lt_iff.mp hlo
      have hhi' : i + 1 < j + 1 := place_lt_iff.mp hhi
      omega
  · rintro ⟨hj, hk⟩
    subst j
    subst k
    exact (place_succ _).symm

/-! ## Binary blocks

The Rocq proof uses bitwise meet to select whole base-`2^(4q)` digit blocks.
The next Euclidean decomposition lemma is the basic semantic fact behind
that operation.  We prove it here from `Nat.bit` rather than assuming a
machine-word model of natural numbers.
-/

theorem testBit_add_mul_two_pow {w r d : ℕ} (hr : r < 2 ^ w) (j : ℕ) :
    (r + d * 2 ^ w).testBit j =
      if j < w then r.testBit j else d.testBit (j - w) := by
  induction w generalizing r d j with
  | zero =>
      have : r = 0 := by simpa using hr
      subst r
      simp
  | succ w ih =>
      have hn : r + d * 2 ^ (w + 1) =
          Nat.bit (Nat.bodd r) (r / 2 + d * 2 ^ w) := by
        rw [Nat.bit_val]
        have hsplit := Nat.bodd_add_div2 r
        dsimp only [Nat.div2] at hsplit
        symm
        calc
          2 * (r / 2 + d * 2 ^ w) + (Nat.bodd r).toNat =
              ((Nat.bodd r).toNat + 2 * (r / 2)) + d * (2 ^ w * 2) := by ring
          _ = r + d * 2 ^ (w + 1) := by rw [hsplit, Nat.pow_add_one]
      have hrdiv : r / 2 < 2 ^ w := by
        rw [Nat.pow_add_one] at hr
        omega
      rw [hn]
      cases j with
      | zero =>
          simp only [Nat.testBit_bit_zero]
          have hbodd : Nat.bodd r = r.testBit 0 := rfl
          rw [hbodd]
          simp
      | succ j =>
          rw [Nat.testBit_bit_succ, ih hrdiv]
          have hshift : (r / 2).testBit j = r.testBit (j + 1) := by
            simpa [Nat.shiftRight_eq_div_pow, Nat.add_comm] using
              (Nat.testBit_shiftRight (i := 1) (j := j) r)
          rw [hshift]
          by_cases hjw : j < w
          · simp [hjw]
          · have hsub : j + 1 - (w + 1) = j - w := by omega
            simp [hjw, hsub]

/-- Bitwise meet respects the low/high decomposition at a power of two.  This
is the Lean counterpart of Rocq's `nat_meet_euclid_power_2`. -/
theorem land_add_mul_two_pow {w r₁ d₁ r₂ d₂ : ℕ}
    (hr₁ : r₁ < 2 ^ w) (hr₂ : r₂ < 2 ^ w) :
    (r₁ + d₁ * 2 ^ w) &&& (r₂ + d₂ * 2 ^ w) =
      (r₁ &&& r₂) + (d₁ &&& d₂) * 2 ^ w := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_land, testBit_add_mul_two_pow hr₁,
    testBit_add_mul_two_pow hr₂]
  have handlt : r₁ &&& r₂ < 2 ^ w := Nat.and_le_left.trans_lt hr₁
  rw [testBit_add_mul_two_pow handlt]
  split <;> simp_all

/-- Blockwise meet of two equal-length base-`2^w` expansions. -/
theorem land_ofDigits_zipWith (w : ℕ) {xs ys : List ℕ}
    (hlen : xs.length = ys.length)
    (hxs : ∀ x ∈ xs, x < 2 ^ w)
    (hys : ∀ y ∈ ys, y < 2 ^ w) :
    Nat.ofDigits (2 ^ w) xs &&& Nat.ofDigits (2 ^ w) ys =
      Nat.ofDigits (2 ^ w) (xs.zipWith (· &&& ·) ys) := by
  induction xs generalizing ys with
  | nil =>
      simp only [List.length_nil] at hlen
      have : ys = [] := List.length_eq_zero_iff.mp hlen.symm
      subst ys
      simp
  | cons x xs ih =>
      rcases ys with _ | ⟨y, ys⟩
      · simp at hlen
      · simp only [List.length_cons] at hlen
        have hlen' : xs.length = ys.length := by omega
        simp only [Nat.ofDigits_cons, List.zipWith_cons_cons]
        rw [show 2 ^ w * Nat.ofDigits (2 ^ w) xs =
            Nat.ofDigits (2 ^ w) xs * 2 ^ w by ring]
        rw [show 2 ^ w * Nat.ofDigits (2 ^ w) ys =
            Nat.ofDigits (2 ^ w) ys * 2 ^ w by ring]
        rw [land_add_mul_two_pow (hxs x List.mem_cons_self)
          (hys y List.mem_cons_self)]
        rw [ih hlen'
          (fun z hz ↦ hxs z (List.mem_cons_of_mem x hz))
          (fun z hz ↦ hys z (List.mem_cons_of_mem y hz))]
        ring

theorem land_two_pow_sub_one_eq_self {w x : ℕ} (hx : x < 2 ^ w) :
    x &&& (2 ^ w - 1) = x := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_land, Nat.testBit_two_pow_sub_one]
  by_cases hj : j < w
  · simp [hj]
  · have hwj : w ≤ j := Nat.le_of_not_gt hj
    have hxj : x < 2 ^ j := hx.trans_le (Nat.pow_le_pow_right (by omega) hwj)
    rw [Nat.testBit_eq_false_of_lt hxj]
    simp [hj]

/-- The coefficient at an arbitrary dense position.  At most one sparse
index can contribute because `place` is injective. -/
noncomputable def denseCoeff (len : ℕ) (f : ℕ → ℕ) (j : ℕ) : ℕ :=
  if h : ∃ i, i < len ∧ place i = j then f (Nat.find h) else 0

theorem denseCoeff_at {len : ℕ} (f : ℕ → ℕ) {i : ℕ} (hi : i < len) :
    denseCoeff len f (place i) = f i := by
  unfold denseCoeff
  let h : ∃ j, j < len ∧ place j = place i := ⟨i, hi, rfl⟩
  rw [dif_pos h]
  have hs := (Nat.find_spec h).2
  exact congrArg f (place_injective hs)

theorem denseCoeff_eq_zero_or {len : ℕ} (f : ℕ → ℕ) (j : ℕ) :
    denseCoeff len f j = 0 ∨
      ∃ i, i < len ∧ place i = j ∧ denseCoeff len f j = f i := by
  unfold denseCoeff
  split
  · rename_i h
    right
    exact ⟨Nat.find h, (Nat.find_spec h).1, (Nat.find_spec h).2, rfl⟩
  · left
    rfl

/-- A dense list long enough to contain every occupied sparse position. -/
noncomputable def denseDigits (len : ℕ) (f : ℕ → ℕ) : List ℕ :=
  List.ofFn fun j : Fin (place len) ↦ denseCoeff len f j

@[simp] theorem denseDigits_length (len : ℕ) (f : ℕ → ℕ) :
    (denseDigits len f).length = place len := by
  simp [denseDigits]

theorem place_lt_length {len i : ℕ} (hi : i < len) :
    place i < (denseDigits len (fun _ ↦ 0)).length := by
  simp only [denseDigits_length]
  exact place_lt_place hi

theorem getElem_denseDigits {len : ℕ} (f : ℕ → ℕ) {i : ℕ} (hi : i < len) :
    (denseDigits len f)[place i]'(by simpa using place_lt_place hi) = f i := by
  simp [denseDigits, denseCoeff_at f hi]

theorem mem_denseDigits_lt {len q : ℕ} {f : ℕ → ℕ}
    (hf : ∀ i, i < len → f i < radix q) :
    ∀ d ∈ denseDigits len f, d < radix q := by
  intro d hd
  simp only [denseDigits, List.mem_ofFn] at hd
  rcases hd with ⟨j, rfl⟩
  rcases denseCoeff_eq_zero_or (len := len) f j with hzero | ⟨i, hi, _hplace, hvalue⟩
  · rw [hzero]
    exact Nat.two_pow_pos _
  · rw [hvalue]
    exact hf i hi

/- The following equality is the bridge between the arithmetic sparse sum
and the standard uniqueness theorem for ordinary base expansions. -/
theorem ofDigits_denseDigits (len q : ℕ) (f : ℕ → ℕ) :
    Nat.ofDigits (radix q) (denseDigits len f) = encode len q f := by
  rw [Nat.ofDigits_eq_sum_mapIdx]
  simp only [denseDigits, List.mapIdx_eq_ofFn, List.get_ofFn, List.length_ofFn,
    Fin.val_cast, List.sum_ofFn]
  unfold encode
  -- Both sides are finite sums over the same graph; the left sum additionally
  -- contains zeros at all unoccupied dense positions.
  classical
  let occupied : Finset (Fin (place len)) :=
    Finset.univ.filter fun j ↦ ∃ i, i < len ∧ place i = j
  have hrestrict :
      (∑ j ∈ occupied, denseCoeff len f j * radix q ^ (j : ℕ)) =
        ∑ j : Fin (place len), denseCoeff len f j * radix q ^ (j : ℕ) := by
    apply Finset.sum_subset
    · intro j hj
      simp
    · intro j _hjuniv hjnot
      have hnone : ¬ ∃ i, i < len ∧ place i = (j : ℕ) := by
        intro h
        exact hjnot (by simp [occupied, h])
      simp [denseCoeff, hnone]
  rw [← hrestrict]
  symm
  apply Finset.sum_bij (fun i hi ↦
      ⟨place i, place_lt_place (Finset.mem_range.mp hi)⟩)
  · intro i hi
    simp only [occupied, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨i, Finset.mem_range.mp hi, rfl⟩
  · intro i hi j hj heq
    exact place_injective (Fin.ext_iff.mp heq)
  · intro j hj
    simp only [occupied, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    rcases hj with ⟨i, hi, hplace⟩
    refine ⟨i, Finset.mem_range.mpr hi, ?_⟩
    exact Fin.ext hplace
  · intro i hi
    simp [denseCoeff_at f (Finset.mem_range.mp hi)]

/-! ## Uniqueness and pointwise addition -/

theorem radix_one_lt {q : ℕ} (hq : 0 < q) : 1 < radix q := by
  unfold radix
  apply Nat.one_lt_pow
  · omega
  · omega

theorem two_pow_lt_radix {q : ℕ} (hq : 0 < q) : 2 ^ q < radix q := by
  unfold radix
  apply Nat.pow_lt_pow_right (by omega)
  omega

/-- Base-expansion uniqueness in the exact form used below.  Notice that its
coefficient hypothesis is the generous `< radix q`, not the stricter
`< 2^q` invariant carried by `IsCipher`; this is what lets it also compare a
sum of two digit columns without assuming that the sum is itself a cipher. -/
theorem encode_injective_of_lt_radix {len q : ℕ} {f g : ℕ → ℕ}
    (hq : 0 < q)
    (hf : ∀ i, i < len → f i < radix q)
    (hg : ∀ i, i < len → g i < radix q)
    (hcode : encode len q f = encode len q g) :
    ∀ i, i < len → f i = g i := by
  have hdigits : denseDigits len f = denseDigits len g := by
    apply Nat.ofDigits_inj_of_len_eq (radix_one_lt hq)
    · simp
    · exact mem_denseDigits_lt hf
    · exact mem_denseDigits_lt hg
    · simpa only [ofDigits_denseDigits] using hcode
  intro i hi
  calc
    f i = (denseDigits len f)[place i]'(by simpa using place_lt_place hi) :=
      (getElem_denseDigits f hi).symm
    _ = (denseDigits len g)[place i]'(by simpa using place_lt_place hi) := by
      exact List.getElem_of_eq hdigits _
    _ = g i := getElem_denseDigits g hi

/-- A code determines every value in its represented prefix. -/
theorem isCipher_inj {len q c : ℕ} {f g : ℕ → ℕ}
    (hf : IsCipher len q f c) (hg : IsCipher len q g c) :
    ∀ i, i < len → f i = g i := by
  rcases hf with ⟨hlen, hf, hfc⟩
  rcases hg with ⟨_hlen, hg, hgc⟩
  apply encode_injective_of_lt_radix (q := q)
  · omega
  · intro i hi
    exact (hf i hi).trans (two_pow_lt_radix (by omega))
  · intro i hi
    exact (hg i hi).trans (two_pow_lt_radix (by omega))
  · rw [← hfc, ← hgc]

/-- Pointwise equality on the represented prefix is also sufficient for code
equality. -/
theorem isCipher_fun {len q cf cg : ℕ} {f g : ℕ → ℕ}
    (hfg : ∀ i, i < len → f i = g i)
    (hf : IsCipher len q f cf) (hg : IsCipher len q g cg) : cf = cg := by
  rcases hf with ⟨_hlen, _hfBound, rfl⟩
  rcases hg with ⟨_hlen', _hgBound, rfl⟩
  unfold encode
  apply Finset.sum_congr rfl
  intro i hi
  rw [hfg i (Finset.mem_range.mp hi)]

theorem isCipher_equiv {len q cf cg : ℕ} {f g : ℕ → ℕ}
    (hf : IsCipher len q f cf) (hg : IsCipher len q g cg) :
    cf = cg ↔ ∀ i, i < len → f i = g i := by
  constructor
  · rintro rfl
    exact isCipher_inj hf hg
  · intro h
    exact isCipher_fun h hf hg

theorem add_lt_radix_of_lt_two_pow {q x y : ℕ} (hq : 0 < q)
    (hx : x < 2 ^ q) (hy : y < 2 ^ q) : x + y < radix q := by
  have hsum : x + y < 2 ^ q + 2 ^ q := Nat.add_lt_add hx hy
  have hnext : 2 ^ q + 2 ^ q = 2 ^ (q + 1) := by
    rw [Nat.pow_add_one]
    omega
  rw [hnext] at hsum
  exact hsum.trans (by
    unfold radix
    apply Nat.pow_lt_pow_right (by omega)
    omega)

/-- Equality of three cipher integers is exactly pointwise addition.  The
reverse implication uses the large radix to rule out carries; it does not
silently assume that `b i + c i < 2^q`. -/
theorem add_spec {len q ca cb cc : ℕ} {a b c : ℕ → ℕ}
    (ha : IsCipher len q a ca)
    (hb : IsCipher len q b cb)
    (hc : IsCipher len q c cc) :
    ca = cb + cc ↔ ∀ i, i < len → a i = b i + c i := by
  rcases ha with ⟨hlen, haBound, rfl⟩
  rcases hb with ⟨_hlenb, hbBound, rfl⟩
  rcases hc with ⟨_hlenc, hcBound, rfl⟩
  constructor
  · intro hsum
    apply encode_injective_of_lt_radix (q := q) (f := a)
    · omega
    · intro i hi
      exact (haBound i hi).trans (two_pow_lt_radix (by omega))
    · intro i hi
      exact add_lt_radix_of_lt_two_pow (by omega) (hbBound i hi) (hcBound i hi)
    · rw [hsum]
      unfold encode
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
  · intro hpoint
    unfold encode
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hpoint i (Finset.mem_range.mp hi)]
    ring

/-! ## Elementary named columns -/

/-- Some bounded sequence is represented by `c`. -/
def Code (len q c : ℕ) : Prop :=
  ∃ f : ℕ → ℕ, IsCipher len q f c

/-- `c` represents the constant column with value `k`. -/
def ConstCode (len q k c : ℕ) : Prop :=
  IsCipher len q (fun _ ↦ k) c

/-- `c` represents the zero-based index column `0,1,...,len-1`. -/
def IndexCode (len q c : ℕ) : Prop :=
  IsCipher len q id c

theorem constCode_iff {len q k c : ℕ} :
    ConstCode len q k c ↔
      len + 1 < q ∧ c = k * encode len q (fun _ ↦ 1) ∧
        (len = 0 ∨ k < 2 ^ q) := by
  constructor
  · rintro ⟨hlen, hbound, rfl⟩
    refine ⟨hlen, ?_, ?_⟩
    · unfold encode
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    · by_cases hzero : len = 0
      · exact Or.inl hzero
      · exact Or.inr (hbound 0 (Nat.pos_of_ne_zero hzero))
  · rintro ⟨hlen, hcode, hbound⟩
    rw [hcode]
    refine ⟨hlen, ?_, ?_⟩
    · intro i hi
      rcases hbound with hzero | hk
      · omega
      · exact hk
    unfold encode
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    ring

theorem indexCode_iff {len q c : ℕ} :
    IndexCode len q c ↔
      len + 1 < q ∧ c = encode len q id := by
  constructor
  · rintro ⟨hlen, _hbound, hcode⟩
    exact ⟨hlen, hcode⟩
  · rintro ⟨hlen, rfl⟩
    refine ⟨hlen, ?_, rfl⟩
    intro i hi
    change i < 2 ^ q
    have hiq : i < q := by omega
    exact hiq.trans (Nat.lt_pow_self (n := q) (a := 2) (by omega))

/-! ## Semantic digit access and pointwise multiplication

The following projection is useful for stating an independently checkable
semantic multiplication operation.  It is *not* named `MulCodes`: a bounded
sum of projected digits is not yet the finite existential meet/mask
certificate required for Diophantine compilation.  Keeping the names apart
prevents that important distinction from being hidden by an attractive API.
-/

/-- Read the digit at the sparse place for index `i`. -/
def entry (q c i : ℕ) : ℕ :=
  c / radix q ^ place i % radix q

theorem entry_encode {len q : ℕ} {f : ℕ → ℕ}
    (hq : 0 < q) (hf : ∀ i, i < len → f i < radix q)
    {i : ℕ} (hi : i < len) :
    entry q (encode len q f) i = f i := by
  unfold entry
  rw [← ofDigits_denseDigits]
  rw [Nat.ofDigits_div_pow_eq_ofDigits_drop (place i)
    (Nat.zero_lt_of_lt (radix_one_lt hq)) (denseDigits len f)
    (mem_denseDigits_lt hf)]
  have hpos : place i < (denseDigits len f).length := by
    simpa using place_lt_place hi
  rw [List.drop_eq_getElem_cons hpos, Nat.ofDigits_mod_eq_head!]
  simp only [List.head!_cons]
  rw [getElem_denseDigits f hi, Nat.mod_eq_of_lt (hf i hi)]

theorem entry_isCipher {len q c : ℕ} {f : ℕ → ℕ}
    (hf : IsCipher len q f c) {i : ℕ} (hi : i < len) :
    entry q c i = f i := by
  rcases hf with ⟨hlen, hbound, rfl⟩
  apply entry_encode (by omega) _ hi
  intro j hj
  exact (hbound j hj).trans (two_pow_lt_radix (by omega))

/-! ### The product convolution

The ordered double sum below is the ordinary convolution of the two sparse
base expansions.  At a diagonal position `place (i+1)`, the powers-of-two
lemma `add_places_eq_succ_place_iff` reduces it to the single pair `(i,i)`.
-/

/-- Coefficient of `radix q ^ e` in the formal product of two sparse
encodings. -/
def productCoeff (len : ℕ) (a b : ℕ → ℕ) (e : ℕ) : ℕ :=
  ∑ j ∈ Finset.range len,
    ∑ k ∈ Finset.range len,
      if place j + place k = e then a j * b k else 0

theorem productCoeff_diagonal {len : ℕ} (a b : ℕ → ℕ) {i : ℕ} (hi : i < len) :
    productCoeff len a b (place (i + 1)) = a i * b i := by
  classical
  unfold productCoeff
  simp only [add_places_eq_succ_place_iff]
  have hinner (j : ℕ) :
      (∑ k ∈ Finset.range len,
        if j = i ∧ k = i then a j * b k else 0) =
        if j = i then a j * b i else 0 := by
    by_cases hj : j = i
    · subst j
      simp [hi]
    · simp [hj]
  simp_rw [hinner]
  simp [hi]

/-- The convolution is supported below twice the first unused sparse place. -/
def productDigits (len : ℕ) (a b : ℕ → ℕ) : List ℕ :=
  List.ofFn fun e : Fin (2 * place len) ↦ productCoeff len a b e

@[simp] theorem productDigits_length (len : ℕ) (a b : ℕ → ℕ) :
    (productDigits len a b).length = 2 * place len := by
  simp [productDigits]

theorem product_place_lt_length {len i : ℕ} (hi : i < len) :
    place (i + 1) < (productDigits len (fun _ ↦ 0) (fun _ ↦ 0)).length := by
  simp only [productDigits_length]
  rw [place_succ]
  have := place_lt_place hi
  omega

theorem getElem_productDigits_diagonal {len : ℕ} (a b : ℕ → ℕ)
    {i : ℕ} (hi : i < len) :
    (productDigits len a b)[place (i + 1)]'(by
      simpa only [productDigits_length] using product_place_lt_length hi) = a i * b i := by
  simp only [productDigits, List.getElem_ofFn]
  exact productCoeff_diagonal a b hi

/-- The coarse estimate used to rule out carries in the convolution.  It is
intentionally independent of the Sidon property: there are at most `len^2`
ordered pairs, and `len < q < 2^q`, so even that deliberately wasteful bound
fits below the radix `2^(4q)`. -/
theorem productCoeff_lt_radix {len q : ℕ} {a b : ℕ → ℕ}
    (hlen : len + 1 < q)
    (ha : ∀ i, i < len → a i < 2 ^ q)
    (hb : ∀ i, i < len → b i < 2 ^ q)
    (e : ℕ) : productCoeff len a b e < radix q := by
  let P := 2 ^ q
  have hterm (j : ℕ) (hj : j ∈ Finset.range len)
      (k : ℕ) (hk : k ∈ Finset.range len) :
      (if place j + place k = e then a j * b k else 0) ≤ P * P := by
    split
    · exact Nat.mul_le_mul
        (Nat.le_of_lt (ha j (Finset.mem_range.mp hj)))
        (Nat.le_of_lt (hb k (Finset.mem_range.mp hk)))
    · exact Nat.zero_le _
  have hinner (j : ℕ) (hj : j ∈ Finset.range len) :
      (∑ k ∈ Finset.range len,
        if place j + place k = e then a j * b k else 0) ≤ len * (P * P) := by
    calc
      _ ≤ (Finset.range len).card • (P * P) :=
        Finset.sum_le_card_nsmul _ _ _ (hterm j hj)
      _ = len * (P * P) := by simp
  have hsum : productCoeff len a b e ≤ len * (len * (P * P)) := by
    unfold productCoeff
    calc
      _ ≤ (Finset.range len).card • (len * (P * P)) :=
        Finset.sum_le_card_nsmul _ _ _ hinner
      _ = len * (len * (P * P)) := by simp
  have hlenP : len < P := by
    have hlq : len < q := by omega
    exact hlq.trans (Nat.lt_pow_self (n := q) (a := 2) (by omega))
  have hsq : len * len < P * P := by
    cases len with
    | zero => simp [P]
    | succ len =>
        exact mul_lt_mul hlenP (Nat.le_of_lt hlenP)
          (Nat.succ_pos len) (Nat.zero_le _)
  have hPP : 0 < P * P := Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)
  calc
    productCoeff len a b e ≤ len * (len * (P * P)) := hsum
    _ = (len * len) * (P * P) := by ring
    _ < (P * P) * (P * P) := Nat.mul_lt_mul_of_pos_right hsq hPP
    _ = radix q := by
      simp only [P, radix, ← Nat.pow_add]
      congr 1
      omega

theorem mem_productDigits_lt_radix {len q : ℕ} {a b : ℕ → ℕ}
    (hlen : len + 1 < q)
    (ha : ∀ i, i < len → a i < 2 ^ q)
    (hb : ∀ i, i < len → b i < 2 ^ q) :
    ∀ d ∈ productDigits len a b, d < radix q := by
  intro d hd
  simp only [productDigits, List.mem_ofFn] at hd
  rcases hd with ⟨e, rfl⟩
  exact productCoeff_lt_radix hlen ha hb e

/-- The dense convolution represents the ordinary product of the two sparse
codes. -/
theorem ofDigits_productDigits (len q : ℕ) (a b : ℕ → ℕ) :
    Nat.ofDigits (radix q) (productDigits len a b) =
      encode len q a * encode len q b := by
  rw [Nat.ofDigits_eq_sum_mapIdx]
  simp only [productDigits, List.mapIdx_eq_ofFn, List.get_ofFn, List.length_ofFn,
    Fin.val_cast, List.sum_ofFn]
  unfold encode productCoeff
  classical
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  simp_rw [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  have hjlt : j < len := Finset.mem_range.mp hj
  have hklt : k < len := Finset.mem_range.mp hk
  have hexp : place j + place k < 2 * place len := by
    have hjp := place_lt_place hjlt
    have hkp := place_lt_place hklt
    omega
  let e0 : Fin (2 * place len) := ⟨place j + place k, hexp⟩
  calc
    (∑ e : Fin (2 * place len),
        if place j + place k = (e : ℕ) then
          a j * b k * radix q ^ (e : ℕ) else 0) =
        a j * b k * radix q ^ (place j + place k) := by
      simpa only [e0, Fin.ext_iff] using
        (Fintype.sum_ite_eq e0
          (fun e : Fin (2 * place len) ↦ a j * b k * radix q ^ (e : ℕ)))
    _ = a j * radix q ^ place j * (b k * radix q ^ place k) := by
      rw [Nat.pow_add]
      ring

/-- Reading the next sparse position from the product returns exactly the
pointwise product.  This is the central semantic invariant behind the Rocq
meet/mask certificate. -/
theorem entry_mul_encode_succ {len q : ℕ} {a b : ℕ → ℕ}
    (hlen : len + 1 < q)
    (ha : ∀ i, i < len → a i < 2 ^ q)
    (hb : ∀ i, i < len → b i < 2 ^ q)
    {i : ℕ} (hi : i < len) :
    entry q (encode len q a * encode len q b) (i + 1) = a i * b i := by
  unfold entry
  rw [← ofDigits_productDigits]
  rw [Nat.ofDigits_div_pow_eq_ofDigits_drop (place (i + 1))
    (Nat.zero_lt_of_lt (radix_one_lt (by omega))) (productDigits len a b)
    (mem_productDigits_lt_radix hlen ha hb)]
  have hpos : place (i + 1) < (productDigits len a b).length := by
    simpa only [productDigits_length] using product_place_lt_length hi
  rw [List.drop_eq_getElem_cons hpos, Nat.ofDigits_mod_eq_head!]
  simp only [List.head!_cons]
  rw [getElem_productDigits_diagonal a b hi]
  apply Nat.mod_eq_of_lt
  simpa only [productCoeff_diagonal a b hi] using
    productCoeff_lt_radix hlen ha hb (place (i + 1))

theorem entry_mul_ciphers_succ {len q ca cb : ℕ} {a b : ℕ → ℕ}
    (ha : IsCipher len q a ca) (hb : IsCipher len q b cb)
    {i : ℕ} (hi : i < len) :
    entry q (ca * cb) (i + 1) = a i * b i := by
  rcases ha with ⟨hlen, haBound, rfl⟩
  rcases hb with ⟨_hlen, hbBound, rfl⟩
  exact entry_mul_encode_succ hlen haBound hbBound hi

/-! ### Shifted diagonal columns and masks -/

/-- The same sparse encoding shifted to the next occupied places. -/
def shiftedEncode (len q : ℕ) (f : ℕ → ℕ) : ℕ :=
  ∑ i ∈ Finset.range len, f i * radix q ^ place (i + 1)

noncomputable def shiftedCoeff (len : ℕ) (f : ℕ → ℕ) (e : ℕ) : ℕ :=
  if h : ∃ i, i < len ∧ place (i + 1) = e then f (Nat.find h) else 0

theorem shiftedCoeff_at {len : ℕ} (f : ℕ → ℕ) {i : ℕ} (hi : i < len) :
    shiftedCoeff len f (place (i + 1)) = f i := by
  unfold shiftedCoeff
  let h : ∃ j, j < len ∧ place (j + 1) = place (i + 1) := ⟨i, hi, rfl⟩
  rw [dif_pos h]
  have hs := (Nat.find_spec h).2
  have : Nat.find h + 1 = i + 1 := place_injective hs
  exact congrArg f (by omega)

theorem shiftedCoeff_eq_zero_or {len : ℕ} (f : ℕ → ℕ) (e : ℕ) :
    shiftedCoeff len f e = 0 ∨
      ∃ i, i < len ∧ place (i + 1) = e ∧ shiftedCoeff len f e = f i := by
  unfold shiftedCoeff
  split
  · rename_i h
    right
    exact ⟨Nat.find h, (Nat.find_spec h).1, (Nat.find_spec h).2, rfl⟩
  · left
    rfl

noncomputable def shiftedDigits (len : ℕ) (f : ℕ → ℕ) : List ℕ :=
  List.ofFn fun e : Fin (2 * place len) ↦ shiftedCoeff len f e

@[simp] theorem shiftedDigits_length (len : ℕ) (f : ℕ → ℕ) :
    (shiftedDigits len f).length = 2 * place len := by
  simp [shiftedDigits]

theorem mem_shiftedDigits_lt {len bound : ℕ} {f : ℕ → ℕ}
    (hf : ∀ i, i < len → f i < bound) (hbound : 0 < bound) :
    ∀ d ∈ shiftedDigits len f, d < bound := by
  intro d hd
  simp only [shiftedDigits, List.mem_ofFn] at hd
  rcases hd with ⟨e, rfl⟩
  rcases shiftedCoeff_eq_zero_or (len := len) f e with
    hzero | ⟨i, hi, _hplace, hvalue⟩
  · rw [hzero]
    exact hbound
  · rw [hvalue]
    exact hf i hi

theorem ofDigits_shiftedDigits (len q : ℕ) (f : ℕ → ℕ) :
    Nat.ofDigits (radix q) (shiftedDigits len f) = shiftedEncode len q f := by
  rw [Nat.ofDigits_eq_sum_mapIdx]
  simp only [shiftedDigits, List.mapIdx_eq_ofFn, List.get_ofFn, List.length_ofFn,
    Fin.val_cast, List.sum_ofFn]
  unfold shiftedEncode
  classical
  let occupied : Finset (Fin (2 * place len)) :=
    Finset.univ.filter fun e ↦ ∃ i, i < len ∧ place (i + 1) = e
  have hrestrict :
      (∑ e ∈ occupied, shiftedCoeff len f e * radix q ^ (e : ℕ)) =
        ∑ e : Fin (2 * place len), shiftedCoeff len f e * radix q ^ (e : ℕ) := by
    apply Finset.sum_subset
    · intro e he
      simp
    · intro e _heuniv henot
      have hnone : ¬ ∃ i, i < len ∧ place (i + 1) = (e : ℕ) := by
        intro h
        exact henot (by simp [occupied, h])
      simp [shiftedCoeff, hnone]
  rw [← hrestrict]
  symm
  apply Finset.sum_bij (fun i hi ↦
      ⟨place (i + 1), by
        rw [place_succ]
        have := place_lt_place (Finset.mem_range.mp hi)
        omega⟩)
  · intro i hi
    simp only [occupied, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨i, Finset.mem_range.mp hi, rfl⟩
  · intro i hi j hj heq
    have hs : i + 1 = j + 1 := place_injective (Fin.ext_iff.mp heq)
    omega
  · intro e he
    simp only [occupied, Finset.mem_filter, Finset.mem_univ, true_and] at he
    rcases he with ⟨i, hi, hplace⟩
    refine ⟨i, Finset.mem_range.mpr hi, ?_⟩
    exact Fin.ext hplace
  · intro i hi
    simp [shiftedCoeff_at f (Finset.mem_range.mp hi)]

/-- Arithmetic mask having one full `radix`-sized binary block at every
shifted diagonal place. -/
def diagonalMask (len q : ℕ) : ℕ :=
  shiftedEncode len q (fun _ ↦ radix q - 1)

theorem diagonalMask_eq (len q : ℕ) :
    diagonalMask len q =
      (radix q - 1) * shiftedEncode len q (fun _ ↦ 1) := by
  unfold diagonalMask shiftedEncode
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

theorem productCoeff_land_shiftedMask {len q : ℕ} {a b : ℕ → ℕ}
    (hlen : len + 1 < q)
    (ha : ∀ i, i < len → a i < 2 ^ q)
    (hb : ∀ i, i < len → b i < 2 ^ q)
    (e : ℕ) :
    productCoeff len a b e &&& shiftedCoeff len (fun _ ↦ radix q - 1) e =
      shiftedCoeff len (fun i ↦ a i * b i) e := by
  classical
  by_cases h : ∃ i, i < len ∧ place (i + 1) = e
  · unfold shiftedCoeff
    rw [dif_pos h, dif_pos h]
    let i := Nat.find h
    have hi : i < len := (Nat.find_spec h).1
    have he : place (i + 1) = e := (Nat.find_spec h).2
    change productCoeff len a b e &&& (radix q - 1) = a i * b i
    have hprod : productCoeff len a b e = a i * b i := by
      calc
        productCoeff len a b e = productCoeff len a b (place (i + 1)) :=
          congrArg (productCoeff len a b) he.symm
        _ = a i * b i := productCoeff_diagonal a b hi
    rw [hprod]
    apply land_two_pow_sub_one_eq_self
    have hlt := productCoeff_lt_radix hlen ha hb e
    rw [hprod] at hlt
    simpa only [radix] using hlt
  · simp [shiftedCoeff, h]

theorem zipWith_productDigits_mask {len q : ℕ} {a b : ℕ → ℕ}
    (hlen : len + 1 < q)
    (ha : ∀ i, i < len → a i < 2 ^ q)
    (hb : ∀ i, i < len → b i < 2 ^ q) :
    (productDigits len a b).zipWith (· &&& ·)
        (shiftedDigits len fun _ ↦ radix q - 1) =
      shiftedDigits len (fun i ↦ a i * b i) := by
  apply List.ext_getElem
  · simp
  · intro e he₁ he₂
    rw [List.getElem_zipWith]
    simp only [productDigits, shiftedDigits, List.getElem_ofFn]
    exact productCoeff_land_shiftedMask hlen ha hb e

/-- Multiplying two ciphers and meeting with the diagonal block mask extracts
exactly the shifted pointwise products. -/
theorem land_product_diagonalMask {len q : ℕ} {a b : ℕ → ℕ}
    (hlen : len + 1 < q)
    (ha : ∀ i, i < len → a i < 2 ^ q)
    (hb : ∀ i, i < len → b i < 2 ^ q) :
    (encode len q a * encode len q b) &&& diagonalMask len q =
      shiftedEncode len q (fun i ↦ a i * b i) := by
  rw [← ofDigits_productDigits]
  unfold diagonalMask
  rw [← ofDigits_shiftedDigits]
  have hmask : ∀ d ∈ shiftedDigits len (fun _ ↦ radix q - 1),
      d < radix q := by
    apply mem_shiftedDigits_lt
    · intro _i _hi
      exact Nat.sub_lt (Nat.two_pow_pos _) (by omega)
    · exact Nat.two_pow_pos _
  have hland := land_ofDigits_zipWith (4 * q)
    (xs := productDigits len a b)
    (ys := shiftedDigits len fun _ ↦ radix q - 1)
    (by simp)
    (by simpa only [radix] using mem_productDigits_lt_radix hlen ha hb)
    (by simpa only [radix] using hmask)
  change Nat.ofDigits (2 ^ (4 * q)) (productDigits len a b) &&&
      Nat.ofDigits (2 ^ (4 * q)) (shiftedDigits len fun _ ↦ radix q - 1) =
    shiftedEncode len q (fun i ↦ a i * b i)
  rw [hland, zipWith_productDigits_mask hlen ha hb]
  simpa only [radix] using
    ofDigits_shiftedDigits len q (fun i ↦ a i * b i)

/-- Re-encode the pointwise products of the digits read from two integers. -/
def productProjection (len q ca cb : ℕ) : ℕ :=
  encode len q fun i ↦ entry q ca i * entry q cb i

/-- Semantic, executable pointwise multiplication.  This relation is useful
for validating the mask construction but deliberately makes no claim of
being Diophantine by elementary closure alone. -/
def PointwiseMul (len q ca cb cc : ℕ) : Prop :=
  cc = productProjection len q ca cb

theorem mul_lt_radix_of_lt_two_pow {q x y : ℕ} (hq : 0 < q)
    (hx : x < 2 ^ q) (hy : y < 2 ^ q) : x * y < radix q := by
  have hmul : x * y < 2 ^ q * 2 ^ q := by
    cases y with
    | zero => simp
    | succ y =>
        exact mul_lt_mul hx (Nat.le_of_lt hy) (Nat.succ_pos y) (Nat.zero_le _)
  rw [← Nat.pow_add] at hmul
  exact hmul.trans (by
    unfold radix
    apply Nat.pow_lt_pow_right (by omega)
    omega)

/-- The executable projection has exactly the intended pointwise meaning on
well-formed ciphers. -/
theorem pointwiseMul_spec {len q ca cb cc : ℕ} {a b c : ℕ → ℕ}
    (ha : IsCipher len q a ca)
    (hb : IsCipher len q b cb)
    (hc : IsCipher len q c cc) :
    PointwiseMul len q ca cb cc ↔
      ∀ i, i < len → c i = a i * b i := by
  rcases ha with ⟨hlen, haBound, haCode⟩
  rcases hb with ⟨_hlenb, hbBound, hbCode⟩
  rcases hc with ⟨_hlenc, hcBound, hcCode⟩
  have haEntry : ∀ i, i < len → entry q ca i = a i := by
    intro i hi
    exact entry_isCipher ⟨hlen, haBound, haCode⟩ hi
  have hbEntry : ∀ i, i < len → entry q cb i = b i := by
    intro i hi
    exact entry_isCipher ⟨hlen, hbBound, hbCode⟩ hi
  constructor
  · intro hmul
    apply encode_injective_of_lt_radix (q := q) (f := c)
    · omega
    · intro i hi
      exact (hcBound i hi).trans (two_pow_lt_radix (by omega))
    · intro i hi
      exact mul_lt_radix_of_lt_two_pow (by omega) (haBound i hi) (hbBound i hi)
    · rw [← hcCode]
      unfold PointwiseMul productProjection at hmul
      calc
        cc = encode len q (fun i ↦ entry q ca i * entry q cb i) := hmul
        _ = encode len q (fun i ↦ a i * b i) := by
          unfold encode
          apply Finset.sum_congr rfl
          intro i hi
          have hil : i < len := Finset.mem_range.mp hi
          change (entry q ca i * entry q cb i) * radix q ^ place i =
            (a i * b i) * radix q ^ place i
          rw [haEntry i hil, hbEntry i hil]
  · intro hpoint
    unfold PointwiseMul productProjection
    rw [hcCode]
    apply Finset.sum_congr rfl
    intro i hi
    have hil : i < len := Finset.mem_range.mp hi
    change c i * radix q ^ place i =
      (entry q ca i * entry q cb i) * radix q ^ place i
    rw [haEntry i hil, hbEntry i hil, hpoint i hil]

/-! ## Rocq-style arithmetic multiplication certificate -/

theorem getElem_shiftedDigits {len : ℕ} (f : ℕ → ℕ)
    {i : ℕ} (hi : i < len) :
    (shiftedDigits len f)[place (i + 1)]'(by
      simp only [shiftedDigits_length]
      rw [place_succ]
      have := place_lt_place hi
      omega) = f i := by
  simp only [shiftedDigits, List.getElem_ofFn]
  exact shiftedCoeff_at f hi

theorem shiftedEncode_injective_of_lt_radix {len q : ℕ} {f g : ℕ → ℕ}
    (hq : 0 < q)
    (hf : ∀ i, i < len → f i < radix q)
    (hg : ∀ i, i < len → g i < radix q)
    (hcode : shiftedEncode len q f = shiftedEncode len q g) :
    ∀ i, i < len → f i = g i := by
  have hdigits : shiftedDigits len f = shiftedDigits len g := by
    apply Nat.ofDigits_inj_of_len_eq (radix_one_lt hq)
    · simp
    · exact mem_shiftedDigits_lt hf (Nat.two_pow_pos _)
    · exact mem_shiftedDigits_lt hg (Nat.two_pow_pos _)
    · simpa only [ofDigits_shiftedDigits] using hcode
  intro i hi
  calc
    f i = (shiftedDigits len f)[place (i + 1)]'(by
      simp only [shiftedDigits_length]
      rw [place_succ]
      have := place_lt_place hi
      omega) := (getElem_shiftedDigits f hi).symm
    _ = (shiftedDigits len g)[place (i + 1)]'(by
      simp only [shiftedDigits_length]
      rw [place_succ]
      have := place_lt_place hi
      omega) := by exact List.getElem_of_eq hdigits _
    _ = g i := getElem_shiftedDigits g hi

/-- The two canonical one-columns used by the meet certificate.  `ones` is
at the original sparse positions and `shifted` at the diagonal positions of
a product. -/
def OnesCodes (len q ones shifted : ℕ) : Prop :=
  len + 1 < q ∧
    ones = encode len q (fun _ ↦ 1) ∧
    shifted = shiftedEncode len q (fun _ ↦ 1)

theorem exists_onesCodes {len q : ℕ} (hlen : len + 1 < q) :
    ∃ ones shifted, OnesCodes len q ones shifted :=
  ⟨encode len q (fun _ ↦ 1), shiftedEncode len q (fun _ ↦ 1), hlen, rfl, rfl⟩

/-- Finite existential multiplication certificate, following `Code_mult` in
the vendored Rocq source.  The witness `predRadix` is `radix q - 1`; its
product with the shifted one-column is the binary block mask.  Both candidate
columns are met with that same mask and compared through the witness `p`.

There is no bounded pointwise quantifier in this definition. -/
def MulCodes (len q ca cb cc : ℕ) : Prop :=
  len = 0 ∨
    len ≠ 0 ∧
      ∃ ones shifted predRadix actualRadix p : ℕ,
        actualRadix = radix q ∧
        actualRadix = predRadix + 1 ∧
        OnesCodes len q ones shifted ∧
        p = (ca * ones) &&& (predRadix * shifted) ∧
        p = (cb * cc) &&& (predRadix * shifted)

/-- The finite meet/mask certificate is equivalent to pointwise
multiplication of three well-formed cipher columns. -/
theorem mul_spec {len q ca cb cc : ℕ} {a b c : ℕ → ℕ}
    (ha : IsCipher len q a ca)
    (hb : IsCipher len q b cb)
    (hc : IsCipher len q c cc) :
    MulCodes len q ca cb cc ↔
      ∀ i, i < len → a i = b i * c i := by
  rcases ha with ⟨hlen, haBound, haCode⟩
  rcases hb with ⟨_hlenb, hbBound, hbCode⟩
  rcases hc with ⟨_hlenc, hcBound, hcCode⟩
  have hone : ∀ i, i < len → (1 : ℕ) < 2 ^ q := by
    intro _i _hi
    exact Nat.one_lt_pow (by omega) (by omega)
  have hradixSucc : radix q = (radix q - 1) + 1 := by
    exact (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt (Nat.two_pow_pos _)))).symm
  constructor
  · intro hmul
    rcases hmul with hzero |
      ⟨_hlenzero, ones, shifted, predRadix, actualRadix, p,
        hactual, hpred, hones, hpA, hpBC⟩
    · intro i hi
      omega
    · rcases hones with ⟨_hlenOnes, hones, hshifted⟩
      have hpredValue : predRadix = radix q - 1 := by omega
      have hmeet :
          (ca * encode len q (fun _ ↦ 1)) &&& diagonalMask len q =
            (cb * cc) &&& diagonalMask len q := by
        have hpEq :
            (ca * ones) &&& (predRadix * shifted) =
              (cb * cc) &&& (predRadix * shifted) := hpA.symm.trans hpBC
        simpa only [hones, hshifted, hpredValue, diagonalMask_eq] using hpEq
      have hshiftEq : shiftedEncode len q a =
          shiftedEncode len q (fun i ↦ b i * c i) := by
        rw [haCode, hbCode, hcCode] at hmeet
        rw [land_product_diagonalMask hlen haBound hone,
          land_product_diagonalMask hlen hbBound hcBound] at hmeet
        simpa using hmeet
      apply shiftedEncode_injective_of_lt_radix (q := q)
      · omega
      · intro i hi
        exact (haBound i hi).trans (two_pow_lt_radix (by omega))
      · intro i hi
        exact mul_lt_radix_of_lt_two_pow (by omega) (hbBound i hi) (hcBound i hi)
      · exact hshiftEq
  · intro hpoint
    by_cases hzero : len = 0
    · exact Or.inl hzero
    · right
      refine ⟨hzero, encode len q (fun _ ↦ 1),
        shiftedEncode len q (fun _ ↦ 1), radix q - 1, radix q,
        (ca * encode len q (fun _ ↦ 1)) &&& diagonalMask len q,
        rfl, hradixSucc, ?_, ?_, ?_⟩
      · exact ⟨hlen, rfl, rfl⟩
      · rw [diagonalMask_eq]
      · rw [← diagonalMask_eq]
        have hleft :
            (ca * encode len q (fun _ ↦ 1)) &&& diagonalMask len q =
              shiftedEncode len q a := by
          rw [haCode]
          simpa using land_product_diagonalMask hlen haBound hone
        have hright :
            (cb * cc) &&& diagonalMask len q =
              shiftedEncode len q (fun i ↦ b i * c i) := by
          rw [hbCode, hcCode]
          exact land_product_diagonalMask hlen hbBound hcBound
        rw [hleft, hright]
        unfold shiftedEncode
        apply Finset.sum_congr rfl
        intro i hi
        rw [hpoint i (Finset.mem_range.mp hi)]

end SparseCipher

end PAListCoding
