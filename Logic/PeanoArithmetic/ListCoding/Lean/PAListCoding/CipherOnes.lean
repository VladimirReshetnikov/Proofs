import PAListCoding.BinaryDioph
import PAListCoding.SparseCipher

/-!
# A finite arithmetic certificate for the sparse one-columns

This file is the Lean counterpart of `seqs_of_ones_dio` in the vendored
Rocq development `H10/Matija/cipher.v`.  We use a slightly strengthened
certificate.  Rocq recovers the fact that `ones` has only the low bit in
each radix block from the two-way split of `ones ^ 2`; here that fact and
the two harmless size bounds are recorded explicitly.  They are elementary
Diophantine clauses and make the semantic inverse substantially more
transparent: after expanding in base `radix q`, the certificate says that
the support `A` satisfies

```
  {2} ∪ {2*a | a ∈ A} = A ∪ {2^(len+1)}.
```

The divisibility boundary removes positions below four, so this finite
recurrence has the unique solution `A = {2,4,...,2^len}`.
-/

namespace PAListCoding
namespace CipherOnes

open Fin2 SparseCipher
open scoped BigOperators Dioph

/-! ## The arithmetic certificate -/

/-- A universal-free arithmetic certificate for the two sparse columns of
ones.  The sole witness `mask` is the dense base-`radix q` number whose
digits from zero through `place len` are all one. -/
def OnesCertificate (len q ones shifted : Nat) : Prop :=
  (len = 0 ∧ ones = 0 ∧ shifted = 0 ∧ 2 ≤ q) ∨
  (0 < len ∧ len + 1 < q ∧ ∃ mask : Nat,
    1 + (radix q - 1) * mask = radix q * radix q ^ place len ∧
    ones &&& mask = ones ∧
    ones < radix q ^ place len ∧
    shifted = (ones * ones) &&& mask ∧
    radix q ^ 2 + shifted = ones + radix q ^ place len ∧
    radix q ^ 4 ∣ shifted)

/-! ## Fixed-length base expansions -/

/-- The dense all-one mask in base `r`. -/
def denseMask (r length : Nat) : Nat :=
  Nat.ofDigits r (List.replicate length 1)

@[simp] theorem denseMask_zero (r : Nat) : denseMask r 0 = 0 := by
  simp [denseMask]

theorem denseMask_succ (r length : Nat) :
    denseMask r (length + 1) = 1 + r * denseMask r length := by
  simp [denseMask, List.replicate_succ, Nat.ofDigits]

/-- The geometric-series identity in the orientation used by the
certificate. -/
theorem denseMask_geometric {r length : Nat} (hr : 0 < r) :
    1 + (r - 1) * denseMask r length = r ^ length := by
  induction length with
  | zero => simp [denseMask]
  | succ length ih =>
      rw [show length + 1 = length.succ by rfl, denseMask_succ]
      rw [Nat.mul_add]
      have hr1 : r - 1 + 1 = r := by omega
      rw [Nat.pow_succ]
      nlinarith

/-- The geometric equation determines the all-one mask uniquely. -/
theorem eq_denseMask_of_geometric {r length mask : Nat} (hr : 1 < r)
    (hmask : 1 + (r - 1) * mask = r ^ length) :
    mask = denseMask r length := by
  have hcanonical := denseMask_geometric (length := length) (Nat.zero_lt_of_lt hr)
  have hmul : (r - 1) * mask = (r - 1) * denseMask r length := by omega
  exact Nat.eq_of_mul_eq_mul_left (by omega) hmul

/-- Meeting with the dense one-mask forces every base-`2^width` digit to be
zero or one.  Fixed-length digits avoid all trailing-zero edge cases. -/
theorem digitsAppend_le_one_of_land_denseMask
    {width length n : Nat} (hwidth : 0 < width)
    (hn : n < (2 ^ width) ^ length)
    (hland : n &&& denseMask (2 ^ width) length = n) :
    ∀ d ∈ Nat.digitsAppend (2 ^ width) length n, d ≤ 1 := by
  let ds := Nat.digitsAppend (2 ^ width) length n
  let os := List.replicate length 1
  have hbase : 1 < 2 ^ width := Nat.one_lt_two_pow (Nat.ne_of_gt hwidth)
  have hlenDs : ds.length = length := Nat.length_digitsAppend hbase length hn
  have hlenOs : os.length = length := by simp [os]
  have hdsBound : ∀ d ∈ ds, d < 2 ^ width := by
    intro d hd
    exact Nat.lt_of_mem_digitsAppend hbase length d hd
  have hosBound : ∀ d ∈ os, d < 2 ^ width := by
    intro d hd
    simp only [os, List.mem_replicate] at hd
    rcases hd with ⟨_hlength, rfl⟩
    exact hbase
  have hnDigits : Nat.ofDigits (2 ^ width) ds = n := by
    simp only [ds, Nat.digitsAppend, Nat.ofDigits_append_replicate_zero,
      Nat.ofDigits_digits]
  have hmaskDigits : Nat.ofDigits (2 ^ width) os =
      denseMask (2 ^ width) length := rfl
  have hmeet := SparseCipher.land_ofDigits_zipWith width
    (xs := ds) (ys := os) (hlenDs.trans hlenOs.symm) hdsBound hosBound
  have hofDigits : Nat.ofDigits (2 ^ width)
      (ds.zipWith (· &&& ·) os) = Nat.ofDigits (2 ^ width) ds := by
    rw [← hmeet, hnDigits, hmaskDigits, hland]
  have hzipBound : ∀ d ∈ ds.zipWith (· &&& ·) os, d < 2 ^ width := by
    intro d hd
    rcases List.mem_iff_getElem.mp hd with ⟨i, hi, rfl⟩
    have hiDs : i < ds.length := by
      rw [List.length_zipWith] at hi
      omega
    rw [List.getElem_zipWith]
    exact (Nat.and_le_left).trans_lt
      (hdsBound ds[i] (List.getElem_mem hiDs))
  have hlist : ds.zipWith (· &&& ·) os = ds := by
    apply Nat.ofDigits_inj_of_len_eq hbase
    · simp [List.length_zipWith, hlenDs, hlenOs]
    · exact hzipBound
    · exact hdsBound
    · exact hofDigits
  intro d hd
  change d ∈ ds at hd
  rcases List.mem_iff_getElem.mp hd with ⟨i, hi, rfl⟩
  have hilength : i < length := by
    rw [← hlenDs]
    exact hi
  have hizip : i < (ds.zipWith (· &&& ·) os).length := by
    rw [List.length_zipWith, hlenDs, hlenOs]
    simpa using hilength
  have hget := List.getElem_of_eq hlist hizip
  have hos : os[i]'(by
      rw [hlenOs]
      exact hilength) = 1 := by
    simp [os]
  rw [List.getElem_zipWith, hos] at hget
  have hle : ds[i] &&& 1 ≤ 1 := Nat.and_le_right
  omega

/-! ## Dense square convolution

The next definitions are proof-local mathematics, not part of the
Diophantine certificate.  They let us reason about the square of an
arbitrary fixed-length radix expansion without appealing to machine-word
arithmetic. -/

def denseEncode (r length : Nat) (digit : Nat → Nat) : Nat :=
  ∑ i ∈ Finset.range length, digit i * r ^ i

def squareCoeff (length : Nat) (digit : Nat → Nat) (e : Nat) : Nat :=
  ∑ i ∈ Finset.range length, ∑ j ∈ Finset.range length,
    if i + j = e then digit i * digit j else 0

def squareDigits (length : Nat) (digit : Nat → Nat) : List Nat :=
  List.ofFn fun e : Fin (2 * length) ↦ squareCoeff length digit e

theorem ofDigits_ofFn_eq_denseEncode (r length : Nat)
    (digit : Nat → Nat) :
    Nat.ofDigits r (List.ofFn fun i : Fin length ↦ digit i) =
      denseEncode r length digit := by
  rw [Nat.ofDigits_eq_sum_mapIdx]
  simp only [List.mapIdx_eq_ofFn, List.get_ofFn, List.length_ofFn,
    Fin.val_cast, List.sum_ofFn, denseEncode]
  exact (Finset.sum_range (n := length) (fun i ↦ digit i * r ^ i)).symm

/-- Dense convolution reconstructs the ordinary square. -/
theorem ofDigits_squareDigits (r length : Nat) (digit : Nat → Nat) :
    Nat.ofDigits r (squareDigits length digit) =
      denseEncode r length digit * denseEncode r length digit := by
  rw [Nat.ofDigits_eq_sum_mapIdx]
  simp only [squareDigits, List.mapIdx_eq_ofFn, List.get_ofFn,
    List.length_ofFn, Fin.val_cast, List.sum_ofFn]
  unfold denseEncode squareCoeff
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  simp_rw [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  have hexp : i + j < 2 * length := by
    have := Finset.mem_range.mp hi
    have := Finset.mem_range.mp hj
    omega
  let e0 : Fin (2 * length) := ⟨i + j, hexp⟩
  calc
    (∑ e : Fin (2 * length),
        if i + j = (e : Nat) then
          digit i * digit j * r ^ (e : Nat) else 0) =
        digit i * digit j * r ^ (i + j) := by
      simpa only [e0, Fin.ext_iff] using
        (Fintype.sum_ite_eq e0
          (fun e : Fin (2 * length) ↦
            digit i * digit j * r ^ (e : Nat)))
    _ = digit i * r ^ i * (digit j * r ^ j) := by
      rw [Nat.pow_add]
      ring

theorem squareCoeff_le_sq_length {length : Nat} {digit : Nat → Nat}
    (hdigit : ∀ i, i < length → digit i ≤ 1) (e : Nat) :
    squareCoeff length digit e ≤ length * length := by
  unfold squareCoeff
  calc
    (∑ i ∈ Finset.range length, ∑ j ∈ Finset.range length,
        if i + j = e then digit i * digit j else 0) ≤
        ∑ _i ∈ Finset.range length, ∑ _j ∈ Finset.range length, 1 := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      split
      · exact Nat.mul_le_mul (hdigit i (Finset.mem_range.mp hi))
          (hdigit j (Finset.mem_range.mp hj))
      · simp
    _ = length * length := by simp

/-- The cipher spacing makes even the deliberately coarse convolution bound
strictly smaller than one radix block. -/
theorem sq_place_succ_lt_radix {len q : Nat} (hlen : len + 1 < q) :
    (place len + 1) * (place len + 1) < radix q := by
  have hplace : 0 < place len := by simp [place]
  have hdouble : place len + 1 ≤ 2 * place len := by omega
  have hsquare :
      (place len + 1) * (place len + 1) ≤
        (2 * place len) * (2 * place len) :=
    Nat.mul_le_mul hdouble hdouble
  have hpow : (2 * place len) * (2 * place len) < radix q := by
    have htwo : 2 * place len = 2 ^ (len + 2) := by
      simp [place, Nat.pow_succ, Nat.mul_comm]
    rw [htwo, ← Nat.pow_add]
    unfold radix
    apply Nat.pow_lt_pow_right (by omega)
    omega
  exact hsquare.trans_lt hpow

/-! ### Parity of the convolution

Over `ZMod 2`, every off-diagonal pair `(i,j)` cancels with `(j,i)`.
Consequently the low bit of a square coefficient comes only from the unique
possible diagonal term.  This is the algebraic heart of the mask argument. -/

private abbrev Z2 := ZMod 2

private def convTerm (digit : Nat → Nat) (e : Nat) (p : Nat × Nat) : Z2 :=
  if p.1 + p.2 = e then (digit p.1 : Z2) * (digit p.2 : Z2) else 0

private theorem offDiag_sum_zero (length : Nat) (digit : Nat → Nat) (e : Nat) :
    ∑ p ∈ (Finset.range length ×ˢ Finset.range length) with p.1 ≠ p.2,
      convTerm digit e p = 0 := by
  let s := (Finset.range length ×ˢ Finset.range length).filter
    (fun p => p.1 ≠ p.2)
  change ∑ p ∈ s, convTerm digit e p = 0
  apply Finset.sum_involution (fun p _hp => (p.2, p.1))
  · intro p hp
    simp only [convTerm]
    split <;> rename_i h
    · rw [if_pos (by omega)]
      change ((digit p.1 : Z2) * digit p.2) +
        ((digit p.2 : Z2) * digit p.1) = 0
      rw [mul_comm (digit p.2 : Z2) (digit p.1 : Z2)]
      exact CharTwo.add_self_eq_zero
        ((digit p.1 : Z2) * (digit p.2 : Z2))
    · rw [if_neg (by omega)]
      simp
  · intro p hp _hterm
    simp only [s, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range] at hp
    exact fun hswap => hp.2 (congrArg Prod.fst hswap).symm
  · intro p hp
    simp only [s, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range] at hp ⊢
    omega
  · intro p hp
    rfl

theorem squareCoeff_cast_zmod2 (length : Nat) (digit : Nat → Nat) (e : Nat) :
    (squareCoeff length digit e : Z2) =
      ∑ i ∈ Finset.range length with i + i = e,
        (digit i : Z2) * digit i := by
  have hcast : (squareCoeff length digit e : Z2) =
      ∑ p ∈ Finset.range length ×ˢ Finset.range length,
        convTerm digit e p := by
    simp only [squareCoeff, Nat.cast_sum, Nat.cast_ite, Nat.cast_mul,
      Nat.cast_zero, Finset.sum_product, convTerm]
  rw [hcast]
  rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.range length ×ˢ Finset.range length) (fun p => p.1 = p.2)
    (convTerm digit e)]
  rw [offDiag_sum_zero]
  simp only [add_zero]
  calc
    (∑ p ∈ (Finset.range length ×ˢ Finset.range length) with p.1 = p.2,
        convTerm digit e p) =
        ∑ i ∈ Finset.range length,
          if i + i = e then (digit i : Z2) * digit i else 0 := by
      rw [Finset.sum_filter, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_eq_single i]
      · simp [convTerm]
      · intro j hj hji
        simp only [Finset.mem_range] at hi hj
        rw [if_neg (Ne.symm hji)]
      · intro hiNot
        exact (hiNot hi).elim
    _ = ∑ i ∈ Finset.range length with i + i = e,
          (digit i : Z2) * digit i := by
      rw [Finset.sum_filter]

theorem squareCoeff_mod_two_of_double
    {length : Nat} {digit : Nat → Nat} {e k : Nat}
    (he : e = k + k) (hk : k < length) (hdigit : digit k ≤ 1) :
    squareCoeff length digit e % 2 = digit k := by
  have hdiag :
      (∑ i ∈ Finset.range length with i + i = e,
          (digit i : Z2) * digit i) = (digit k : Z2) := by
    rw [Finset.sum_eq_single k]
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hdigit with hzero | hone
      · simp [hzero]
      · simp [hone]
    · intro j hj hjk
      simp only [Finset.mem_filter, Finset.mem_range] at hj
      exact (hjk (by omega)).elim
    · intro hkNot
      exact (hkNot (Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr hk, by omega⟩)).elim
  have hcast : (squareCoeff length digit e : Z2) = (digit k : Z2) := by
    rw [squareCoeff_cast_zmod2, hdiag]
  have hval := congrArg ZMod.val hcast
  simpa only [ZMod.val_natCast,
    Nat.mod_eq_of_lt (by omega : digit k < 2)] using hval

theorem squareCoeff_mod_two_of_not_double
    {length : Nat} {digit : Nat → Nat} {e : Nat}
    (hno : ∀ k < length, e ≠ k + k) :
    squareCoeff length digit e % 2 = 0 := by
  have hdiag :
      (∑ i ∈ Finset.range length with i + i = e,
          (digit i : Z2) * digit i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    exact (hno i hi.1 hi.2.symm).elim
  have hcast : (squareCoeff length digit e : Z2) = 0 := by
    rw [squareCoeff_cast_zmod2, hdiag]
  have hval := congrArg ZMod.val hcast
  simpa only [ZMod.val_natCast, ZMod.val_zero] using hval

theorem land_one_eq_mod_two (n : Nat) : n &&& 1 = n % 2 := by
  induction n using Nat.binaryRec with
  | zero => simp
  | bit b n ih => cases b <;> simp [Nat.bit]

/-- The dense mask padded to the convolution length. -/
def squareMaskDigits (length : Nat) : List Nat :=
  List.ofFn fun e : Fin (2 * length) ↦ if (e : Nat) < length then 1 else 0

/-- The diagonal support of a square, truncated to the blocks selected by
`squareMaskDigits`. -/
def diagonalDigits (length : Nat) (digit : Nat → Nat) : List Nat :=
  List.ofFn fun e : Fin (2 * length) ↦
    if _h : (e : Nat) < length ∧ Even (e : Nat) then digit ((e : Nat) / 2)
    else 0

@[simp] theorem squareMaskDigits_length (length : Nat) :
    (squareMaskDigits length).length = 2 * length := by
  simp [squareMaskDigits]

@[simp] theorem diagonalDigits_length (length : Nat) (digit : Nat → Nat) :
    (diagonalDigits length digit).length = 2 * length := by
  simp [diagonalDigits]

theorem ofDigits_squareMaskDigits (r length : Nat) :
    Nat.ofDigits r (squareMaskDigits length) = denseMask r length := by
  have hlist : squareMaskDigits length =
      List.replicate length 1 ++ List.replicate length 0 := by
    apply List.ext_getElem
    · simp
      omega
    · intro i hiLeft hiRight
      simp only [squareMaskDigits, List.getElem_ofFn]
      by_cases hi : i < length
      · have hi' : i < (List.replicate length 1).length := by simpa using hi
        rw [if_pos hi, List.getElem_append_left hi']
        simp
      · have hi' : (List.replicate length 1).length ≤ i := by
          simpa using Nat.le_of_not_gt hi
        rw [if_neg hi, List.getElem_append_right hi']
        simp
  rw [hlist, Nat.ofDigits_append_replicate_zero]
  rfl

theorem zipWith_squareMask_eq_diagonal {length : Nat} {digit : Nat → Nat}
    (hdigit : ∀ i, i < length → digit i ≤ 1) :
    (squareDigits length digit).zipWith (· &&& ·) (squareMaskDigits length) =
      diagonalDigits length digit := by
  apply List.ext_getElem
  · simp [squareDigits, List.length_zipWith]
  · intro e heLeft heRight
    rw [List.getElem_zipWith]
    simp only [squareDigits, squareMaskDigits, diagonalDigits,
      List.getElem_ofFn]
    by_cases helength : e < length
    · rw [if_pos helength]
      rw [land_one_eq_mod_two]
      by_cases heven : Even e
      · rw [dif_pos ⟨helength, heven⟩]
        rcases heven with ⟨k, hk⟩
        have hkhalf : e / 2 = k := by omega
        rw [hkhalf]
        apply squareCoeff_mod_two_of_double (k := k)
        · omega
        · omega
        · exact hdigit k (by omega)
      · rw [dif_neg (fun h => heven h.2)]
        apply squareCoeff_mod_two_of_not_double
        intro k hk hdouble
        apply heven
        exact ⟨k, hdouble⟩
    · rw [if_neg helength]
      rw [Nat.and_zero]
      rw [dif_neg (fun h => helength h.1)]

/-- Meeting a carry-free dense square with the all-one mask keeps exactly
the doubled diagonal support. -/
theorem land_denseSquare_denseMask {width length : Nat} {digit : Nat → Nat}
    (hwidth : 0 < width) (hdigit : ∀ i, i < length → digit i ≤ 1)
    (hcoeff : length * length < 2 ^ width) :
    denseEncode (2 ^ width) length digit *
        denseEncode (2 ^ width) length digit &&&
        denseMask (2 ^ width) length =
      Nat.ofDigits (2 ^ width) (diagonalDigits length digit) := by
  have hsquareBound : ∀ d ∈ squareDigits length digit, d < 2 ^ width := by
    intro d hd
    simp only [squareDigits, List.mem_ofFn] at hd
    rcases hd with ⟨e, rfl⟩
    exact (squareCoeff_le_sq_length hdigit e).trans_lt hcoeff
  have hmaskBound : ∀ d ∈ squareMaskDigits length, d < 2 ^ width := by
    intro d hd
    simp only [squareMaskDigits, List.mem_ofFn] at hd
    rcases hd with ⟨e, rfl⟩
    split
    · exact Nat.one_lt_two_pow (Nat.ne_of_gt hwidth)
    · exact Nat.two_pow_pos _
  rw [← ofDigits_squareDigits, ← ofDigits_squareMaskDigits]
  rw [SparseCipher.land_ofDigits_zipWith width
    (by simp [squareDigits]) hsquareBound hmaskBound]
  rw [zipWith_squareMask_eq_diagonal hdigit]

theorem land_denseEncode_denseMask {width length : Nat} {digit : Nat → Nat}
    (hwidth : 0 < width) (hdigit : ∀ i, i < length → digit i ≤ 1) :
    denseEncode (2 ^ width) length digit &&& denseMask (2 ^ width) length =
      denseEncode (2 ^ width) length digit := by
  let ds := List.ofFn fun i : Fin length ↦ digit i
  let os := List.replicate length 1
  have hlen : ds.length = os.length := by simp [ds, os]
  have hds : ∀ d ∈ ds, d < 2 ^ width := by
    intro d hd
    simp only [ds, List.mem_ofFn] at hd
    rcases hd with ⟨i, rfl⟩
    exact (hdigit i i.isLt).trans_lt
      (Nat.one_lt_two_pow (Nat.ne_of_gt hwidth))
  have hos : ∀ d ∈ os, d < 2 ^ width := by
    intro d hd
    simp only [os, List.mem_replicate] at hd
    rcases hd with ⟨_hlength, rfl⟩
    exact Nat.one_lt_two_pow (Nat.ne_of_gt hwidth)
  rw [← ofDigits_ofFn_eq_denseEncode]
  change Nat.ofDigits (2 ^ width) ds &&& Nat.ofDigits (2 ^ width) os =
    Nat.ofDigits (2 ^ width) ds
  rw [SparseCipher.land_ofDigits_zipWith width hlen hds hos]
  congr 1
  apply List.ext_getElem
  · simp [ds, os, List.length_zipWith]
  · intro i hiLeft hiRight
    rw [List.getElem_zipWith]
    simp only [ds, os, List.getElem_ofFn, List.getElem_replicate]
    rw [land_one_eq_mod_two]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp
        (hdigit i (by simpa [ds] using hiRight)) with hzero | hone
    · simp [hzero]
    · simp [hone]

/-! ## Reading the support of a certified column -/

/-- The `i`-th digit of the fixed-length expansion used in the inverse
argument. -/
def fixedDigit (r length n i : Nat) : Nat :=
  (Nat.digitsAppend r length n).getD i 0

theorem ofFn_fixedDigit {r length n : Nat} (hr : 1 < r)
    (hn : n < r ^ length) :
    List.ofFn (fun i : Fin length ↦ fixedDigit r length n i) =
      Nat.digitsAppend r length n := by
  apply List.ext_getElem
  · simp [Nat.length_digitsAppend hr length hn]
  · intro i hiLeft hiRight
    simp only [List.getElem_ofFn]
    unfold fixedDigit
    rw [List.getD_eq_getElem]

theorem denseEncode_fixedDigit {r length n : Nat} (hr : 1 < r)
    (hn : n < r ^ length) :
    denseEncode r length (fixedDigit r length n) = n := by
  rw [← ofDigits_ofFn_eq_denseEncode]
  rw [ofFn_fixedDigit hr hn]
  simp only [Nat.digitsAppend, Nat.ofDigits_append_replicate_zero,
    Nat.ofDigits_digits]

theorem fixedDigit_le_one_of_land_denseMask
    {width length n : Nat} (hwidth : 0 < width)
    (hn : n < (2 ^ width) ^ length)
    (hland : n &&& denseMask (2 ^ width) length = n) :
    ∀ i, i < length → fixedDigit (2 ^ width) length n i ≤ 1 := by
  intro i hi
  apply digitsAppend_le_one_of_land_denseMask hwidth hn hland
  unfold fixedDigit
  rw [List.getD_eq_getElem]
  exact List.getElem_mem (by
    rw [Nat.length_digitsAppend
      (Nat.one_lt_two_pow (Nat.ne_of_gt hwidth)) length hn]
    exact hi)

theorem fixedDigit_eq_zero_of_lt_pow
    {r length n i : Nat} (hr : 1 < r) (hi : i < length)
    (hnLength : n < r ^ length) (hn : n < r ^ i) :
    fixedDigit r length n i = 0 := by
  have hencode := denseEncode_fixedDigit hr hnLength
  have hmem : i ∈ Finset.range length := Finset.mem_range.mpr hi
  have hterm : fixedDigit r length n i * r ^ i ≤
      denseEncode r length (fixedDigit r length n) := by
    unfold denseEncode
    exact Finset.single_le_sum
      (fun j _hj ↦ Nat.zero_le (fixedDigit r length n j * r ^ j)) hmem
  by_contra hne
  have hone : 1 ≤ fixedDigit r length n i := Nat.one_le_iff_ne_zero.mpr hne
  have hpow : r ^ i ≤ fixedDigit r length n i * r ^ i := by
    simpa [one_mul] using Nat.mul_le_mul_right (r ^ i) hone
  rw [hencode] at hterm
  omega

/-- A fixed-length radix list with one active digit. -/
def singleDigitList (length position : Nat) : List Nat :=
  List.ofFn fun i : Fin length ↦ if (i : Nat) = position then 1 else 0

@[simp] theorem singleDigitList_length (length position : Nat) :
    (singleDigitList length position).length = length := by
  simp [singleDigitList]

theorem mem_singleDigitList_le_one {length position d : Nat}
    (hd : d ∈ singleDigitList length position) : d ≤ 1 := by
  simp only [singleDigitList, List.mem_ofFn] at hd
  rcases hd with ⟨i, rfl⟩
  split <;> simp

theorem ofDigits_singleDigitList {r length position : Nat}
    (hposition : position < length) :
    Nat.ofDigits r (singleDigitList length position) = r ^ position := by
  rw [Nat.ofDigits_eq_sum_mapIdx]
  simp only [singleDigitList, List.mapIdx_eq_ofFn, List.get_ofFn,
    List.length_ofFn, Fin.val_cast, List.sum_ofFn]
  let p : Fin length := ⟨position, hposition⟩
  calc
    (∑ i : Fin length,
        (if (i : Nat) = position then 1 else 0) * r ^ (i : Nat)) =
        ∑ i : Fin length, if p = i then r ^ (i : Nat) else 0 := by
      apply Finset.sum_congr rfl
      intro i _hi
      by_cases h : (i : Nat) = position
      · have hp : p = i := Fin.ext h.symm
        rw [if_pos h, if_pos hp, one_mul]
      · have hp : p ≠ i := by
          intro hpi
          apply h
          simpa [p] using congrArg Fin.val hpi.symm
        rw [if_neg h, if_neg hp, zero_mul]
    _ = r ^ position := by
      simpa only [p] using
        (Fintype.sum_ite_eq p (fun i : Fin length ↦ r ^ (i : Nat)))

theorem ofDigits_padded_fixedDigits (r length n : Nat) :
    Nat.ofDigits r
        (Nat.digitsAppend r length n ++ List.replicate length 0) = n := by
  rw [Nat.ofDigits_append_replicate_zero]
  simp only [Nat.digitsAppend, Nat.ofDigits_append_replicate_zero,
    Nat.ofDigits_digits]

def leftBoundaryDigits (length : Nat) (digit : Nat → Nat) : List Nat :=
  (singleDigitList (2 * length) 2).zipWith (· + ·)
    (diagonalDigits length digit)

def rightBoundaryDigits (length terminal : Nat)
    (digit : Nat → Nat) : List Nat :=
  ((List.ofFn fun i : Fin length ↦ digit i) ++ List.replicate length 0).zipWith
    (· + ·) (singleDigitList (2 * length) terminal)

@[simp] theorem leftBoundaryDigits_length (length : Nat) (digit : Nat → Nat) :
    (leftBoundaryDigits length digit).length = 2 * length := by
  simp [leftBoundaryDigits, List.length_zipWith]

@[simp] theorem rightBoundaryDigits_length
    (length terminal : Nat) (digit : Nat → Nat) :
    (rightBoundaryDigits length terminal digit).length = 2 * length := by
  simp [rightBoundaryDigits, List.length_zipWith]
  omega

private theorem mem_zipWith_add_le_two {xs ys : List Nat}
    (hlen : xs.length = ys.length)
    (hxs : ∀ x ∈ xs, x ≤ 1) (hys : ∀ y ∈ ys, y ≤ 1) :
    ∀ z ∈ xs.zipWith (· + ·) ys, z ≤ 2 := by
  intro z hz
  rcases List.mem_iff_getElem.mp hz with ⟨i, hi, rfl⟩
  have hix : i < xs.length := by
    rw [List.length_zipWith] at hi
    omega
  have hiy : i < ys.length := by omega
  rw [List.getElem_zipWith]
  have hx := hxs xs[i] (List.getElem_mem hix)
  have hy := hys ys[i] (List.getElem_mem hiy)
  omega

theorem mem_diagonalDigits_le_one {length : Nat} {digit : Nat → Nat}
    (hdigit : ∀ i, i < length → digit i ≤ 1) :
    ∀ d ∈ diagonalDigits length digit, d ≤ 1 := by
  intro d hd
  simp only [diagonalDigits, List.mem_ofFn] at hd
  rcases hd with ⟨e, rfl⟩
  split
  · rename_i h
    exact hdigit _ (by omega)
  · simp

theorem mem_padded_ofFn_le_one {length : Nat} {digit : Nat → Nat}
    (hdigit : ∀ i, i < length → digit i ≤ 1) :
    ∀ d ∈ (List.ofFn fun i : Fin length ↦ digit i) ++
        List.replicate length 0, d ≤ 1 := by
  intro d hd
  simp only [List.mem_append, List.mem_ofFn, List.mem_replicate] at hd
  rcases hd with ⟨i, rfl⟩ | ⟨_hlength, rfl⟩
  · exact hdigit i i.isLt
  · simp

/-- The telescoping boundary equation can be read without carries because
both sides have digits at most two, far below the cipher radix. -/
theorem boundary_digit_eq {r length terminal : Nat} {digit : Nat → Nat}
    (hr : 2 < r) (htwo : 2 < 2 * length) (hterminal : terminal < 2 * length)
    (hdigit : ∀ i, i < length → digit i ≤ 1)
    (hboundary : r ^ 2 + Nat.ofDigits r (diagonalDigits length digit) =
      denseEncode r length digit + r ^ terminal) :
    ∀ e, e < 2 * length →
      (if e = 2 then 1 else 0) +
          (if _h : e < length ∧ Even e then digit (e / 2) else 0) =
        (if _h : e < length then digit e else 0) +
          (if e = terminal then 1 else 0) := by
  have hleftValue : Nat.ofDigits r (leftBoundaryDigits length digit) =
      r ^ 2 + Nat.ofDigits r (diagonalDigits length digit) := by
    rw [leftBoundaryDigits]
    rw [← Nat.ofDigits_add_ofDigits_eq_ofDigits_zipWith_of_length_eq]
    · rw [ofDigits_singleDigitList htwo]
    · simp
  have hrightValue : Nat.ofDigits r (rightBoundaryDigits length terminal digit) =
      denseEncode r length digit + r ^ terminal := by
    rw [rightBoundaryDigits]
    rw [← Nat.ofDigits_add_ofDigits_eq_ofDigits_zipWith_of_length_eq]
    · rw [ofDigits_singleDigitList hterminal]
      rw [Nat.ofDigits_append_replicate_zero]
      rw [ofDigits_ofFn_eq_denseEncode]
    · simp
      omega
  have hleftBound : ∀ d ∈ leftBoundaryDigits length digit, d < r := by
    intro d hd
    have hdle : d ≤ 2 := mem_zipWith_add_le_two (by simp)
      (fun x hx ↦ mem_singleDigitList_le_one hx)
      (mem_diagonalDigits_le_one hdigit) d hd
    omega
  have hrightBound : ∀ d ∈ rightBoundaryDigits length terminal digit, d < r := by
    intro d hd
    have hdle : d ≤ 2 := mem_zipWith_add_le_two (by simp; omega)
      (mem_padded_ofFn_le_one hdigit)
      (fun x hx ↦ mem_singleDigitList_le_one hx) d hd
    omega
  have hlists : leftBoundaryDigits length digit =
      rightBoundaryDigits length terminal digit := by
    apply Nat.ofDigits_inj_of_len_eq (b := r) (by omega)
    · simp
    · exact hleftBound
    · exact hrightBound
    · rw [hleftValue, hrightValue]
      exact hboundary
  intro e he
  have hget := List.getElem_of_eq hlists (i := e) (by simp [he])
  simp only [leftBoundaryDigits, rightBoundaryDigits, List.getElem_zipWith,
    singleDigitList, diagonalDigits, List.getElem_ofFn] at hget
  by_cases helength : e < length
  · rw [List.getElem_append_left (by simpa using helength)] at hget
    simpa [helength] using hget
  · rw [List.getElem_append_right (by simpa using Nat.le_of_not_gt helength)] at hget
    simp [helength] at hget
    simpa [helength] using hget

theorem digit_zero_of_fourth_power_dvd_diagonal
    {r length : Nat} {digit : Nat → Nat}
    (hr : 1 < r) (hlength : 0 < length) (hdigit : digit 0 ≤ 1)
    (hdvd : r ^ 4 ∣ Nat.ofDigits r (diagonalDigits length digit)) :
    digit 0 = 0 := by
  have hrdvd : r ∣ Nat.ofDigits r (diagonalDigits length digit) :=
    Nat.dvd_trans (dvd_pow_self r (by omega)) hdvd
  have hmod : Nat.ofDigits r (diagonalDigits length digit) % r = 0 :=
    Nat.mod_eq_zero_of_dvd hrdvd
  rw [Nat.ofDigits_mod_eq_head!] at hmod
  have hhead : (diagonalDigits length digit).head! = digit 0 := by
    cases length with
    | zero => omega
    | succ length => simp [diagonalDigits, List.ofFn_succ]
  rw [hhead, Nat.mod_eq_of_lt (hdigit.trans_lt hr)] at hmod
  exact hmod

/-- Membership in the desired sparse support. -/
def IsSparsePlace (len e : Nat) : Prop :=
  ∃ i, i < len ∧ e = place i

theorem isSparsePlace_double_iff {len e k : Nat}
    (he : e = k + k) (heTwo : 2 < e) (heTop : e < place len) :
    IsSparsePlace len e ↔ IsSparsePlace len k := by
  constructor
  · rintro ⟨i, hi, hplace⟩
    cases i with
    | zero => simp [place] at hplace; omega
    | succ i =>
        refine ⟨i, by omega, ?_⟩
        rw [place_succ i] at hplace
        omega
  · rintro ⟨i, hi, hplace⟩
    refine ⟨i + 1, ?_, ?_⟩
    · have : place (i + 1) < place len := by
        rw [place_succ i, ← hplace, ← he]
        exact heTop
      exact place_lt_iff.mp this
    · rw [place_succ i, ← hplace, ← he]

theorem isSparsePlace_even {len e : Nat} (h : IsSparsePlace len e) :
    Even e := by
  rcases h with ⟨i, _hi, rfl⟩
  refine ⟨2 ^ i, ?_⟩
  simp [place, Nat.pow_succ]
  omega

theorem two_le_of_isSparsePlace {len e : Nat} (h : IsSparsePlace len e) :
    2 ≤ e := by
  rcases h with ⟨i, _hi, rfl⟩
  unfold place
  have : 1 ≤ 2 ^ i := Nat.one_le_two_pow
  rw [Nat.pow_succ]
  omega

/-- The boundary recurrence uniquely determines the support below its
terminal block. -/
theorem digit_one_iff_sparsePlace
    {len : Nat} {digit : Nat → Nat} (hlen : 0 < len)
    (hdigitZero : digit 0 = 0)
    (hboundary : ∀ e, e < place len →
      (if e = 2 then 1 else 0) +
          (if _h : Even e then digit (e / 2) else 0) = digit e) :
    ∀ e, e < place len → (digit e = 1 ↔ IsSparsePlace len e) := by
  have htop : 2 < place len := by
    unfold place
    have hpow := Nat.pow_lt_pow_right (by omega : 1 < (2 : Nat))
      (show 1 < len + 1 by omega)
    simpa using hpow
  have hone : digit 1 = 0 := by
    have h := hboundary 1 (by omega)
    simp at h
    exact h.symm
  have htwo : digit 2 = 1 := by
    have h := hboundary 2 (by omega)
    simp [hone] at h
    omega
  intro e
  induction e using Nat.strong_induction_on with
  | h e ih =>
      intro heTop
      rcases lt_trichotomy e 2 with heSmall | rfl | heLarge
      · have hsparse : ¬ IsSparsePlace len e := by
          intro hs
          exact (not_le_of_gt heSmall) (two_le_of_isSparsePlace hs)
        interval_cases e
        · simp [hdigitZero, hsparse]
        · simp [hone, hsparse]
      · constructor
        · intro _h
          exact ⟨0, hlen, by simp [place]⟩
        · intro _h
          exact htwo
      · by_cases heven : Even e
        · rcases heven with ⟨k, hk⟩
          have hklt : k < e := by omega
          have hkTop : k < place len := by omega
          have hrec := hboundary e heTop
          rw [if_neg (by omega), dif_pos ⟨k, hk⟩] at hrec
          have hhalf : e / 2 = k := by omega
          rw [hhalf] at hrec
          simp only [zero_add] at hrec
          rw [← hrec, ih k hklt hkTop,
            isSparsePlace_double_iff hk heLarge heTop]
        · have hrec := hboundary e heTop
          rw [if_neg (by omega), dif_neg heven] at hrec
          constructor
          · intro hone'
            rw [← hrec] at hone'
            omega
          · intro hsparse
            exact (heven (isSparsePlace_even hsparse)).elim

theorem denseCoeff_one_eq_one {len e : Nat} (hsparse : IsSparsePlace len e) :
    denseCoeff len (fun _ ↦ 1) e = 1 := by
  unfold denseCoeff
  rw [dif_pos]
  rcases hsparse with ⟨i, hi, he⟩
  exact ⟨i, hi, he.symm⟩

theorem denseCoeff_one_eq_zero {len e : Nat}
    (hsparse : ¬IsSparsePlace len e) :
    denseCoeff len (fun _ ↦ 1) e = 0 := by
  unfold denseCoeff
  rw [dif_neg]
  intro h
  rcases h with ⟨i, hi, he⟩
  exact hsparse ⟨i, hi, he.symm⟩

theorem ofFn_digit_eq_denseDigits_append_zero
    {len : Nat} {digit : Nat → Nat}
    (hdigit : ∀ e, e < place len + 1 → digit e ≤ 1)
    (htop : digit (place len) = 0)
    (hsupport : ∀ e, e < place len →
      (digit e = 1 ↔ IsSparsePlace len e)) :
    List.ofFn (fun e : Fin (place len + 1) ↦ digit e) =
      denseDigits len (fun _ ↦ 1) ++ [0] := by
  classical
  apply List.ext_getElem
  · simp
  · intro e heLeft heRight
    simp only [List.getElem_ofFn]
    by_cases he : e < place len
    · rw [List.getElem_append_left (by simpa using he)]
      simp only [denseDigits, List.getElem_ofFn]
      by_cases hsparse : IsSparsePlace len e
      · rw [denseCoeff_one_eq_one hsparse]
        exact (hsupport e he).mpr hsparse
      · rw [denseCoeff_one_eq_zero hsparse]
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp
            (hdigit e (by omega)) with hzero | hone
        · exact hzero
        · exact (hsparse ((hsupport e he).mp hone)).elim
    · have heq : e = place len := by
        have : e < place len + 1 := by simpa using heLeft
        omega
      subst e
      rw [List.getElem_append_right (by simp)]
      simpa using htop

def IsShiftedPlace (len e : Nat) : Prop :=
  ∃ i, i < len ∧ e = place (i + 1)

theorem shiftedCoeff_one_eq_one {len e : Nat}
    (hshifted : IsShiftedPlace len e) :
    shiftedCoeff len (fun _ ↦ 1) e = 1 := by
  unfold shiftedCoeff
  rw [dif_pos]
  rcases hshifted with ⟨i, hi, he⟩
  exact ⟨i, hi, he.symm⟩

theorem shiftedCoeff_one_eq_zero {len e : Nat}
    (hshifted : ¬IsShiftedPlace len e) :
    shiftedCoeff len (fun _ ↦ 1) e = 0 := by
  unfold shiftedCoeff
  rw [dif_neg]
  intro h
  rcases h with ⟨i, hi, he⟩
  exact hshifted ⟨i, hi, he.symm⟩

/-- Once the source support is known, the diagonal digits are exactly the
canonical shifted one-column (plus two harmless trailing zeros). -/
theorem diagonalDigits_eq_shiftedDigits_append_zeros
    {len : Nat} {digit : Nat → Nat}
    (hdigit : ∀ e, e < place len + 1 → digit e ≤ 1)
    (hsupport : ∀ e, e < place len →
      (digit e = 1 ↔ IsSparsePlace len e)) :
    diagonalDigits (place len + 1) digit =
      shiftedDigits len (fun _ ↦ 1) ++ [0, 0] := by
  classical
  apply List.ext_getElem
  · simp
    omega
  · intro e heLeft heRight
    simp only [diagonalDigits, List.getElem_ofFn]
    by_cases he : e < 2 * place len
    · rw [List.getElem_append_left (by simpa using he)]
      simp only [shiftedDigits, List.getElem_ofFn]
      by_cases hshifted : IsShiftedPlace len e
      · rw [shiftedCoeff_one_eq_one hshifted]
        rcases hshifted with ⟨i, hi, heq⟩
        have hiPlace : place i < place len := place_lt_place hi
        have heDouble : e = place i + place i := by
          rw [heq, place_succ]
        have heLength : e < place len + 1 := by
          rw [heq]
          have hle : i + 1 ≤ len := by omega
          exact Nat.lt_succ_of_le (place_strictMono.monotone hle)
        have heEven : Even e := ⟨place i, heDouble⟩
        rw [dif_pos ⟨heLength, heEven⟩]
        have hhalf : e / 2 = place i := by omega
        rw [hhalf]
        exact (hsupport (place i) hiPlace).mpr ⟨i, hi, rfl⟩
      · rw [shiftedCoeff_one_eq_zero hshifted]
        by_cases hdiag : e < place len + 1 ∧ Even e
        · rw [dif_pos hdiag]
          rcases hdiag.2 with ⟨k, hk⟩
          have hhalf : e / 2 = k := by omega
          rw [hhalf]
          have hkTop : k < place len := by omega
          rcases Nat.le_one_iff_eq_zero_or_eq_one.mp
              (hdigit k (by omega)) with hzero | hone
          · exact hzero
          · exfalso
            apply hshifted
            rcases (hsupport k hkTop).mp hone with ⟨i, hi, hki⟩
            refine ⟨i, hi, ?_⟩
            rw [place_succ i, ← hki, ← hk]
        · rw [dif_neg hdiag]
    · rw [List.getElem_append_right (by simpa using Nat.le_of_not_gt he)]
      have hplacePos : 0 < place len := by simp [place]
      rw [dif_neg]
      · have htail : e - 2 * place len < 2 := by
          simp only [List.length_append, shiftedDigits_length,
            List.length_cons, List.length_nil] at heRight
          omega
        have hidx : e - (shiftedDigits len fun _ ↦ 1).length < [0, 0].length := by
          simpa using htail
        have hget := List.getElem_of_eq
          (show [0, 0] = List.replicate 2 0 by rfl) hidx
        rw [List.getElem_replicate] at hget
        exact hget.symm
      · intro hdiag
        omega

/-! ## The canonical columns satisfy the certificate -/

noncomputable def canonicalDigit (len e : Nat) : Nat :=
  if e < place len then denseCoeff len (fun _ ↦ 1) e else 0

theorem canonicalDigit_le_one (len e : Nat) : canonicalDigit len e ≤ 1 := by
  unfold canonicalDigit
  split
  · rename_i he
    rcases denseCoeff_eq_zero_or (len := len) (fun _ ↦ 1) e with
      hzero | ⟨i, hi, hplace, hone⟩
    · simp [hzero]
    · simp [hone]
  · simp

theorem canonicalDigit_one_iff {len e : Nat} (he : e < place len) :
    canonicalDigit len e = 1 ↔ IsSparsePlace len e := by
  unfold canonicalDigit
  rw [if_pos he]
  constructor
  · intro hone
    rcases denseCoeff_eq_zero_or (len := len) (fun _ ↦ 1) e with
      hzero | ⟨i, hi, hplace, _hvalue⟩
    · rw [hzero] at hone
      omega
    · exact ⟨i, hi, hplace.symm⟩
  · intro hsparse
    exact denseCoeff_one_eq_one hsparse

theorem ofFn_canonicalDigit (len : Nat) :
    List.ofFn (fun e : Fin (place len + 1) ↦ canonicalDigit len e) =
      denseDigits len (fun _ ↦ 1) ++ [0] := by
  apply ofFn_digit_eq_denseDigits_append_zero
  · intro e he
    exact canonicalDigit_le_one len e
  · simp [canonicalDigit]
  · intro e he
    exact canonicalDigit_one_iff he

theorem denseEncode_canonicalDigit (len q : Nat) :
    denseEncode (radix q) (place len + 1) (canonicalDigit len) =
      encode len q (fun _ ↦ 1) := by
  rw [← ofDigits_ofFn_eq_denseEncode]
  rw [ofFn_canonicalDigit]
  rw [Nat.ofDigits_append_zero]
  exact ofDigits_denseDigits len q (fun _ ↦ 1)

theorem diagonalDigits_canonical (len : Nat) :
    diagonalDigits (place len + 1) (canonicalDigit len) =
      shiftedDigits len (fun _ ↦ 1) ++ [0, 0] := by
  apply diagonalDigits_eq_shiftedDigits_append_zeros
  · intro e he
    exact canonicalDigit_le_one len e
  · intro e he
    exact canonicalDigit_one_iff he

theorem canonical_land_mask {len q : Nat} (hq : len + 1 < q) :
    encode len q (fun _ ↦ 1) * encode len q (fun _ ↦ 1) &&&
        denseMask (radix q) (place len + 1) =
      shiftedEncode len q (fun _ ↦ 1) := by
  have hwidth : 0 < 4 * q := by omega
  have hland := land_denseSquare_denseMask
    (width := 4 * q) (length := place len + 1)
    (digit := canonicalDigit len) hwidth
    (fun i _hi ↦ canonicalDigit_le_one len i)
    (sq_place_succ_lt_radix hq)
  have hencode : denseEncode (2 ^ (4 * q)) (place len + 1)
      (canonicalDigit len) = encode len q (fun _ ↦ 1) := by
    simpa only [radix] using denseEncode_canonicalDigit len q
  simp only [radix] at hland ⊢
  rw [hencode] at hland
  rw [diagonalDigits_canonical] at hland
  have hpad : Nat.ofDigits (2 ^ (4 * q))
      (shiftedDigits len (fun _ ↦ 1) ++ [0, 0]) =
      Nat.ofDigits (2 ^ (4 * q)) (shiftedDigits len (fun _ ↦ 1)) := by
    rw [show shiftedDigits len (fun _ ↦ 1) ++ [0, 0] =
        (shiftedDigits len (fun _ ↦ 1) ++ [0]) ++ [0] by simp]
    rw [Nat.ofDigits_append_zero, Nat.ofDigits_append_zero]
  rw [hpad] at hland
  have hof := ofDigits_shiftedDigits len q (fun _ ↦ 1)
  simp only [radix] at hof
  rw [hof] at hland
  exact hland

theorem canonical_land_denseMask {len q : Nat} (hq : len + 1 < q) :
    encode len q (fun _ ↦ 1) &&& denseMask (radix q) (place len + 1) =
      encode len q (fun _ ↦ 1) := by
  have hwidth : 0 < 4 * q := by omega
  have hland := land_denseEncode_denseMask
    (width := 4 * q) (length := place len + 1)
    (digit := canonicalDigit len) hwidth
    (fun i _hi ↦ canonicalDigit_le_one len i)
  have hencode : denseEncode (2 ^ (4 * q)) (place len + 1)
      (canonicalDigit len) = encode len q (fun _ ↦ 1) := by
    simpa only [radix] using denseEncode_canonicalDigit len q
  simp only [radix] at hland ⊢
  simpa only [hencode] using hland

theorem encode_one_lt_top {len q : Nat} (hq : len + 1 < q) :
    encode len q (fun _ ↦ 1) < radix q ^ place len := by
  rw [← ofDigits_denseDigits]
  have hbound : ∀ d ∈ denseDigits len (fun _ ↦ 1), d < radix q := by
    exact mem_denseDigits_lt (fun _i _hi ↦ by
      exact (Nat.one_lt_two_pow (by omega)).trans
        (two_pow_lt_radix (by omega)))
  have hlt := Nat.ofDigits_lt_base_pow_length
    (b := radix q) (l := denseDigits len (fun _ ↦ 1))
    (radix_one_lt (by omega)) hbound
  simpa using hlt

theorem canonical_boundary (len q : Nat) :
    radix q ^ 2 + shiftedEncode len q (fun _ ↦ 1) =
      encode len q (fun _ ↦ 1) + radix q ^ place len := by
  induction len with
  | zero => simp [encode, shiftedEncode, place]
  | succ len ih =>
      have hshift : shiftedEncode (len + 1) q (fun _ ↦ 1) =
          shiftedEncode len q (fun _ ↦ 1) + radix q ^ place (len + 1) := by
        unfold shiftedEncode
        rw [Finset.sum_range_succ]
        simp
      have hencode : encode (len + 1) q (fun _ ↦ 1) =
          encode len q (fun _ ↦ 1) + radix q ^ place len := by
        unfold encode
        rw [Finset.sum_range_succ]
        simp
      rw [hshift, hencode]
      calc
        radix q ^ 2 +
            (shiftedEncode len q (fun _ ↦ 1) + radix q ^ place (len + 1)) =
            (radix q ^ 2 + shiftedEncode len q (fun _ ↦ 1)) +
              radix q ^ place (len + 1) := by omega
        _ = (encode len q (fun _ ↦ 1) + radix q ^ place len) +
              radix q ^ place (len + 1) := by rw [ih]

theorem radix_four_dvd_shifted (len q : Nat) :
    radix q ^ 4 ∣ shiftedEncode len q (fun _ ↦ 1) := by
  unfold shiftedEncode
  apply Finset.dvd_sum
  intro i hi
  simp only [one_mul]
  apply pow_dvd_pow
  have hi0 : 0 ≤ i := Nat.zero_le i
  unfold place
  have hpow := Nat.pow_le_pow_right (by omega : 0 < (2 : Nat))
    (show 2 ≤ i + 2 by omega)
  simpa using hpow

theorem canonical_onesCertificate {len q : Nat} (hq : len + 1 < q) :
    OnesCertificate len q (encode len q (fun _ ↦ 1))
      (shiftedEncode len q (fun _ ↦ 1)) := by
  by_cases hlen : len = 0
  · left
    subst len
    simp [encode, shiftedEncode]
    omega
  · right
    have hlenPos : 0 < len := Nat.pos_of_ne_zero hlen
    refine ⟨hlenPos, hq, denseMask (radix q) (place len + 1), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [denseMask_geometric (r := radix q) (Nat.two_pow_pos _)]
      rw [Nat.pow_succ]
      simp [Nat.mul_comm]
    · exact canonical_land_denseMask hq
    · exact encode_one_lt_top hq
    · exact (canonical_land_mask hq).symm
    · exact canonical_boundary len q
    · exact radix_four_dvd_shifted len q

/-! ## Semantic exactness -/

theorem positive_certificate_implies_onesCodes
    {len q ones shifted mask : Nat}
    (hlen : 0 < len) (hspacing : len + 1 < q)
    (hgeom : 1 + (radix q - 1) * mask =
      radix q * radix q ^ place len)
    (hland : ones &&& mask = ones)
    (honesLt : ones < radix q ^ place len)
    (hshifted : shifted = (ones * ones) &&& mask)
    (hboundary : radix q ^ 2 + shifted =
      ones + radix q ^ place len)
    (hdvd : radix q ^ 4 ∣ shifted) :
    OnesCodes len q ones shifted := by
  let r := radix q
  let N := place len
  let L := N + 1
  let digit := fixedDigit r L ones
  have hq : 0 < q := by omega
  have hwidth : 0 < 4 * q := by omega
  have hr : 1 < r := by
    dsimp only [r]
    exact radix_one_lt hq
  have hgeom' : 1 + (r - 1) * mask = r ^ L := by
    dsimp only [r, L, N]
    rw [Nat.pow_succ]
    simpa only [Nat.mul_comm] using hgeom
  have hmask : mask = denseMask r L :=
    eq_denseMask_of_geometric hr hgeom'
  have honesBound : ones < r ^ L := by
    exact honesLt.trans (Nat.pow_lt_pow_right (by omega) (by
      dsimp only [L, N]
      omega))
  have hland' : ones &&& denseMask r L = ones := by
    rw [← hmask]
    exact hland
  have hdigit : ∀ e, e < L → digit e ≤ 1 := by
    intro e he
    dsimp only [digit, r]
    exact fixedDigit_le_one_of_land_denseMask hwidth honesBound hland' e he
  have hdense : denseEncode r L digit = ones :=
    denseEncode_fixedDigit hr honesBound
  have htop : digit N = 0 := by
    apply fixedDigit_eq_zero_of_lt_pow hr
    · dsimp only [L]
      omega
    · exact honesBound
    · exact honesLt
  have hcoeff : L * L < 2 ^ (4 * q) := by
    simpa only [L, N, radix] using sq_place_succ_lt_radix hspacing
  have hsquare := land_denseSquare_denseMask hwidth hdigit hcoeff
  have hsquare' :
      denseEncode r L digit * denseEncode r L digit &&& denseMask r L =
        Nat.ofDigits r (diagonalDigits L digit) := by
    simpa only [r, radix] using hsquare
  have hmaskedSquare :
      (ones * ones) &&& mask = Nat.ofDigits r (diagonalDigits L digit) := by
    simpa only [hdense, hmask] using hsquare'
  have hshiftedDigits :
      shifted = Nat.ofDigits r (diagonalDigits L digit) :=
    hshifted.trans hmaskedSquare
  have hboundary' :
      r ^ 2 + Nat.ofDigits r (diagonalDigits L digit) =
        denseEncode r L digit + r ^ N := by
    rw [hdense]
    exact hshiftedDigits ▸ hboundary
  have hboundaryDigit := boundary_digit_eq
    (r := r) (length := L) (terminal := N)
    (by
      dsimp only [r, radix]
      simpa using Nat.pow_lt_pow_right (by omega : 1 < (2 : Nat))
        (by omega : 1 < 4 * q))
    (by
      dsimp only [L, N]
      have : 0 < place len := by simp [place]
      omega)
    (by
      dsimp only [L, N]
      have : 0 < place len := by simp [place]
      omega)
    hdigit hboundary'
  have hrec : ∀ e, e < N →
      (if e = 2 then 1 else 0) +
          (if _h : Even e then digit (e / 2) else 0) = digit e := by
    intro e he
    have h := hboundaryDigit e (by
      dsimp only [L, N]
      omega)
    have heL : e < L := by dsimp only [L, N]; omega
    have heN : e ≠ N := by omega
    rw [dif_pos heL, if_neg heN, add_zero] at h
    by_cases heven : Even e
    · rw [dif_pos ⟨heL, heven⟩] at h
      rw [dif_pos heven]
      exact h
    · rw [dif_neg (fun h' ↦ heven h'.2)] at h
      rw [dif_neg heven]
      exact h
  have hdvd' : r ^ 4 ∣ Nat.ofDigits r (diagonalDigits L digit) := by
    rw [← hshiftedDigits]
    exact hdvd
  have hdigitZero : digit 0 = 0 :=
    digit_zero_of_fourth_power_dvd_diagonal hr
      (by dsimp only [L, N]; omega)
      (hdigit 0 (by dsimp only [L, N]; omega)) hdvd'
  have hsupport : ∀ e, e < N →
      (digit e = 1 ↔ IsSparsePlace len e) := by
    dsimp only [N]
    exact digit_one_iff_sparsePlace hlen (by
      exact hdigitZero) (by
      intro e he
      exact hrec e he)
  have hsourceList : List.ofFn (fun e : Fin L ↦ digit e) =
      denseDigits len (fun _ ↦ 1) ++ [0] := by
    dsimp only [L, N]
    exact ofFn_digit_eq_denseDigits_append_zero
      (by intro e he; exact hdigit e he) htop (by
        intro e he
        exact hsupport e he)
  have honesValue : ones = encode len q (fun _ ↦ 1) := by
    calc
      ones = denseEncode r L digit := hdense.symm
      _ = Nat.ofDigits r (List.ofFn fun e : Fin L ↦ digit e) :=
        (ofDigits_ofFn_eq_denseEncode r L digit).symm
      _ = Nat.ofDigits r (denseDigits len (fun _ ↦ 1) ++ [0]) := by
        rw [hsourceList]
      _ = Nat.ofDigits r (denseDigits len (fun _ ↦ 1)) := by
        simp [Nat.ofDigits_append]
      _ = encode len q (fun _ ↦ 1) := by
        dsimp only [r]
        exact ofDigits_denseDigits len q (fun _ ↦ 1)
  have hdiagonalList : diagonalDigits L digit =
      shiftedDigits len (fun _ ↦ 1) ++ [0, 0] := by
    dsimp only [L, N]
    exact diagonalDigits_eq_shiftedDigits_append_zeros
      (by intro e he; exact hdigit e he) (by
        intro e he
        exact hsupport e he)
  have hshiftedValue : shifted = shiftedEncode len q (fun _ ↦ 1) := by
    calc
      shifted = Nat.ofDigits r (diagonalDigits L digit) := hshiftedDigits
      _ = Nat.ofDigits r (shiftedDigits len (fun _ ↦ 1) ++ [0, 0]) := by
        rw [hdiagonalList]
      _ = Nat.ofDigits r (shiftedDigits len (fun _ ↦ 1)) := by
        rw [show [0, 0] = List.replicate 2 0 by rfl,
          Nat.ofDigits_append_replicate_zero]
      _ = shiftedEncode len q (fun _ ↦ 1) := by
        dsimp only [r]
        exact ofDigits_shiftedDigits len q (fun _ ↦ 1)
  exact ⟨hspacing, honesValue, hshiftedValue⟩

theorem onesCodes_iff_certificate (len q ones shifted : Nat) :
    OnesCodes len q ones shifted ↔ OnesCertificate len q ones shifted := by
  constructor
  · intro h
    rcases h with ⟨hspacing, hones, hshifted⟩
    subst ones
    subst shifted
    exact canonical_onesCertificate hspacing
  · intro h
    rcases h with hzero | hpositive
    · rcases hzero with ⟨rfl, rfl, rfl, hq⟩
      simp [OnesCodes, encode, shiftedEncode]
      omega
    · rcases hpositive with
        ⟨hlen, hspacing, mask, hgeom, hland, honesLt,
          hshifted, hboundary, hdvd⟩
      exact positive_certificate_implies_onesCodes hlen hspacing hgeom hland
        honesLt hshifted hboundary hdvd

end CipherOnes
end PAListCoding
