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
    ones * ones < radix q * radix q ^ place len ∧
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

end CipherOnes
end PAListCoding
