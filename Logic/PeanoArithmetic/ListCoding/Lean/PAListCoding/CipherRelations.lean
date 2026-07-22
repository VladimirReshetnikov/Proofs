import PAListCoding.BinaryDioph
import PAListCoding.BoundedCipher
import PAListCoding.CircuitDioph

/-!
# Diophantine sparse-cipher relations

This module compiles the arithmetic relations used by `CipherCircuit` into
Mathlib's `Dioph` predicate.  The only non-elementary input is the finite
certificate for the two sparse columns of ones.  It is kept behind a small
substitution-closure contract so the arithmetic proofs below are independent
of the particular Pell/exponentiation certificate used to construct those
columns.

The semantic heart of the file is a block-mask characterization of `Code`:
a number is a well-formed sparse cipher exactly when all of its active bits
lie in the low `q` bits of the designated sparse radix blocks.  This removes
the apparent existential quantification over an infinite function from the
definition of `Code`.
-/

namespace PAListCoding

namespace CipherRelations

open SparseCipher BinaryDioph
open scoped Dioph

private theorem and_dioph {alpha : Type} {P Q : (alpha → ℕ) → Prop}
    (hP : Dioph {v | P v}) (hQ : Dioph {v | Q v}) :
    Dioph {v | P v ∧ Q v} :=
  CircuitDioph.and_dioph hP hQ

private theorem or_dioph {alpha : Type} {P Q : (alpha → ℕ) → Prop}
    (hP : Dioph {v | P v}) (hQ : Dioph {v | Q v}) :
    Dioph {v | P v ∨ Q v} := by
  apply Dioph.ext (Dioph.union hP hQ)
  intro v
  rfl

/-! ## Closure contract for the two canonical one-columns -/

/-- Substitution closure supplied by the independent construction of the
two one-columns. -/
def OnesSubstitutionClosed : Prop :=
  ∀ {alpha : Type} {len q ones shifted : (alpha → ℕ) → ℕ},
    Dioph.DiophFn len → Dioph.DiophFn q →
    Dioph.DiophFn ones → Dioph.DiophFn shifted →
      Dioph {v : alpha → ℕ |
        OnesCodes (len v) (q v) (ones v) (shifted v)}

/-! ## Elementary bit-mask facts -/

/-- Binary support inclusion is equivalently absorption by bitwise AND. -/
theorem binaryLE_iff_land_eq_left (a b : ℕ) :
    BinaryLE a b ↔ a &&& b = a := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_land]
    cases ha : a.testBit i
    · rfl
    · rw [h i ha]
      rfl
  · intro h i hi
    have hb := congrArg (fun n : ℕ => n.testBit i) h
    simpa only [Nat.testBit_land, hi, Bool.true_and] using hb

/-- Multiplying the one-column by a digit mask simply fills every occupied
radix block with that mask. -/
theorem mul_encode_ones (len q k : ℕ) :
    k * encode len q (fun _ ↦ 1) = encode len q (fun _ ↦ k) := by
  unfold encode
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- A bounded sparse encoding is unchanged when met with the mask containing
the low `q` bits of every occupied radix block. -/
theorem land_encode_mask {len q : ℕ} {f : ℕ → ℕ}
    (hq : 0 < q) (hf : ∀ i, i < len → f i < 2 ^ q) :
    encode len q f &&&
        encode len q (fun _ ↦ 2 ^ q - 1) = encode len q f := by
  rw [← ofDigits_denseDigits, ← ofDigits_denseDigits]
  simp only [radix]
  rw [land_ofDigits_zipWith (4 * q)]
  · congr 1
    apply List.ext_getElem
    · simp
    · intro e he₁ he₂
      rw [List.getElem_zipWith]
      simp only [denseDigits, List.getElem_ofFn]
      unfold denseCoeff
      split
      · rename_i h
        apply land_two_pow_sub_one_eq_self
        exact hf (Nat.find h) (Nat.find_spec h).1
      · simp
  · simp
  · apply mem_denseDigits_lt
    intro i hi
    exact (hf i hi).trans (two_pow_lt_radix hq)
  · apply mem_denseDigits_lt
    intro _i _hi
    exact (Nat.sub_lt (Nat.two_pow_pos q) Nat.one_pos).trans
      (two_pow_lt_radix hq)

/-! ## A finite block-mask characterization of arbitrary ciphers -/

/-- The arithmetic mask relation used in place of the function-valued
existential in `Code`. -/
def CodeMask (len q c : ℕ) : Prop :=
  ∃ ones shifted,
    OnesCodes len q ones shifted ∧
      BinaryLE c ((2 ^ q - 1) * ones)

/-- Absorption by the canonical block mask is sufficient to reconstruct a
bounded digit at each sparse place.  Fixed-length radix digits are used here
only in the metatheoretic correctness proof; they do not occur in the
Diophantine certificate. -/
theorem code_of_land_encode_mask {len q c : ℕ}
    (hlen : len + 1 < q)
    (hc : c &&& encode len q (fun _ ↦ 2 ^ q - 1) = c) :
    Code len q c := by
  let maskDigits := denseDigits len (fun _ ↦ 2 ^ q - 1)
  have hq : 0 < q := by omega
  have hradix : 1 < radix q := radix_one_lt hq
  have hmaskBound : ∀ d ∈ maskDigits, d < radix q := by
    intro d hd
    apply mem_denseDigits_lt (q := q) (f := fun _ ↦ 2 ^ q - 1) ?_ d hd
    intro _i _hi
    exact (Nat.sub_lt (Nat.two_pow_pos q) Nat.one_pos).trans
      (two_pow_lt_radix hq)
  have hmaskLt :
      encode len q (fun _ ↦ 2 ^ q - 1) < radix q ^ place len := by
    rw [← ofDigits_denseDigits]
    have h := Nat.ofDigits_lt_base_pow_length hradix hmaskBound
    simpa only [maskDigits, denseDigits_length] using h
  have hcLe : c ≤ encode len q (fun _ ↦ 2 ^ q - 1) := by
    rw [← hc]
    exact Nat.and_le_right
  have hcLt : c < radix q ^ place len := hcLe.trans_lt hmaskLt
  let digits := Nat.digitsAppend (radix q) (place len) c
  have hdigitsLength : digits.length = place len :=
    Nat.length_digitsAppend hradix _ hcLt
  have hdigitsBound : ∀ d ∈ digits, d < radix q := by
    intro d hd
    exact Nat.lt_of_mem_digitsAppend hradix (place len) d hd
  have hdigitsCode : Nat.ofDigits (radix q) digits = c := by
    dsimp only [digits]
    rw [Nat.digitsAppend, Nat.ofDigits_append_replicate_zero,
      Nat.ofDigits_digits]
  have hlength : digits.length = maskDigits.length := by
    simpa only [maskDigits, denseDigits_length] using hdigitsLength
  have hland := land_ofDigits_zipWith (4 * q) hlength
      (by simpa only [radix] using hdigitsBound)
      (by simpa only [radix] using hmaskBound)
  have hofDigits :
      Nat.ofDigits (radix q)
          (digits.zipWith (fun x y ↦ x &&& y) maskDigits) =
        Nat.ofDigits (radix q) digits := by
    calc
      _ = Nat.ofDigits (radix q) digits &&&
          Nat.ofDigits (radix q) maskDigits := by
        simpa only [radix] using hland.symm
      _ = _ := by
        rw [hdigitsCode]
        dsimp only [maskDigits]
        rw [ofDigits_denseDigits, hc, ← hdigitsCode]
  have hzipBound : ∀ d ∈ digits.zipWith (fun x y ↦ x &&& y) maskDigits,
      d < radix q := by
    rw [List.forall_mem_iff_getElem]
    intro i hi
    have hiDigits : i < digits.length := by
      simp only [List.length_zipWith] at hi
      omega
    rw [List.getElem_zipWith]
    exact Nat.and_le_left.trans_lt
      (hdigitsBound (digits.get ⟨i, hiDigits⟩) (List.get_mem ..))
  have hzip : digits.zipWith (fun x y ↦ x &&& y) maskDigits = digits := by
    apply Nat.ofDigits_inj_of_len_eq hradix
    · simp [List.length_zipWith, hlength]
    · exact hzipBound
    · exact hdigitsBound
    · exact hofDigits
  let f : ℕ → ℕ := fun i ↦ digits.getD (place i) 0
  have hf : ∀ i, i < len → f i < 2 ^ q := by
    intro i hi
    have hplace : place i < digits.length := by
      rw [hdigitsLength]
      exact place_lt_place hi
    have hmaskPlace : place i < maskDigits.length := by
      rw [← hlength]
      exact hplace
    have habsorb :
        digits[place i]'hplace &&& (2 ^ q - 1) = digits[place i]'hplace := by
      have hget :
          (digits.zipWith (fun x y ↦ x &&& y) maskDigits)[place i]'(by
              simp only [List.length_zipWith]
              omega) = digits[place i]'hplace := by
        exact List.getElem_of_eq hzip (by
          simp only [List.length_zipWith]
          omega)
      rw [List.getElem_zipWith] at hget
      have hmaskGet : maskDigits[place i]'hmaskPlace = 2 ^ q - 1 := by
        simpa only [maskDigits] using
          (getElem_denseDigits (fun _ ↦ 2 ^ q - 1) hi)
      simpa only [hmaskGet] using hget
    dsimp only [f]
    rw [List.getD_eq_getElem digits 0 hplace]
    calc
      digits[place i] = digits[place i] &&& (2 ^ q - 1) := habsorb.symm
      _ ≤ 2 ^ q - 1 := Nat.and_le_right
      _ < 2 ^ q := Nat.sub_lt (Nat.two_pow_pos q) Nat.one_pos
  have hdense : digits = denseDigits len f := by
    apply List.ext_getElem
    · simpa only [denseDigits_length] using hdigitsLength
    · intro e heDigits heDense
      simp only [denseDigits, List.getElem_ofFn]
      unfold denseCoeff
      split
      · rename_i h
        dsimp only [f]
        rw [(Nat.find_spec h).2]
        exact (List.getD_eq_getElem digits 0 heDigits).symm
      · rename_i h
        have heMask : e < maskDigits.length := by
          simpa only [maskDigits, denseDigits_length] using heDense
        have hmaskZero : maskDigits[e]'heMask = 0 := by
          simp only [maskDigits, denseDigits, List.getElem_ofFn]
          unfold denseCoeff
          rw [dif_neg h]
        have hget :
            (digits.zipWith (fun x y ↦ x &&& y) maskDigits)[e]'(by
                simp only [List.length_zipWith]
                omega) = digits[e]'heDigits := by
          exact List.getElem_of_eq hzip (by
            simp only [List.length_zipWith]
            omega)
        rw [List.getElem_zipWith, hmaskZero] at hget
        simpa using hget.symm
  refine ⟨f, hlen, hf, ?_⟩
  rw [← hdigitsCode, hdense, ofDigits_denseDigits]

/-- The block-mask certificate is exactly `SparseCipher.Code`. -/
theorem codeMask_iff (len q c : ℕ) : CodeMask len q c ↔ Code len q c := by
  constructor
  · rintro ⟨ones, shifted, hones, hmask⟩
    rcases hones with ⟨hlen, rfl, _hshifted⟩
    apply code_of_land_encode_mask hlen
    rw [← mul_encode_ones]
    exact binaryLE_iff_land_eq_left _ _ |>.mp hmask
  · rintro ⟨f, hlen, hf, rfl⟩
    refine ⟨encode len q (fun _ ↦ 1), shiftedEncode len q (fun _ ↦ 1),
      ⟨hlen, rfl, rfl⟩, ?_⟩
    apply binaryLE_iff_land_eq_left _ _ |>.mpr
    rw [mul_encode_ones]
    exact land_encode_mask (by omega) hf

/-! ## Diophantine closure of `Code` -/

private abbrev PairWire := Fin 2

private def pairValues (first second : ℕ) : PairWire → ℕ :=
  ![first, second]

/-- Generic substitution theorem for arbitrary cipher codes.  It is
parameterized only by the corresponding theorem for the two one-columns. -/
theorem code_dioph_of_ones (hones : OnesSubstitutionClosed)
    {alpha : Type} {len q c : (alpha → ℕ) → ℕ}
    (dlen : Dioph.DiophFn len) (dq : Dioph.DiophFn q)
    (dc : Dioph.DiophFn c) :
    Dioph {v : alpha → ℕ | Code (len v) (q v) (c v)} := by
  have dlen' : Dioph.DiophFn
      (fun v : (alpha ⊕ PairWire) → ℕ ↦ len (v ∘ Sum.inl)) :=
    Dioph.reindex_diophFn Sum.inl dlen
  have dq' : Dioph.DiophFn
      (fun v : (alpha ⊕ PairWire) → ℕ ↦ q (v ∘ Sum.inl)) :=
    Dioph.reindex_diophFn Sum.inl dq
  have dc' : Dioph.DiophFn
      (fun v : (alpha ⊕ PairWire) → ℕ ↦ c (v ∘ Sum.inl)) :=
    Dioph.reindex_diophFn Sum.inl dc
  have dwire (i : PairWire) : Dioph.DiophFn
      (fun v : (alpha ⊕ PairWire) → ℕ ↦ v (Sum.inr i)) :=
    Dioph.proj_dioph (Sum.inr i)
  have dtwo : Dioph.DiophFn
      (fun _v : (alpha ⊕ PairWire) → ℕ ↦ 2) :=
    Dioph.const_dioph 2
  have done : Dioph.DiophFn
      (fun _v : (alpha ⊕ PairWire) → ℕ ↦ 1) :=
    Dioph.const_dioph 1
  have dpow : Dioph.DiophFn
      (fun v : (alpha ⊕ PairWire) → ℕ ↦ 2 ^ q (v ∘ Sum.inl)) :=
    Dioph.pow_dioph dtwo dq'
  have dpred : Dioph.DiophFn
      (fun v : (alpha ⊕ PairWire) → ℕ ↦ 2 ^ q (v ∘ Sum.inl) - 1) :=
    Dioph.sub_dioph dpow done
  have dmask : Dioph.DiophFn
      (fun v : (alpha ⊕ PairWire) → ℕ ↦
        (2 ^ q (v ∘ Sum.inl) - 1) * v (Sum.inr 0)) :=
    Dioph.mul_dioph dpred (dwire 0)
  have dbody : Dioph {v : (alpha ⊕ PairWire) → ℕ |
      OnesCodes (len (v ∘ Sum.inl)) (q (v ∘ Sum.inl))
          (v (Sum.inr 0)) (v (Sum.inr 1)) ∧
        BinaryLE (c (v ∘ Sum.inl))
          ((2 ^ q (v ∘ Sum.inl) - 1) * v (Sum.inr 0))} :=
    and_dioph (hones dlen' dq' (dwire 0) (dwire 1))
      (binaryLE_dioph dc' dmask)
  apply Dioph.ext (Dioph.ex_dioph dbody)
  intro v
  simp only [Set.mem_setOf_eq, Sum.elim_inr]
  constructor
  · rintro ⟨w, honesw, hmask⟩
    exact (codeMask_iff (len v) (q v) (c v)).mp
      ⟨w 0, w 1, honesw, hmask⟩
  · intro hc
    rcases (codeMask_iff (len v) (q v) (c v)).mpr hc with
      ⟨ones, shifted, honesw, hmask⟩
    refine ⟨pairValues ones shifted, ?_⟩
    simpa [pairValues] using And.intro honesw hmask

/-! ## Constant columns -/

/-- Finite certificate for a constant column.  The explicit bound is needed
only for nonempty columns; an empty column always has code zero. -/
def ConstMask (len q k c : ℕ) : Prop :=
  ∃ ones shifted,
    OnesCodes len q ones shifted ∧
      c = k * ones ∧ (len = 0 ∨ k < 2 ^ q)

theorem constMask_iff (len q k c : ℕ) :
    ConstMask len q k c ↔ ConstCode len q k c := by
  constructor
  · rintro ⟨ones, shifted, ⟨hlen, hones, _hshifted⟩,
      hcode, hbound⟩
    apply constCode_iff.mpr
    exact ⟨hlen, by simpa only [hones] using hcode, hbound⟩
  · intro hc
    rcases constCode_iff.mp hc with ⟨hlen, hcode, hbound⟩
    exact ⟨encode len q (fun _ ↦ 1), shiftedEncode len q (fun _ ↦ 1),
      ⟨hlen, rfl, rfl⟩, hcode, hbound⟩

/-- Generic substitution theorem for constant columns, including a
Diophantine (not merely metatheoretically fixed) column value. -/
theorem constCode_dioph_of_ones (hones : OnesSubstitutionClosed)
    {alpha : Type} {len q k c : (alpha → ℕ) → ℕ}
    (dlen : Dioph.DiophFn len) (dq : Dioph.DiophFn q)
    (dk : Dioph.DiophFn k) (dc : Dioph.DiophFn c) :
    Dioph {v : alpha → ℕ | ConstCode (len v) (q v) (k v) (c v)} := by
  have dlen' : Dioph.DiophFn
      (fun v : (alpha ⊕ PairWire) → ℕ ↦ len (v ∘ Sum.inl)) :=
    Dioph.reindex_diophFn Sum.inl dlen
  have dq' : Dioph.DiophFn
      (fun v : (alpha ⊕ PairWire) → ℕ ↦ q (v ∘ Sum.inl)) :=
    Dioph.reindex_diophFn Sum.inl dq
  have dk' : Dioph.DiophFn
      (fun v : (alpha ⊕ PairWire) → ℕ ↦ k (v ∘ Sum.inl)) :=
    Dioph.reindex_diophFn Sum.inl dk
  have dc' : Dioph.DiophFn
      (fun v : (alpha ⊕ PairWire) → ℕ ↦ c (v ∘ Sum.inl)) :=
    Dioph.reindex_diophFn Sum.inl dc
  have dwire (i : PairWire) : Dioph.DiophFn
      (fun v : (alpha ⊕ PairWire) → ℕ ↦ v (Sum.inr i)) :=
    Dioph.proj_dioph (Sum.inr i)
  have dzero : Dioph.DiophFn
      (fun _v : (alpha ⊕ PairWire) → ℕ ↦ 0) :=
    Dioph.const_dioph 0
  have dtwo : Dioph.DiophFn
      (fun _v : (alpha ⊕ PairWire) → ℕ ↦ 2) :=
    Dioph.const_dioph 2
  have dpow : Dioph.DiophFn
      (fun v : (alpha ⊕ PairWire) → ℕ ↦ 2 ^ q (v ∘ Sum.inl)) :=
    Dioph.pow_dioph dtwo dq'
  have dproduct : Dioph.DiophFn
      (fun v : (alpha ⊕ PairWire) → ℕ ↦
        k (v ∘ Sum.inl) * v (Sum.inr 0)) :=
    Dioph.mul_dioph dk' (dwire 0)
  have dbound : Dioph {v : (alpha ⊕ PairWire) → ℕ |
      len (v ∘ Sum.inl) = 0 ∨ k (v ∘ Sum.inl) < 2 ^ q (v ∘ Sum.inl)} :=
    or_dioph (Dioph.eq_dioph dlen' dzero) (Dioph.lt_dioph dk' dpow)
  have dbody : Dioph {v : (alpha ⊕ PairWire) → ℕ |
      OnesCodes (len (v ∘ Sum.inl)) (q (v ∘ Sum.inl))
          (v (Sum.inr 0)) (v (Sum.inr 1)) ∧
        c (v ∘ Sum.inl) = k (v ∘ Sum.inl) * v (Sum.inr 0) ∧
        (len (v ∘ Sum.inl) = 0 ∨
          k (v ∘ Sum.inl) < 2 ^ q (v ∘ Sum.inl))} :=
    and_dioph (hones dlen' dq' (dwire 0) (dwire 1))
      (and_dioph (Dioph.eq_dioph dc' dproduct) dbound)
  apply Dioph.ext (Dioph.ex_dioph dbody)
  intro v
  simp only [Set.mem_setOf_eq, Sum.elim_inr]
  constructor
  · rintro ⟨w, honesw, hcode, hbound⟩
    exact (constMask_iff (len v) (q v) (k v) (c v)).mp
      ⟨w 0, w 1, honesw, hcode, hbound⟩
  · intro hc
    rcases (constMask_iff (len v) (q v) (k v) (c v)).mpr hc with
      ⟨ones, shifted, honesw, hcode, hbound⟩
    refine ⟨pairValues ones shifted, ?_⟩
    simpa [pairValues] using
      (show OnesCodes (len v) (q v) ones shifted ∧
          c v = k v * ones ∧ (len v = 0 ∨ k v < 2 ^ q v)
        from ⟨honesw, hcode, hbound⟩)

/-! ## Pointwise multiplication certificates -/

private abbrev MulWire := Fin 5

private def mulValues
    (ones shifted predRadix actualRadix p : ℕ) : MulWire → ℕ :=
  ![ones, shifted, predRadix, actualRadix, p]

/-- `SparseCipher.MulCodes` is Diophantine after arbitrary Diophantine
substitutions.  The five right-hand coordinates are exactly the witnesses in
its finite meet/mask certificate. -/
theorem mulCodes_dioph_of_ones (hones : OnesSubstitutionClosed)
    {alpha : Type} {len q ca cb cc : (alpha → ℕ) → ℕ}
    (dlen : Dioph.DiophFn len) (dq : Dioph.DiophFn q)
    (dca : Dioph.DiophFn ca) (dcb : Dioph.DiophFn cb)
    (dcc : Dioph.DiophFn cc) :
    Dioph {v : alpha → ℕ |
      MulCodes (len v) (q v) (ca v) (cb v) (cc v)} := by
  have dlen' : Dioph.DiophFn
      (fun v : (alpha ⊕ MulWire) → ℕ ↦ len (v ∘ Sum.inl)) :=
    Dioph.reindex_diophFn Sum.inl dlen
  have dq' : Dioph.DiophFn
      (fun v : (alpha ⊕ MulWire) → ℕ ↦ q (v ∘ Sum.inl)) :=
    Dioph.reindex_diophFn Sum.inl dq
  have dca' : Dioph.DiophFn
      (fun v : (alpha ⊕ MulWire) → ℕ ↦ ca (v ∘ Sum.inl)) :=
    Dioph.reindex_diophFn Sum.inl dca
  have dcb' : Dioph.DiophFn
      (fun v : (alpha ⊕ MulWire) → ℕ ↦ cb (v ∘ Sum.inl)) :=
    Dioph.reindex_diophFn Sum.inl dcb
  have dcc' : Dioph.DiophFn
      (fun v : (alpha ⊕ MulWire) → ℕ ↦ cc (v ∘ Sum.inl)) :=
    Dioph.reindex_diophFn Sum.inl dcc
  have dwire (i : MulWire) : Dioph.DiophFn
      (fun v : (alpha ⊕ MulWire) → ℕ ↦ v (Sum.inr i)) :=
    Dioph.proj_dioph (Sum.inr i)
  have dzero : Dioph.DiophFn
      (fun _v : (alpha ⊕ MulWire) → ℕ ↦ 0) :=
    Dioph.const_dioph 0
  have done : Dioph.DiophFn
      (fun _v : (alpha ⊕ MulWire) → ℕ ↦ 1) :=
    Dioph.const_dioph 1
  have dtwo : Dioph.DiophFn
      (fun _v : (alpha ⊕ MulWire) → ℕ ↦ 2) :=
    Dioph.const_dioph 2
  have dfour : Dioph.DiophFn
      (fun _v : (alpha ⊕ MulWire) → ℕ ↦ 4) :=
    Dioph.const_dioph 4
  have dfourq : Dioph.DiophFn
      (fun v : (alpha ⊕ MulWire) → ℕ ↦ 4 * q (v ∘ Sum.inl)) :=
    Dioph.mul_dioph dfour dq'
  have dradix : Dioph.DiophFn
      (fun v : (alpha ⊕ MulWire) → ℕ ↦ radix (q (v ∘ Sum.inl))) := by
    simpa only [radix] using Dioph.pow_dioph dtwo dfourq
  have dpredSucc : Dioph.DiophFn
      (fun v : (alpha ⊕ MulWire) → ℕ ↦ v (Sum.inr 2) + 1) :=
    Dioph.add_dioph (dwire 2) done
  have dcaOnes : Dioph.DiophFn
      (fun v : (alpha ⊕ MulWire) → ℕ ↦
        ca (v ∘ Sum.inl) * v (Sum.inr 0)) :=
    Dioph.mul_dioph dca' (dwire 0)
  have dcbcc : Dioph.DiophFn
      (fun v : (alpha ⊕ MulWire) → ℕ ↦
        cb (v ∘ Sum.inl) * cc (v ∘ Sum.inl)) :=
    Dioph.mul_dioph dcb' dcc'
  have dmask : Dioph.DiophFn
      (fun v : (alpha ⊕ MulWire) → ℕ ↦
        v (Sum.inr 2) * v (Sum.inr 1)) :=
    Dioph.mul_dioph (dwire 2) (dwire 1)
  have dmeetA : Dioph.DiophFn
      (fun v : (alpha ⊕ MulWire) → ℕ ↦
        (ca (v ∘ Sum.inl) * v (Sum.inr 0)) &&&
          (v (Sum.inr 2) * v (Sum.inr 1))) :=
    land_diophFn dcaOnes dmask
  have dmeetBC : Dioph.DiophFn
      (fun v : (alpha ⊕ MulWire) → ℕ ↦
        (cb (v ∘ Sum.inl) * cc (v ∘ Sum.inl)) &&&
          (v (Sum.inr 2) * v (Sum.inr 1))) :=
    land_diophFn dcbcc dmask
  have dbody : Dioph {v : (alpha ⊕ MulWire) → ℕ |
      len (v ∘ Sum.inl) ≠ 0 ∧
        v (Sum.inr 3) = radix (q (v ∘ Sum.inl)) ∧
        v (Sum.inr 3) = v (Sum.inr 2) + 1 ∧
        OnesCodes (len (v ∘ Sum.inl)) (q (v ∘ Sum.inl))
          (v (Sum.inr 0)) (v (Sum.inr 1)) ∧
        v (Sum.inr 4) =
          (ca (v ∘ Sum.inl) * v (Sum.inr 0)) &&&
            (v (Sum.inr 2) * v (Sum.inr 1)) ∧
        v (Sum.inr 4) =
          (cb (v ∘ Sum.inl) * cc (v ∘ Sum.inl)) &&&
            (v (Sum.inr 2) * v (Sum.inr 1))} :=
    and_dioph (Dioph.ne_dioph dlen' dzero) <|
      and_dioph (Dioph.eq_dioph (dwire 3) dradix) <|
      and_dioph (Dioph.eq_dioph (dwire 3) dpredSucc) <|
      and_dioph (hones dlen' dq' (dwire 0) (dwire 1)) <|
      and_dioph (Dioph.eq_dioph (dwire 4) dmeetA)
        (Dioph.eq_dioph (dwire 4) dmeetBC)
  have dnonempty : Dioph {v : alpha → ℕ |
      len v ≠ 0 ∧
        ∃ ones shifted predRadix actualRadix p,
          actualRadix = radix (q v) ∧
          actualRadix = predRadix + 1 ∧
          OnesCodes (len v) (q v) ones shifted ∧
          p = (ca v * ones) &&& (predRadix * shifted) ∧
          p = (cb v * cc v) &&& (predRadix * shifted)} := by
    apply Dioph.ext (Dioph.ex_dioph dbody)
    intro v
    simp only [Set.mem_setOf_eq, Sum.elim_inr]
    constructor
    · rintro ⟨w, hne, hradix, hsucc, honesw, hmeetA, hmeetBC⟩
      exact ⟨hne, w 0, w 1, w 2, w 3, w 4,
        hradix, hsucc, honesw, hmeetA, hmeetBC⟩
    · rintro ⟨hne, ones, shifted, predRadix, actualRadix, p,
        hradix, hsucc, honesw, hmeetA, hmeetBC⟩
      refine ⟨mulValues ones shifted predRadix actualRadix p, ?_⟩
      simpa [mulValues] using
        (show len v ≠ 0 ∧
            actualRadix = radix (q v) ∧
            actualRadix = predRadix + 1 ∧
            OnesCodes (len v) (q v) ones shifted ∧
            p = (ca v * ones) &&& (predRadix * shifted) ∧
            p = (cb v * cc v) &&& (predRadix * shifted)
          from ⟨hne, hradix, hsucc, honesw, hmeetA, hmeetBC⟩)
  have dzero : Dioph {v : alpha → ℕ | len v = 0} :=
    Dioph.eq_dioph dlen (Dioph.const_dioph 0)
  simpa only [MulCodes] using or_dioph dzero dnonempty

/-- The operand/output ordering used by `BoundedCipher` is likewise closed
under arbitrary Diophantine substitutions. -/
theorem mulRel_dioph_of_ones (hones : OnesSubstitutionClosed)
    {alpha : Type} {len q left right output : (alpha → ℕ) → ℕ}
    (dlen : Dioph.DiophFn len) (dq : Dioph.DiophFn q)
    (dleft : Dioph.DiophFn left) (dright : Dioph.DiophFn right)
    (doutput : Dioph.DiophFn output) :
    Dioph {v : alpha → ℕ |
      BoundedCipher.MulRel (len v) (q v) (left v) (right v) (output v)} := by
  simpa only [BoundedCipher.MulRel] using
    mulCodes_dioph_of_ones hones dlen dq doutput dleft dright

/-! ## Radix identities for the index column -/

/-- Extend a finite prefix by one final value.  Values beyond the displayed
prefix are irrelevant to `encode`. -/
private def appendValue (len : ℕ) (f : ℕ → ℕ) (last : ℕ) (i : ℕ) : ℕ :=
  if i < len then f i else last

/-- Shift a sequence one sparse position to the right, inserting zero. -/
private def shiftValue (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => f i

private theorem encode_appendValue (len q last : ℕ) (f : ℕ → ℕ) :
    encode (len + 1) q (appendValue len f last) =
      encode len q f + last * radix q ^ place len := by
  unfold encode
  rw [Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    simp only [appendValue, Finset.mem_range.mp hi, if_true]
  · simp only [appendValue, lt_self_iff_false, if_false]

private theorem shiftedEncode_eq_encode_shiftValue (len q : ℕ) (f : ℕ → ℕ) :
    shiftedEncode len q f = encode (len + 1) q (shiftValue f) := by
  unfold shiftedEncode encode
  rw [Finset.sum_range_succ']
  simp only [shiftValue, zero_mul, add_zero]

private theorem encode_add (len q : ℕ) (f g : ℕ → ℕ) :
    encode len q (fun i ↦ f i + g i) = encode len q f + encode len q g := by
  unfold encode
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

private theorem encode_succ_ones (len q : ℕ) :
    encode (len + 1) q (fun _ ↦ 1) =
      radix q * radix q + shiftedEncode len q (fun _ ↦ 1) := by
  unfold encode shiftedEncode
  rw [Finset.sum_range_succ']
  simp only [one_mul]
  rw [show place 0 = 2 by rfl, pow_two]
  omega

private theorem encode_append_add_one (len q : ℕ) (f : ℕ → ℕ) :
    encode (len + 1) q (fun i ↦ appendValue len f 0 i + 1) =
      encode len q f + shiftedEncode len q (fun _ ↦ 1) +
        radix q * radix q := by
  rw [encode_add]
  rw [encode_appendValue, encode_succ_ones]
  simp only [zero_mul, add_zero]
  omega

private theorem index_shift_identity (len q : ℕ) :
    encode len q id + len * radix q ^ place len =
      shiftedEncode len q (fun i ↦ i + 1) := by
  rw [← encode_appendValue, shiftedEncode_eq_encode_shiftValue]
  unfold encode
  apply Finset.sum_congr rfl
  intro i hi
  congr 2
  have hi' : i < len + 1 := Finset.mem_range.mp hi
  rcases i with _ | i
  · simp [appendValue, shiftValue]
  · simp only [appendValue, shiftValue, id_eq]
    by_cases hil : i + 1 < len
    · simp [hil]
    · have : i + 1 = len := by omega
      simp [this]

private theorem index_increment_identity (len q : ℕ) :
    encode len q id + shiftedEncode len q (fun _ ↦ 1) +
        radix q * radix q =
      encode len q (fun i ↦ i + 1) + radix q ^ place len := by
  rw [← encode_append_add_one]
  have happend := encode_appendValue len q 1 (fun i ↦ i + 1)
  simp only [one_mul] at happend
  rw [← happend]
  unfold encode
  apply Finset.sum_congr rfl
  intro i hi
  congr 2
  have hi' : i < len + 1 := Finset.mem_range.mp hi
  simp only [appendValue, id_eq]
  by_cases hil : i < len
  · simp [hil]
  · have : i = len := by omega
    simp [this]

/-! ## A finite certificate for the zero-based index column -/

/-- Rocq's `CodeNat_dio` certificate, adapted to the sparse-cipher names in
this development.  The first meet equation shifts the auxiliary successor
column one sparse position; the second equation says that this auxiliary
column is pointwise one greater than the candidate index column. -/
def IndexMask (len q y : ℕ) : Prop :=
  ∃ z ones shifted actualRadix topPlace topPower predRadix,
    actualRadix = radix q ∧
    actualRadix = predRadix + 1 ∧
    topPlace = 2 ^ (1 + len) ∧
    topPower = actualRadix ^ topPlace ∧
    OnesCodes len q ones shifted ∧
    Code len q y ∧
    Code len q z ∧
    y + len * topPower =
      (z * ones) &&& (predRadix * shifted) ∧
    y + shifted + actualRadix * actualRadix = z + topPower

/-- The finite successor/shift certificate defines exactly the index
column. -/
theorem indexMask_iff (len q y : ℕ) :
    IndexMask len q y ↔ IndexCode len q y := by
  constructor
  · rintro ⟨z, ones, shifted, actualRadix, topPlace, topPower,
      predRadix, hactual, hpredSucc, htopPlace, htopPower,
      hones, hyCode, hzCode, hshiftEq, hincEq⟩
    rcases hones with ⟨hlen, honesValue, hshiftedValue⟩
    rcases hyCode with ⟨f, hf⟩
    rcases hzCode with ⟨g, hg⟩
    rcases hf with ⟨_hlenf, hfBound, hyValue⟩
    rcases hg with ⟨_hleng, hgBound, hzValue⟩
    have hq : 0 < q := by omega
    have honeBound : ∀ i, i < len → (1 : ℕ) < 2 ^ q := by
      intro _i _hi
      exact Nat.one_lt_two_pow (by omega)
    have hpredValue : predRadix = radix q - 1 := by
      have hradixPos : 0 < radix q := Nat.two_pow_pos _
      omega
    have htopPlaceValue : topPlace = place len := by
      rw [htopPlace]
      simp only [place]
      congr 1
      omega
    have htopPowerValue : topPower = radix q ^ place len := by
      rw [htopPower, hactual, htopPlaceValue]
    have hshiftEq' :
        encode len q f + len * radix q ^ place len = shiftedEncode len q g := by
      rw [hyValue, hzValue, honesValue, hshiftedValue,
        htopPowerValue, hpredValue] at hshiftEq
      rw [← diagonalMask_eq] at hshiftEq
      have hland := land_product_diagonalMask hlen hgBound honeBound
      rw [hland] at hshiftEq
      simpa only [Nat.mul_one] using hshiftEq
    have hencShift :
        encode (len + 1) q (appendValue len f len) =
          encode (len + 1) q (shiftValue g) := by
      rw [encode_appendValue]
      rw [← shiftedEncode_eq_encode_shiftValue]
      exact hshiftEq'
    have hlenRadix : len < radix q := by
      exact (show len < q by omega).trans
        ((Nat.lt_pow_self (a := 2) (by omega)).trans (two_pow_lt_radix hq))
    have happendBound : ∀ i, i < len + 1 →
        appendValue len f len i < radix q := by
      intro i hi
      unfold appendValue
      split
      · rename_i hil
        exact (hfBound i hil).trans (two_pow_lt_radix hq)
      · exact hlenRadix
    have hshiftBound : ∀ i, i < len + 1 →
        shiftValue g i < radix q := by
      intro i hi
      rcases i with _ | i
      · exact Nat.zero_lt_of_lt (radix_one_lt hq)
      · exact (hgBound i (by omega)).trans (two_pow_lt_radix hq)
    have hshiftPoint : ∀ i, i < len + 1 →
        appendValue len f len i = shiftValue g i :=
      encode_injective_of_lt_radix hq happendBound hshiftBound hencShift
    have hfZero : len ≠ 0 → f 0 = 0 := by
      intro hne
      have h := hshiftPoint 0 (by omega)
      simpa [appendValue, shiftValue, Nat.pos_of_ne_zero hne] using h
    have hfShift : ∀ i, i + 1 < len → f (i + 1) = g i := by
      intro i hi
      have h := hshiftPoint (i + 1) (by omega)
      simpa [appendValue, shiftValue, hi] using h
    have hincEq' :
        encode len q f + shiftedEncode len q (fun _ ↦ 1) +
            radix q * radix q =
          encode len q g + radix q ^ place len := by
      simpa only [hyValue, hzValue, hshiftedValue, hactual,
        htopPowerValue] using hincEq
    have hencInc :
        encode (len + 1) q (fun i ↦ appendValue len f 0 i + 1) =
          encode (len + 1) q (appendValue len g 1) := by
      rw [encode_append_add_one]
      rw [encode_appendValue]
      simpa only [one_mul] using hincEq'
    have hleftBound : ∀ i, i < len + 1 →
        appendValue len f 0 i + 1 < radix q := by
      intro i hi
      unfold appendValue
      split
      · rename_i hil
        have hle : f i + 1 ≤ 2 ^ q := Nat.add_one_le_iff.mpr (hfBound i hil)
        exact hle.trans_lt (two_pow_lt_radix hq)
      · simpa using radix_one_lt hq
    have hrightBound : ∀ i, i < len + 1 →
        appendValue len g 1 i < radix q := by
      intro i hi
      unfold appendValue
      split
      · rename_i hil
        exact (hgBound i hil).trans (two_pow_lt_radix hq)
      · simpa using radix_one_lt hq
    have hincPoint : ∀ i, i < len + 1 →
        appendValue len f 0 i + 1 = appendValue len g 1 i :=
      encode_injective_of_lt_radix hq hleftBound hrightBound hencInc
    have hsucc : ∀ i, i < len → f i + 1 = g i := by
      intro i hi
      have h := hincPoint i (by omega)
      simpa [appendValue, hi] using h
    have hfId : ∀ i, i < len → f i = i := by
      intro i
      induction i with
      | zero =>
          intro hi
          exact hfZero (by omega)
      | succ i ih =>
          intro hi
          calc
            f (i + 1) = g i := hfShift i hi
            _ = f i + 1 := (hsucc i (by omega)).symm
            _ = i + 1 := by rw [ih (by omega)]
    exact CipherCircuit.isCipher_congr
      ⟨hlen, hfBound, hyValue⟩ hfId
  · intro hy
    rcases hy with ⟨hlen, hyBound, hyValue⟩
    let successor : ℕ → ℕ := fun i ↦ i + 1
    let z := encode len q successor
    have hsuccessorBound : ∀ i, i < len → successor i < 2 ^ q := by
      intro i hi
      exact (show i + 1 < q by omega).trans
        (Nat.lt_pow_self (a := 2) (by omega))
    have hz : IsCipher len q successor z :=
      ⟨hlen, hsuccessorBound, rfl⟩
    have honeBound : ∀ i, i < len → (1 : ℕ) < 2 ^ q := by
      intro _i _hi
      exact Nat.one_lt_two_pow (by omega)
    refine ⟨z, encode len q (fun _ ↦ 1),
      shiftedEncode len q (fun _ ↦ 1), radix q,
      2 ^ (1 + len), radix q ^ place len, radix q - 1,
      rfl, ?_, ?_, ?_, ⟨hlen, rfl, rfl⟩,
      ⟨id, hlen, hyBound, hyValue⟩, ⟨successor, hz⟩, ?_, ?_⟩
    · exact (Nat.sub_add_cancel
        (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.two_pow_pos _)))).symm
    · rfl
    · congr 1
      simp only [place]
      congr 1
      omega
    · rw [hyValue]
      change encode len q id + len * (radix q ^ place len) =
        (encode len q successor * encode len q (fun _ ↦ 1)) &&&
          ((radix q - 1) * shiftedEncode len q (fun _ ↦ 1))
      rw [← diagonalMask_eq]
      rw [land_product_diagonalMask hlen hsuccessorBound honeBound]
      simpa only [successor, Nat.mul_one] using index_shift_identity len q
    · rw [hyValue]
      change encode len q id + shiftedEncode len q (fun _ ↦ 1) +
          radix q * radix q = encode len q successor + radix q ^ place len
      simpa only [successor] using index_increment_identity len q

/-! ## Diophantine closure of the index column -/

private abbrev IndexWire := Fin 7

private def indexValues
    (z ones shifted actualRadix topPlace topPower predRadix : ℕ) :
    IndexWire → ℕ :=
  ![z, ones, shifted, actualRadix, topPlace, topPower, predRadix]

/-- Generic substitution theorem for the zero-based index column. -/
theorem indexCode_dioph_of_ones (hones : OnesSubstitutionClosed)
    {alpha : Type} {len q y : (alpha → ℕ) → ℕ}
    (dlen : Dioph.DiophFn len) (dq : Dioph.DiophFn q)
    (dy : Dioph.DiophFn y) :
    Dioph {v : alpha → ℕ | IndexCode (len v) (q v) (y v)} := by
  have dlen' : Dioph.DiophFn
      (fun v : (alpha ⊕ IndexWire) → ℕ ↦ len (v ∘ Sum.inl)) :=
    Dioph.reindex_diophFn Sum.inl dlen
  have dq' : Dioph.DiophFn
      (fun v : (alpha ⊕ IndexWire) → ℕ ↦ q (v ∘ Sum.inl)) :=
    Dioph.reindex_diophFn Sum.inl dq
  have dy' : Dioph.DiophFn
      (fun v : (alpha ⊕ IndexWire) → ℕ ↦ y (v ∘ Sum.inl)) :=
    Dioph.reindex_diophFn Sum.inl dy
  have dwire (i : IndexWire) : Dioph.DiophFn
      (fun v : (alpha ⊕ IndexWire) → ℕ ↦ v (Sum.inr i)) :=
    Dioph.proj_dioph (Sum.inr i)
  have done : Dioph.DiophFn
      (fun _v : (alpha ⊕ IndexWire) → ℕ ↦ 1) :=
    Dioph.const_dioph 1
  have dtwo : Dioph.DiophFn
      (fun _v : (alpha ⊕ IndexWire) → ℕ ↦ 2) :=
    Dioph.const_dioph 2
  have dfour : Dioph.DiophFn
      (fun _v : (alpha ⊕ IndexWire) → ℕ ↦ 4) :=
    Dioph.const_dioph 4
  have dfourq : Dioph.DiophFn
      (fun v : (alpha ⊕ IndexWire) → ℕ ↦ 4 * q (v ∘ Sum.inl)) :=
    Dioph.mul_dioph dfour dq'
  have dradix : Dioph.DiophFn
      (fun v : (alpha ⊕ IndexWire) → ℕ ↦ radix (q (v ∘ Sum.inl))) := by
    simpa only [radix] using Dioph.pow_dioph dtwo dfourq
  have dpredSucc : Dioph.DiophFn
      (fun v : (alpha ⊕ IndexWire) → ℕ ↦ v (Sum.inr 6) + 1) :=
    Dioph.add_dioph (dwire 6) done
  have dlenSucc : Dioph.DiophFn
      (fun v : (alpha ⊕ IndexWire) → ℕ ↦ 1 + len (v ∘ Sum.inl)) :=
    Dioph.add_dioph done dlen'
  have dtopPlace : Dioph.DiophFn
      (fun v : (alpha ⊕ IndexWire) → ℕ ↦ 2 ^ (1 + len (v ∘ Sum.inl))) :=
    Dioph.pow_dioph dtwo dlenSucc
  have dtopPower : Dioph.DiophFn
      (fun v : (alpha ⊕ IndexWire) → ℕ ↦
        v (Sum.inr 3) ^ v (Sum.inr 4)) :=
    Dioph.pow_dioph (dwire 3) (dwire 4)
  have dlenTop : Dioph.DiophFn
      (fun v : (alpha ⊕ IndexWire) → ℕ ↦
        len (v ∘ Sum.inl) * v (Sum.inr 5)) :=
    Dioph.mul_dioph dlen' (dwire 5)
  have dshiftLeft : Dioph.DiophFn
      (fun v : (alpha ⊕ IndexWire) → ℕ ↦
        y (v ∘ Sum.inl) + len (v ∘ Sum.inl) * v (Sum.inr 5)) :=
    Dioph.add_dioph dy' dlenTop
  have dzOnes : Dioph.DiophFn
      (fun v : (alpha ⊕ IndexWire) → ℕ ↦
        v (Sum.inr 0) * v (Sum.inr 1)) :=
    Dioph.mul_dioph (dwire 0) (dwire 1)
  have dpredShifted : Dioph.DiophFn
      (fun v : (alpha ⊕ IndexWire) → ℕ ↦
        v (Sum.inr 6) * v (Sum.inr 2)) :=
    Dioph.mul_dioph (dwire 6) (dwire 2)
  have dmeet : Dioph.DiophFn
      (fun v : (alpha ⊕ IndexWire) → ℕ ↦
        (v (Sum.inr 0) * v (Sum.inr 1)) &&&
          (v (Sum.inr 6) * v (Sum.inr 2))) :=
    land_diophFn dzOnes dpredShifted
  have dyShifted : Dioph.DiophFn
      (fun v : (alpha ⊕ IndexWire) → ℕ ↦
        y (v ∘ Sum.inl) + v (Sum.inr 2)) :=
    Dioph.add_dioph dy' (dwire 2)
  have dactualSq : Dioph.DiophFn
      (fun v : (alpha ⊕ IndexWire) → ℕ ↦
        v (Sum.inr 3) * v (Sum.inr 3)) :=
    Dioph.mul_dioph (dwire 3) (dwire 3)
  have dincLeft : Dioph.DiophFn
      (fun v : (alpha ⊕ IndexWire) → ℕ ↦
        y (v ∘ Sum.inl) + v (Sum.inr 2) +
          v (Sum.inr 3) * v (Sum.inr 3)) :=
    Dioph.add_dioph dyShifted dactualSq
  have dincRight : Dioph.DiophFn
      (fun v : (alpha ⊕ IndexWire) → ℕ ↦
        v (Sum.inr 0) + v (Sum.inr 5)) :=
    Dioph.add_dioph (dwire 0) (dwire 5)
  have dbody : Dioph {v : (alpha ⊕ IndexWire) → ℕ |
      v (Sum.inr 3) = radix (q (v ∘ Sum.inl)) ∧
      v (Sum.inr 3) = v (Sum.inr 6) + 1 ∧
      v (Sum.inr 4) = 2 ^ (1 + len (v ∘ Sum.inl)) ∧
      v (Sum.inr 5) = v (Sum.inr 3) ^ v (Sum.inr 4) ∧
      OnesCodes (len (v ∘ Sum.inl)) (q (v ∘ Sum.inl))
        (v (Sum.inr 1)) (v (Sum.inr 2)) ∧
      Code (len (v ∘ Sum.inl)) (q (v ∘ Sum.inl))
        (y (v ∘ Sum.inl)) ∧
      Code (len (v ∘ Sum.inl)) (q (v ∘ Sum.inl))
        (v (Sum.inr 0)) ∧
      y (v ∘ Sum.inl) + len (v ∘ Sum.inl) * v (Sum.inr 5) =
        (v (Sum.inr 0) * v (Sum.inr 1)) &&&
          (v (Sum.inr 6) * v (Sum.inr 2)) ∧
      y (v ∘ Sum.inl) + v (Sum.inr 2) +
          v (Sum.inr 3) * v (Sum.inr 3) =
        v (Sum.inr 0) + v (Sum.inr 5)} :=
    and_dioph (Dioph.eq_dioph (dwire 3) dradix) <|
      and_dioph (Dioph.eq_dioph (dwire 3) dpredSucc) <|
      and_dioph (Dioph.eq_dioph (dwire 4) dtopPlace) <|
      and_dioph (Dioph.eq_dioph (dwire 5) dtopPower) <|
      and_dioph (hones dlen' dq' (dwire 1) (dwire 2)) <|
      and_dioph (code_dioph_of_ones hones dlen' dq' dy') <|
      and_dioph (code_dioph_of_ones hones dlen' dq' (dwire 0)) <|
      and_dioph (Dioph.eq_dioph dshiftLeft dmeet)
        (Dioph.eq_dioph dincLeft dincRight)
  apply Dioph.ext (Dioph.ex_dioph dbody)
  intro v
  simp only [Set.mem_setOf_eq, Sum.elim_inr]
  constructor
  · rintro ⟨w, hactual, hpredSucc, htopPlace, htopPower,
      honesw, hyCode, hzCode, hshift, hinc⟩
    exact (indexMask_iff (len v) (q v) (y v)).mp
      ⟨w 0, w 1, w 2, w 3, w 4, w 5, w 6,
        hactual, hpredSucc, htopPlace, htopPower,
        honesw, hyCode, hzCode, hshift, hinc⟩
  · intro hy
    rcases (indexMask_iff (len v) (q v) (y v)).mpr hy with
      ⟨z, ones, shifted, actualRadix, topPlace, topPower, predRadix,
        hactual, hpredSucc, htopPlace, htopPower,
        honesw, hyCode, hzCode, hshift, hinc⟩
    refine ⟨indexValues z ones shifted actualRadix topPlace topPower predRadix, ?_⟩
    simpa [indexValues] using
      (show actualRadix = radix (q v) ∧
          actualRadix = predRadix + 1 ∧
          topPlace = 2 ^ (1 + len v) ∧
          topPower = actualRadix ^ topPlace ∧
          OnesCodes (len v) (q v) ones shifted ∧
          Code (len v) (q v) (y v) ∧
          Code (len v) (q v) z ∧
          y v + len v * topPower =
            (z * ones) &&& (predRadix * shifted) ∧
          y v + shifted + actualRadix * actualRadix = z + topPower
        from ⟨hactual, hpredSucc, htopPlace, htopPower,
          honesw, hyCode, hzCode, hshift, hinc⟩)

/-! ## Primitive closure contracts for the circuit compilers -/

/-- The four-place analogue of `CircuitDioph.TernarySubstitutionClosed`.
This unfolds to the same contract used by `BoundedCipherDioph`; keeping the
definition here avoids making the arithmetic relation layer depend on the
downstream bounded-certificate compiler. -/
def QuaternarySubstitutionClosed
    (R : ℕ → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ {alpha : Type} {a b c d : (alpha → ℕ) → ℕ},
    Dioph.DiophFn a → Dioph.DiophFn b →
    Dioph.DiophFn c → Dioph.DiophFn d →
      Dioph {v : alpha → ℕ | R (a v) (b v) (c v) (d v)}

/-- Closure contract consumed by `CircuitDioph` for arbitrary codes. -/
theorem code_closed_of_ones (hones : OnesSubstitutionClosed) :
    CircuitDioph.TernarySubstitutionClosed Code := by
  intro alpha len q c dlen dq dc
  exact code_dioph_of_ones hones dlen dq dc

/-- Closure contract consumed by fixed expression constants in
`CircuitDioph`. -/
theorem constCode_fixed_closed_of_ones (hones : OnesSubstitutionClosed) :
    ∀ k, CircuitDioph.TernarySubstitutionClosed
      (fun len q c ↦ ConstCode len q k c) := by
  intro k alpha len q c dlen dq dc
  exact constCode_dioph_of_ones hones dlen dq (Dioph.const_dioph k) dc

/-- Four-place substitution closure for parameter-valued constant columns. -/
theorem constCode_closed_of_ones (hones : OnesSubstitutionClosed) :
    QuaternarySubstitutionClosed ConstCode := by
  intro alpha len q k c dlen dq dk dc
  exact constCode_dioph_of_ones hones dlen dq dk dc

/-- Closure contract for the distinguished zero-based row-index column. -/
theorem indexCode_closed_of_ones (hones : OnesSubstitutionClosed) :
    CircuitDioph.TernarySubstitutionClosed IndexCode := by
  intro alpha len q c dlen dq dc
  exact indexCode_dioph_of_ones hones dlen dq dc

/-- Closure contract for pointwise circuit multiplication, in the operand
ordering expected by `BoundedCipher.MulRel`. -/
theorem mulRel_closed_of_ones (hones : OnesSubstitutionClosed) :
    CircuitDioph.QuinarySubstitutionClosed BoundedCipher.MulRel := by
  intro alpha len q left right output dlen dq dleft dright doutput
  exact mulRel_dioph_of_ones hones dlen dq dleft dright doutput

end CipherRelations

end PAListCoding
