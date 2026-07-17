import PAListCoding.EpsilonZero

/-!
# Algebra and order laws for epsilon-zero codes

The coding layer proves each individual operation correct.  This companion
file packages the familiar laws of ordinal arithmetic directly at the level
of natural-number codes.  Every statement carries the normal-form hypotheses
that make the public operations meaningful; equality is then reflected back
from set-theoretic ordinals by uniqueness of canonical CNF.
-/

namespace PAListCoding.EpsilonZero

open Ordinal
open scoped Ordinal

/-! ## Distinguished codes -/

/-- The canonical code of the ordinal zero. -/
def zeroCode : ℕ := encode 0

/-- The canonical code of the ordinal one. -/
def oneCode : ℕ := encode 1

@[simp] theorem zeroCode_eq : zeroCode = 0 := rfl

@[simp] theorem decode_zeroCode : decode zeroCode = 0 := by simp [zeroCode]

@[simp] theorem decode_oneCode : decode oneCode = 1 := by simp [oneCode]

@[simp] theorem zeroCode_valid : ValidOrdinalCode zeroCode := by
  simpa [zeroCode, ValidOrdinalCode] using ONote.NF.zero

@[simp] theorem oneCode_valid : ValidOrdinalCode oneCode := by
  simpa [oneCode, ValidOrdinalCode] using (inferInstance : ONote.NF (1 : ONote))

@[simp] theorem denote_zeroCode : denote zeroCode = 0 := by simp [zeroCode, denote]

@[simp] theorem denote_oneCode : denote oneCode = 1 := by simp [oneCode, denote]

/-! ## Strict linear order on valid codes -/

theorem ordinalLT_irrefl {a : ℕ} : ¬OrdinalLT a a := by
  intro h
  have := (ordinalLT_iff a a).mp h
  exact (lt_irrefl (denote a)) this.2.2

theorem ordinalLT_trans {a b c : ℕ}
    (hab : OrdinalLT a b) (hbc : OrdinalLT b c) : OrdinalLT a c := by
  rw [ordinalLT_iff] at hab hbc ⊢
  exact ⟨hab.1, hbc.2.1, hab.2.2.trans hbc.2.2⟩

theorem ordinalLT_trichotomy {a b : ℕ}
    (ha : ValidOrdinalCode a) (hb : ValidOrdinalCode b) :
    OrdinalLT a b ∨ a = b ∨ OrdinalLT b a := by
  rcases lt_trichotomy (denote a) (denote b) with h | h | h
  · exact Or.inl ((ordinalLT_iff a b).mpr ⟨ha, hb, h⟩)
  · exact Or.inr <| Or.inl <| denote_injective_on_valid ha hb h
  · exact Or.inr <| Or.inr <| (ordinalLT_iff b a).mpr ⟨hb, ha, h⟩

/-! ## Addition -/

@[simp] theorem zeroCode_add (a : ℕ) : addCode zeroCode a = a := by
  simp [zeroCode, addCode]

theorem add_zeroCode {a : ℕ} (ha : ValidOrdinalCode a) :
    addCode a zeroCode = a := by
  apply denote_injective_on_valid (addCode_valid ha zeroCode_valid) ha
  rw [denote_addCode ha zeroCode_valid, denote_zeroCode, add_zero]

theorem addCode_assoc {a b c : ℕ}
    (ha : ValidOrdinalCode a) (hb : ValidOrdinalCode b)
    (hc : ValidOrdinalCode c) :
    addCode (addCode a b) c = addCode a (addCode b c) := by
  apply denote_injective_on_valid
    (addCode_valid (addCode_valid ha hb) hc)
    (addCode_valid ha (addCode_valid hb hc))
  rw [denote_addCode (addCode_valid ha hb) hc,
    denote_addCode ha hb, denote_addCode ha (addCode_valid hb hc),
    denote_addCode hb hc, add_assoc]

/-! ## Multiplication -/

@[simp] theorem zeroCode_mul (a : ℕ) : mulCode zeroCode a = zeroCode := by
  simp [zeroCode, mulCode]

@[simp] theorem mul_zeroCode (a : ℕ) : mulCode a zeroCode = zeroCode := by
  simp [zeroCode, mulCode]

theorem oneCode_mul {a : ℕ} (ha : ValidOrdinalCode a) :
    mulCode oneCode a = a := by
  apply denote_injective_on_valid (mulCode_valid oneCode_valid ha) ha
  rw [denote_mulCode oneCode_valid ha, denote_oneCode, one_mul]

theorem mul_oneCode {a : ℕ} (ha : ValidOrdinalCode a) :
    mulCode a oneCode = a := by
  apply denote_injective_on_valid (mulCode_valid ha oneCode_valid) ha
  rw [denote_mulCode ha oneCode_valid, denote_oneCode, mul_one]

theorem mulCode_assoc {a b c : ℕ}
    (ha : ValidOrdinalCode a) (hb : ValidOrdinalCode b)
    (hc : ValidOrdinalCode c) :
    mulCode (mulCode a b) c = mulCode a (mulCode b c) := by
  apply denote_injective_on_valid
    (mulCode_valid (mulCode_valid ha hb) hc)
    (mulCode_valid ha (mulCode_valid hb hc))
  rw [denote_mulCode (mulCode_valid ha hb) hc,
    denote_mulCode ha hb, denote_mulCode ha (mulCode_valid hb hc),
    denote_mulCode hb hc, mul_assoc]

/-- Ordinal multiplication distributes over a sum in its right argument. -/
theorem mulCode_addCode {a b c : ℕ}
    (ha : ValidOrdinalCode a) (hb : ValidOrdinalCode b)
    (hc : ValidOrdinalCode c) :
    mulCode a (addCode b c) =
      addCode (mulCode a b) (mulCode a c) := by
  apply denote_injective_on_valid
    (mulCode_valid ha (addCode_valid hb hc))
    (addCode_valid (mulCode_valid ha hb) (mulCode_valid ha hc))
  rw [denote_mulCode ha (addCode_valid hb hc), denote_addCode hb hc,
    denote_addCode (mulCode_valid ha hb) (mulCode_valid ha hc),
    denote_mulCode ha hb, denote_mulCode ha hc, left_distrib]

/-! ## Exponentiation -/

theorem pow_zeroCode {a : ℕ} (ha : ValidOrdinalCode a) :
    powCode a zeroCode = oneCode := by
  apply denote_injective_on_valid (powCode_valid ha zeroCode_valid) oneCode_valid
  rw [denote_powCode ha zeroCode_valid, denote_zeroCode,
    denote_oneCode, opow_zero]

theorem pow_oneCode {a : ℕ} (ha : ValidOrdinalCode a) :
    powCode a oneCode = a := by
  apply denote_injective_on_valid (powCode_valid ha oneCode_valid) ha
  rw [denote_powCode ha oneCode_valid, denote_oneCode, opow_one]

/-- `0^0 = 1` is the convention inherited from ordinal exponentiation. -/
@[simp] theorem zeroCode_pow_zeroCode :
    powCode zeroCode zeroCode = oneCode := pow_zeroCode zeroCode_valid

theorem powCode_addCode {a b c : ℕ}
    (ha : ValidOrdinalCode a) (hb : ValidOrdinalCode b)
    (hc : ValidOrdinalCode c) :
    powCode a (addCode b c) =
      mulCode (powCode a b) (powCode a c) := by
  apply denote_injective_on_valid
    (powCode_valid ha (addCode_valid hb hc))
    (mulCode_valid (powCode_valid ha hb) (powCode_valid ha hc))
  rw [denote_powCode ha (addCode_valid hb hc), denote_addCode hb hc,
    denote_mulCode (powCode_valid ha hb) (powCode_valid ha hc),
    denote_powCode ha hb, denote_powCode ha hc, opow_add]

theorem powCode_mulCode {a b c : ℕ}
    (ha : ValidOrdinalCode a) (hb : ValidOrdinalCode b)
    (hc : ValidOrdinalCode c) :
    powCode (powCode a b) c = powCode a (mulCode b c) := by
  apply denote_injective_on_valid
    (powCode_valid (powCode_valid ha hb) hc)
    (powCode_valid ha (mulCode_valid hb hc))
  rw [denote_powCode (powCode_valid ha hb) hc, denote_powCode ha hb,
    denote_powCode ha (mulCode_valid hb hc), denote_mulCode hb hc,
    opow_mul]

end PAListCoding.EpsilonZero
