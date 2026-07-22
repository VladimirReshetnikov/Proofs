import PAListCoding.NumberTheory
import Mathlib.SetTheory.Ordinal.Notation
import Mathlib.SetTheory.Ordinal.Veblen

/-!
# Natural-number codes for ordinals below epsilon zero

Mathlib's `ONote` type is the raw syntax of hereditary Cantor normal forms:
`ONote.oadd e n a` denotes `omega ^ e * n + a`, where `n` is positive.
This file gives that syntax a particularly small natural-number code.  Zero
has code zero, while a nonzero node uses two nested Cantor pairs:

```
code (oadd e n a) = pair (code e) (pair (n - 1) (code a)) + 1.
```

Subtracting one before pairing reserves code zero for the zero notation and
stores a positive coefficient without wasting a tag.  Both child codes of a
positive node are strictly smaller than the whole code, so decoding is a
course-of-values recursion.  Every natural number decodes to one raw `ONote`;
the predicate `ValidOrdinalCode` then selects exactly the normal forms.
-/

namespace PAListCoding.EpsilonZero

open Ordinal
open scoped Ordinal

/-! ## The raw coding bijection -/

/-- Canonical natural-number code of a raw ordinal notation. -/
def encode : ONote → ℕ
  | 0 => 0
  | .oadd e n a => Nat.pair (encode e) (Nat.pair n.natPred (encode a)) + 1

/--
Decode every natural number as a raw ordinal notation.

For a positive input `c + 1`, both recursive arguments are at most `c`.
The explicit inequalities below are the reason for the outer `+ 1` in the
encoding: they make termination independent of any semantic normality fact.
-/
def decode : (c : ℕ) → ONote
  | 0 => 0
  | c + 1 =>
      let outer := c.unpair
      let inner := outer.2.unpair
      .oadd (decode outer.1) inner.1.succPNat (decode inner.2)
termination_by c => c
decreasing_by
  · exact (Nat.unpair_left_le c).trans_lt (Nat.lt_succ_self c)
  · exact ((Nat.unpair_right_le outer.2).trans
      (Nat.unpair_right_le c)).trans_lt (Nat.lt_succ_self c)

@[simp] theorem decode_zero : decode 0 = 0 := by simp [decode]

@[simp] theorem decode_encode : ∀ o : ONote, decode (encode o) = o
  | 0 => by simp [encode]
  | .oadd e n a => by
      simp [encode, decode, decode_encode e, decode_encode a]

@[simp] theorem encode_decode (c : ℕ) : encode (decode c) = c := by
  induction c using Nat.strong_induction_on with
  | h c ih =>
      cases c with
      | zero => simp [encode]
      | succ c =>
          have he : c.unpair.1 < c + 1 :=
            (Nat.unpair_left_le c).trans_lt (Nat.lt_succ_self c)
          have ha : c.unpair.2.unpair.2 < c + 1 :=
            ((Nat.unpair_right_le c.unpair.2).trans
              (Nat.unpair_right_le c)).trans_lt (Nat.lt_succ_self c)
          simp [decode, encode, ih _ he, ih _ ha]

/-- Raw ordinal notations and naturals are in canonical bijection. -/
def codeEquiv : ONote ≃ ℕ where
  toFun := encode
  invFun := decode
  left_inv := decode_encode
  right_inv := encode_decode

theorem encode_injective : Function.Injective encode := codeEquiv.injective

theorem decode_injective : Function.Injective decode := codeEquiv.symm.injective

/-! ## Valid codes and their ordinal meaning -/

/-- A code is valid exactly when its decoded hereditary CNF is normal. -/
def ValidOrdinalCode (c : ℕ) : Prop := ONote.NF (decode c)

/-- The set-theoretic ordinal denoted by a raw code. -/
noncomputable def denote (c : ℕ) : Ordinal := ONote.repr (decode c)

@[simp] theorem valid_encode_iff (o : ONote) :
    ValidOrdinalCode (encode o) ↔ ONote.NF o := by
  simp [ValidOrdinalCode]

@[simp] theorem denote_encode (o : ONote) : denote (encode o) = ONote.repr o := by
  simp [denote]

/-- The code of a Mathlib normal-form notation. -/
def codeOf (o : NONote) : ℕ := encode o.1

@[simp] theorem codeOf_valid (o : NONote) : ValidOrdinalCode (codeOf o) := by
  simpa [codeOf, ValidOrdinalCode] using o.2

@[simp] theorem decode_codeOf (o : NONote) : decode (codeOf o) = o.1 := by
  simp [codeOf]

@[simp] theorem denote_codeOf (o : NONote) : denote (codeOf o) = NONote.repr o := by
  simp [denote, codeOf, NONote.repr]

/-- Valid natural codes are equivalent to Mathlib's normal ordinal notations. -/
def validCodeEquiv : {c : ℕ // ValidOrdinalCode c} ≃ NONote where
  toFun c := ⟨decode c.1, c.2⟩
  invFun o := ⟨codeOf o, codeOf_valid o⟩
  left_inv c := by
    apply Subtype.ext
    simp [codeOf]
  right_inv o := by
    apply Subtype.ext
    simp [codeOf]

theorem denote_injective_on_valid {a b : ℕ}
    (ha : ValidOrdinalCode a) (hb : ValidOrdinalCode b)
    (h : denote a = denote b) : a = b := by
  haveI : ONote.NF (decode a) := ha
  haveI : ONote.NF (decode b) := hb
  apply decode_injective
  exact ONote.repr_inj.mp h

/-!
Every normal notation lies below a finite tower of powers of `omega`.  This
small induction supplies the missing explicit bridge between Mathlib's
`NONote` documentation and its set-theoretic epsilon-zero development.
-/
private theorem nf_exists_iterate_bound : ∀ o : ONote, ONote.NF o →
    ∃ k : ℕ, ONote.repr o < (fun x : Ordinal ↦ ω ^ x)^[k] 0
  | 0, _ => ⟨1, by simp⟩
  | .oadd e n a, h => by
      obtain ⟨k, hk⟩ := nf_exists_iterate_bound e h.fst
      refine ⟨k + 1, ?_⟩
      have below : ONote.NFBelow (.oadd e n a)
          ((fun x : Ordinal ↦ ω ^ x)^[k] 0) :=
        ONote.NFBelow.oadd h.fst h.snd' hk
      simpa [Function.iterate_succ_apply'] using below.repr_lt

/-- Every valid natural code denotes a set-theoretic ordinal below `epsilon zero`. -/
theorem valid_denote_lt_epsilonZero {c : ℕ} (hc : ValidOrdinalCode c) :
    denote c < ε₀ := by
  rw [Ordinal.lt_epsilon_zero]
  exact nf_exists_iterate_bound (decode c) hc

/-! ## Canonical arithmetic on codes -/

/-- Canonical output code for ordinal addition. -/
def addCode (a b : ℕ) : ℕ := encode (decode a + decode b)

/-- Canonical output code for ordinal multiplication. -/
def mulCode (a b : ℕ) : ℕ := encode (decode a * decode b)

/-- Canonical output code for ordinal exponentiation. -/
def powCode (a b : ℕ) : ℕ := encode (decode a ^ decode b)

/-- Strict comparison of valid ordinal codes, computed by `ONote.cmp`. -/
def OrdinalLT (a b : ℕ) : Prop :=
  ValidOrdinalCode a ∧ ValidOrdinalCode b ∧
    ONote.cmp (decode a) (decode b) = Ordering.lt

/-- Graph of canonical ordinal addition on valid codes; arguments are `(result, left, right)`. -/
def OrdinalAdd (z a b : ℕ) : Prop :=
  ValidOrdinalCode a ∧ ValidOrdinalCode b ∧ z = addCode a b

/-- Graph of canonical ordinal multiplication on valid codes. -/
def OrdinalMul (z a b : ℕ) : Prop :=
  ValidOrdinalCode a ∧ ValidOrdinalCode b ∧ z = mulCode a b

/-- Graph of canonical ordinal exponentiation on valid codes. -/
def OrdinalPow (z a b : ℕ) : Prop :=
  ValidOrdinalCode a ∧ ValidOrdinalCode b ∧ z = powCode a b

/-- Computational comparison agrees with comparison of the denoted ordinals. -/
theorem ordinalLT_iff (a b : ℕ) :
    OrdinalLT a b ↔
      ValidOrdinalCode a ∧ ValidOrdinalCode b ∧ denote a < denote b := by
  constructor
  · rintro ⟨ha, hb, hcmp⟩
    haveI : ONote.NF (decode a) := ha
    haveI : ONote.NF (decode b) := hb
    refine ⟨ha, hb, ?_⟩
    have compares := ONote.cmp_compares (decode a) (decode b)
    simpa [denote, ONote.lt_def] using compares.eq_lt.mp hcmp
  · rintro ⟨ha, hb, hlt⟩
    haveI : ONote.NF (decode a) := ha
    haveI : ONote.NF (decode b) := hb
    refine ⟨ha, hb, ?_⟩
    have compares := ONote.cmp_compares (decode a) (decode b)
    apply compares.eq_lt.mpr
    simpa [denote, ONote.lt_def] using hlt

@[simp] theorem ordinalLT_codeOf_iff (a b : NONote) :
    OrdinalLT (codeOf a) (codeOf b) ↔ a < b := by
  rw [ordinalLT_iff]
  simp only [codeOf_valid, denote_codeOf, true_and]
  rfl

@[simp] theorem decode_addCode (a b : ℕ) :
    decode (addCode a b) = decode a + decode b := by
  simp [addCode]

@[simp] theorem decode_mulCode (a b : ℕ) :
    decode (mulCode a b) = decode a * decode b := by
  simp [mulCode]

@[simp] theorem decode_powCode (a b : ℕ) :
    decode (powCode a b) = decode a ^ decode b := by
  simp [powCode]

theorem addCode_valid {a b : ℕ}
    (ha : ValidOrdinalCode a) (hb : ValidOrdinalCode b) :
    ValidOrdinalCode (addCode a b) := by
  haveI : ONote.NF (decode a) := ha
  haveI : ONote.NF (decode b) := hb
  simp [ValidOrdinalCode]
  infer_instance

theorem mulCode_valid {a b : ℕ}
    (ha : ValidOrdinalCode a) (hb : ValidOrdinalCode b) :
    ValidOrdinalCode (mulCode a b) := by
  haveI : ONote.NF (decode a) := ha
  haveI : ONote.NF (decode b) := hb
  simp [ValidOrdinalCode]
  infer_instance

theorem powCode_valid {a b : ℕ}
    (ha : ValidOrdinalCode a) (hb : ValidOrdinalCode b) :
    ValidOrdinalCode (powCode a b) := by
  haveI : ONote.NF (decode a) := ha
  haveI : ONote.NF (decode b) := hb
  simp [ValidOrdinalCode]
  infer_instance

@[simp] theorem denote_addCode {a b : ℕ}
    (ha : ValidOrdinalCode a) (hb : ValidOrdinalCode b) :
    denote (addCode a b) = denote a + denote b := by
  haveI : ONote.NF (decode a) := ha
  haveI : ONote.NF (decode b) := hb
  simp [denote, addCode, ONote.repr_add]

@[simp] theorem denote_mulCode {a b : ℕ}
    (ha : ValidOrdinalCode a) (hb : ValidOrdinalCode b) :
    denote (mulCode a b) = denote a * denote b := by
  haveI : ONote.NF (decode a) := ha
  haveI : ONote.NF (decode b) := hb
  simp [denote, mulCode, ONote.repr_mul]

@[simp] theorem denote_powCode {a b : ℕ}
    (ha : ValidOrdinalCode a) (hb : ValidOrdinalCode b) :
    denote (powCode a b) = denote a ^ denote b := by
  haveI : ONote.NF (decode a) := ha
  haveI : ONote.NF (decode b) := hb
  simp [denote, powCode, ONote.repr_opow]

theorem ordinalAdd_existsUnique (a b : ℕ)
    (ha : ValidOrdinalCode a) (hb : ValidOrdinalCode b) :
    ∃! z, OrdinalAdd z a b := by
  exact ⟨addCode a b, ⟨ha, hb, rfl⟩, fun z hz ↦ hz.2.2⟩

theorem ordinalMul_existsUnique (a b : ℕ)
    (ha : ValidOrdinalCode a) (hb : ValidOrdinalCode b) :
    ∃! z, OrdinalMul z a b := by
  exact ⟨mulCode a b, ⟨ha, hb, rfl⟩, fun z hz ↦ hz.2.2⟩

theorem ordinalPow_existsUnique (a b : ℕ)
    (ha : ValidOrdinalCode a) (hb : ValidOrdinalCode b) :
    ∃! z, OrdinalPow z a b := by
  exact ⟨powCode a b, ⟨ha, hb, rfl⟩, fun z hz ↦ hz.2.2⟩

/-! ### Extensional graph characterizations -/

theorem ordinalAdd_iff (z a b : ℕ) :
    OrdinalAdd z a b ↔
      ValidOrdinalCode a ∧ ValidOrdinalCode b ∧ ValidOrdinalCode z ∧
        denote z = denote a + denote b := by
  constructor
  · rintro ⟨ha, hb, rfl⟩
    exact ⟨ha, hb, addCode_valid ha hb, denote_addCode ha hb⟩
  · rintro ⟨ha, hb, hz, hvalue⟩
    refine ⟨ha, hb, denote_injective_on_valid hz (addCode_valid ha hb) ?_⟩
    exact hvalue.trans (denote_addCode ha hb).symm

theorem ordinalMul_iff (z a b : ℕ) :
    OrdinalMul z a b ↔
      ValidOrdinalCode a ∧ ValidOrdinalCode b ∧ ValidOrdinalCode z ∧
        denote z = denote a * denote b := by
  constructor
  · rintro ⟨ha, hb, rfl⟩
    exact ⟨ha, hb, mulCode_valid ha hb, denote_mulCode ha hb⟩
  · rintro ⟨ha, hb, hz, hvalue⟩
    refine ⟨ha, hb, denote_injective_on_valid hz (mulCode_valid ha hb) ?_⟩
    exact hvalue.trans (denote_mulCode ha hb).symm

theorem ordinalPow_iff (z a b : ℕ) :
    OrdinalPow z a b ↔
      ValidOrdinalCode a ∧ ValidOrdinalCode b ∧ ValidOrdinalCode z ∧
        denote z = denote a ^ denote b := by
  constructor
  · rintro ⟨ha, hb, rfl⟩
    exact ⟨ha, hb, powCode_valid ha hb, denote_powCode ha hb⟩
  · rintro ⟨ha, hb, hz, hvalue⟩
    refine ⟨ha, hb, denote_injective_on_valid hz (powCode_valid ha hb) ?_⟩
    exact hvalue.trans (denote_powCode ha hb).symm

@[simp] theorem addCode_codeOf (a b : NONote) :
    addCode (codeOf a) (codeOf b) = codeOf (a + b) := by
  simp only [addCode, codeOf, decode_encode]
  rfl

@[simp] theorem mulCode_codeOf (a b : NONote) :
    mulCode (codeOf a) (codeOf b) = codeOf (a * b) := by
  simp only [mulCode, codeOf, decode_encode]
  rfl

@[simp] theorem powCode_codeOf (a b : NONote) :
    powCode (codeOf a) (codeOf b) = codeOf (NONote.opow a b) := by
  simp only [powCode, codeOf, decode_encode]
  rfl

end PAListCoding.EpsilonZero
