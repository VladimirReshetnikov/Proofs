import Foundation.FirstOrder.Arithmetic.HFS

/-!
# Natural-number codes for finite lists

Foundation represents a finite sequence internally as the graph of a function
whose domain is an initial segment.  In the standard natural-number model this
graph is an Ackermann-coded hereditary finite set, hence a single natural
number.  The code below specializes Foundation's fixed-length `vecToSeq`
constructor to an ordinary external `List Nat`.
-/

namespace PAListCoding

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.HierarchySymbol

/-- The code of an external finite list in the standard model of arithmetic. -/
noncomputable def encode (xs : List ℕ) : ℕ :=
  vecToSeq (V := ℕ) (fun i : Fin xs.length => xs.get i)

@[simp] theorem encode_valid (xs : List ℕ) : Seq (encode xs) := by
  exact vecToSeq_seq _

@[simp] theorem encode_length (xs : List ℕ) : lh (encode xs) = xs.length := by
  simpa [encode] using
    (lh_vecToSeq (V := ℕ) (fun i : Fin xs.length => xs.get i))

theorem encode_nth (xs : List ℕ) (i : Fin xs.length) :
    znth (encode xs) i = xs.get i := by
  apply Seq.znth_eq_of_mem (encode_valid xs)
  simpa [encode] using
    (mem_vectoSeq (V := ℕ) (fun j : Fin xs.length => xs.get j) i)

/-- Equality of codes determines equality of the represented external lists. -/
theorem encode_injective : Function.Injective encode := by
  intro xs ys h
  have hlen : xs.length = ys.length := by
    simpa using congrArg lh h
  apply List.ext_get hlen
  intro i hi hj
  have hxi := encode_nth xs ⟨i, hi⟩
  have hyi := encode_nth ys ⟨i, hj⟩
  rw [h] at hxi
  exact hxi.symm.trans hyi

/-- Every valid standard code is the code of a unique external finite list. -/
theorem valid_iff_existsUnique_encode (p : ℕ) :
    Seq p ↔ ∃! xs : List ℕ, encode xs = p := by
  constructor
  · intro hp
    let xs : List ℕ := List.ofFn (fun i : Fin (lh p) => znth p i)
    have hcode : encode xs = p := by
      apply Seq.lh_ext (encode_valid xs) hp
      · simp [xs]
      · intro i x y hix hiy
        have hiCode : i < lh (encode xs) := (encode_valid xs).lt_lh_of_mem hix
        have hiP : i < lh p := hp.lt_lh_of_mem hiy
        have hx : x = znth (encode xs) i := by
          exact (encode_valid xs).isMapping.uniq hix
            ((encode_valid xs).znth hiCode)
        have hy : y = znth p i := by
          exact hp.isMapping.uniq hiy (hp.znth hiP)
        let ii : Fin xs.length := ⟨i, by simpa [xs] using hiP⟩
        have hii : (ii : ℕ) = i := by simp [ii]
        have hnth := encode_nth xs ii
        rw [hii] at hnth
        calc
          x = znth (encode xs) i := hx
          _ = znth p i := by simpa [xs] using hnth
          _ = y := hy.symm
    exact ExistsUnique.intro xs hcode (fun ys hys => encode_injective (hys.trans hcode.symm))
  · rintro ⟨xs, rfl, _⟩
    exact encode_valid xs

/-- A valid code has a unique decoded external list. -/
noncomputable def decode (p : ℕ) : List ℕ :=
  by
    classical
    exact if hp : Seq p then Classical.choose (valid_iff_existsUnique_encode p |>.mp hp) else []

theorem encode_decode {p : ℕ} (hp : Seq p) : encode (decode p) = p := by
  simp only [decode, dif_pos hp]
  exact (Classical.choose_spec (valid_iff_existsUnique_encode p |>.mp hp)).1

@[simp] theorem decode_encode (xs : List ℕ) : decode (encode xs) = xs := by
  apply encode_injective
  exact encode_decode (encode_valid xs)

/-- The actual formula saying that a number is a valid sequence code. -/
abbrev validFormula : ArithmeticSemisentence 1 := seqDef.val

@[simp] theorem validFormula_spec (p : ℕ) :
    validFormula.Evalb ![p] ↔ Seq p := by
  simpa [validFormula] using (seq_defined (V := ℕ)).iff ![p]

end PAListCoding
