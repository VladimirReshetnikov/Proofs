import PAListCoding.EpsilonZero
import Foundation.FirstOrder.Arithmetic.R0.Representation
import Mathlib.Computability.Primrec.List

/-!
# PA formula witnesses for epsilon-zero ordinal codes

This module uses Foundation's arithmetization theorem for partial-recursive
functions.  The first section records the small computability boundary needed
to apply that theorem to the explicit pairing code from `EpsilonZero`.
-/

namespace PAListCoding.EpsilonZero

open LO FirstOrder
open LO.FirstOrder.Arithmetic

/-!
Give `ONote` the primitive-recursive presentation induced by `codeEquiv`.
This is a local implementation detail: the public natural code remains the
explicit nested-pair code, rather than an opaque `Encodable` number.
-/
local instance : Primcodable ONote := Primcodable.ofEquiv ℕ codeEquiv

private theorem encode_primrec : Primrec encode := by
  exact Primrec.of_equiv (e := codeEquiv)

private theorem decode_primrec : Primrec decode := by
  exact Primrec.of_equiv_symm (e := codeEquiv)

/-- Raw payload below the positive-node tag. -/
private def payload (o : ONote) : ℕ := (encode o).pred

/-- Exponent child of a raw node; its value at zero is harmless. -/
private def exponentPart (o : ONote) : ONote :=
  decode (payload o).unpair.1

/-- Stored coefficient-minus-one of a raw node. -/
private def coefficientPred (o : ONote) : ℕ :=
  (payload o).unpair.2.unpair.1

/-- Tail child of a raw node; its value at zero is harmless. -/
private def tailPart (o : ONote) : ONote :=
  decode (payload o).unpair.2.unpair.2

private theorem payload_primrec : Primrec payload := by
  exact Primrec.pred.comp encode_primrec

private theorem payload_unpair_primrec : Primrec (fun o => (payload o).unpair) := by
  exact Primrec.unpair.comp payload_primrec

private theorem exponentPart_primrec : Primrec exponentPart := by
  exact decode_primrec.comp (Primrec.fst.comp payload_unpair_primrec)

private theorem payload_right_unpair_primrec :
    Primrec (fun o => (payload o).unpair.2.unpair) := by
  exact Primrec.unpair.comp (Primrec.snd.comp payload_unpair_primrec)

private theorem coefficientPred_primrec : Primrec coefficientPred := by
  exact Primrec.fst.comp payload_right_unpair_primrec

private theorem tailPart_primrec : Primrec tailPart := by
  exact decode_primrec.comp (Primrec.snd.comp payload_right_unpair_primrec)

@[simp] private theorem exponentPart_oadd (e : ONote) (n : ℕ+) (a : ONote) :
    exponentPart (.oadd e n a) = e := by
  simp [exponentPart, payload, encode]

@[simp] private theorem coefficientPred_oadd (e : ONote) (n : ℕ+) (a : ONote) :
    coefficientPred (.oadd e n a) = n.natPred := by
  simp [coefficientPred, payload, encode]

@[simp] private theorem tailPart_oadd (e : ONote) (n : ℕ+) (a : ONote) :
    tailPart (.oadd e n a) = a := by
  simp [tailPart, payload, encode]

/-- Immediate recursive children of a raw notation. -/
private def children : ONote → List ONote
  | 0 => []
  | .oadd e _ a => [e, a]

private theorem children_eq (o : ONote) :
    children o = if o = 0 then [] else [exponentPart o, tailPart o] := by
  cases o <;> simp [children]

private theorem children_primrec : Primrec children := by
  apply Primrec.of_eq
    (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const (0 : ONote)))
      (Primrec.const [])
      (Primrec.list_cons.comp exponentPart_primrec
        (Primrec.list_cons.comp tailPart_primrec (Primrec.const []))))
  intro o
  exact (children_eq o).symm

private theorem child_encode_lt {o child : ONote} (h : child ∈ children o) :
    encode child < encode o := by
  cases o with
  | zero => simp [children] at h
  | oadd e n a =>
      simp [children] at h
      rcases h with he | ha
      · rw [he]
        simpa [encode] using
          (Nat.left_le_pair (encode e) (Nat.pair n.natPred (encode a))).trans_lt
            (Nat.lt_succ_self _)
      · rw [ha]
        simpa [encode] using
          ((Nat.right_le_pair n.natPred (encode a)).trans
            (Nat.right_le_pair (encode e) (Nat.pair n.natPred (encode a)))).trans_lt
              (Nat.lt_succ_self _)

/-!
`nat_omega_rec'` is Mathlib's primitive-recursive well-founded recursion
combinator.  The explicit ordinal code itself is a decreasing measure for
both immediate subterms, so every ordinary structural recursion on `ONote`
can be discharged through this one lemma.
-/
private theorem onote_rec_primrec {σ : Type*} [Primcodable σ]
    (f : ONote → σ) (g : ONote → List σ → Option σ)
    (hg : Primrec₂ g)
    (H : ∀ o, g o ((children o).map f) = some (f o)) :
    Primrec f := by
  exact Primrec.nat_omega_rec' f encode_primrec children_primrec hg
    (fun _ _ h => child_encode_lt h) H

/-! ## Primitive-recursive comparison -/

/- `Ordering` is finite but has no library `Primcodable` instance.  This
transparent three-value equivalence is enough for the recursion compiler. -/
private def orderingEquivOptionBool : Ordering ≃ Option Bool where
  toFun
    | .lt => none
    | .eq => some false
    | .gt => some true
  invFun
    | none => .lt
    | some false => .eq
    | some true => .gt
  left_inv x := by cases x <;> rfl
  right_inv
    | none => rfl
    | some false => rfl
    | some true => rfl

local instance : Primcodable Ordering :=
  Primcodable.ofEquiv (Option Bool) orderingEquivOptionBool

private def natCmp (m n : ℕ) : Ordering :=
  if m < n then .lt else if m = n then .eq else .gt

private theorem natCmp_primrec : Primrec₂ natCmp := by
  exact Primrec.ite Primrec.nat_lt (Primrec₂.const Ordering.lt)
    (Primrec.ite Primrec.eq (Primrec₂.const Ordering.eq)
      (Primrec₂.const Ordering.gt))

@[simp] private theorem natCmp_eq_cmp (m n : ℕ) : natCmp m n = _root_.cmp m n := by
  by_cases hlt : m < n
  · simp [natCmp, _root_.cmp, cmpUsing, hlt]
  by_cases heq : m = n
  · subst n
    simp [natCmp, _root_.cmp, cmpUsing]
  · have hgt : n < m := lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm heq)
    simp [natCmp, _root_.cmp, cmpUsing, hlt, heq, hgt]

private theorem orderingThen_primrec : Primrec₂ Ordering.then := by
  have h : Primrec (fun p : Ordering × Ordering =>
      if p.1 = Ordering.eq then p.2 else p.1) :=
    Primrec.ite
      (Primrec.eq.comp Primrec.fst (Primrec.const Ordering.eq))
      Primrec.snd Primrec.fst
  have h₂ : Primrec₂ (fun a b : Ordering =>
      if a = Ordering.eq then b else a) := by
    change Primrec (fun p : Ordering × Ordering =>
      if p.1 = Ordering.eq then p.2 else p.1)
    exact h
  apply Primrec₂.of_eq h₂
  intro a b
  cases a <;> rfl

@[simp] private theorem cmp_natPred (m n : ℕ+) :
    _root_.cmp m.natPred n.natPred = _root_.cmp (m : ℕ) (n : ℕ) := by
  rw [← PNat.natPred_add_one m, ← PNat.natPred_add_one n]
  exact (cmp_add_right m.natPred n.natPred 1).symm

/-- The two recursive calls made when comparing nonzero notations. -/
private def cmpChildren (p : ONote × ONote) : List (ONote × ONote) :=
  if p.1 = 0 then []
  else if p.2 = 0 then []
  else
    [(exponentPart p.1, exponentPart p.2),
      (tailPart p.1, tailPart p.2)]

private theorem cmpChildren_primrec : Primrec cmpChildren := by
  exact Primrec.ite
    (Primrec.eq.comp Primrec.fst (Primrec.const (0 : ONote)))
    (Primrec.const [])
    (Primrec.ite
      (Primrec.eq.comp Primrec.snd (Primrec.const (0 : ONote)))
      (Primrec.const [])
      (Primrec.list_cons.comp
        (Primrec.pair
          (exponentPart_primrec.comp Primrec.fst)
          (exponentPart_primrec.comp Primrec.snd))
        (Primrec.list_cons.comp
          (Primrec.pair
            (tailPart_primrec.comp Primrec.fst)
            (tailPart_primrec.comp Primrec.snd))
          (Primrec.const []))))

private def cmpMeasure (p : ONote × ONote) : ℕ :=
  Nat.pair (encode p.1) (encode p.2)

private theorem cmpMeasure_primrec : Primrec cmpMeasure := by
  exact Primrec₂.natPair.comp
    (encode_primrec.comp Primrec.fst)
    (encode_primrec.comp Primrec.snd)

/-- One layer of the comparison recursion, consuming the recursive answers. -/
private def cmpStep (p : ONote × ONote) (rs : List Ordering) : Option Ordering :=
  if p.1 = 0 then some (if p.2 = 0 then .eq else .lt)
  else if p.2 = 0 then some .gt
  else
    some ((rs.getD 0 .eq).then
      ((natCmp (coefficientPred p.1) (coefficientPred p.2)).then
        (rs.getD 1 .eq)))

private theorem cmpStep_primrec : Primrec₂ cmpStep := by
  let leftNote : Primrec (fun x : (ONote × ONote) × List Ordering => x.1.1) :=
    Primrec.fst.comp Primrec.fst
  let rightNote : Primrec (fun x : (ONote × ONote) × List Ordering => x.1.2) :=
    Primrec.snd.comp Primrec.fst
  let answers : Primrec (fun x : (ONote × ONote) × List Ordering => x.2) := Primrec.snd
  let r₀ : Primrec (fun x : (ONote × ONote) × List Ordering => x.2.getD 0 Ordering.eq) :=
    (Primrec.list_getD Ordering.eq).comp answers (Primrec.const 0)
  let r₁ : Primrec (fun x : (ONote × ONote) × List Ordering => x.2.getD 1 Ordering.eq) :=
    (Primrec.list_getD Ordering.eq).comp answers (Primrec.const 1)
  let coeffCmp : Primrec (fun x : (ONote × ONote) × List Ordering =>
      natCmp (coefficientPred x.1.1) (coefficientPred x.1.2)) :=
    natCmp_primrec.comp
      (coefficientPred_primrec.comp leftNote)
      (coefficientPred_primrec.comp rightNote)
  let tailCmp : Primrec (fun x : (ONote × ONote) × List Ordering =>
      (natCmp (coefficientPred x.1.1) (coefficientPred x.1.2)).then
        (x.2.getD 1 Ordering.eq)) :=
    orderingThen_primrec.comp coeffCmp r₁
  let result : Primrec (fun x : (ONote × ONote) × List Ordering =>
      (x.2.getD 0 Ordering.eq).then
        ((natCmp (coefficientPred x.1.1) (coefficientPred x.1.2)).then
          (x.2.getD 1 Ordering.eq))) :=
    orderingThen_primrec.comp r₀ tailCmp
  exact Primrec.ite
    (Primrec.eq.comp leftNote (Primrec.const (0 : ONote)))
    (Primrec.option_some.comp <| Primrec.ite
      (Primrec.eq.comp rightNote (Primrec.const (0 : ONote)))
      (Primrec.const Ordering.eq) (Primrec.const Ordering.lt))
    (Primrec.ite
      (Primrec.eq.comp rightNote (Primrec.const (0 : ONote)))
      (Primrec.const (some Ordering.gt))
      (Primrec.option_some.comp result))

private theorem cmp_child_measure {p child : ONote × ONote}
    (h : child ∈ cmpChildren p) : cmpMeasure child < cmpMeasure p := by
  rcases p with ⟨o₁, o₂⟩
  cases o₁ with
  | zero => simp [cmpChildren] at h
  | oadd e₁ n₁ a₁ =>
      cases o₂ with
      | zero => simp [cmpChildren] at h
      | oadd e₂ n₂ a₂ =>
          simp [cmpChildren] at h
          rcases h with he | ha
          · rw [he]
            exact (Nat.pair_lt_pair_left _
              (child_encode_lt (o := .oadd e₁ n₁ a₁) (by simp [children]))).trans
              (Nat.pair_lt_pair_right _
                (child_encode_lt (o := .oadd e₂ n₂ a₂) (by simp [children])))
          · rw [ha]
            exact (Nat.pair_lt_pair_left _
              (child_encode_lt (o := .oadd e₁ n₁ a₁) (by simp [children]))).trans
              (Nat.pair_lt_pair_right _
                (child_encode_lt (o := .oadd e₂ n₂ a₂) (by simp [children])))

private theorem onoteCmp_primrec :
    Primrec (fun p : ONote × ONote => ONote.cmp p.1 p.2) := by
  apply Primrec.nat_omega_rec'
    (fun p : ONote × ONote => ONote.cmp p.1 p.2)
    cmpMeasure_primrec cmpChildren_primrec cmpStep_primrec
    (fun _ _ h => cmp_child_measure h)
  rintro ⟨o₁, o₂⟩
  cases o₁ <;> cases o₂ <;>
    simp [cmpStep, cmpChildren, ONote.cmp, natCmp_eq_cmp]

private theorem onoteCmp₂_primrec : Primrec₂ ONote.cmp := by
  exact onoteCmp_primrec

end PAListCoding.EpsilonZero
