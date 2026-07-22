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

/-! ## Primitive-recursive normal-form validity -/

private theorem nf_oadd_iff (e : ONote) (n : ℕ+) (a : ONote) :
    ONote.NF (.oadd e n a) ↔
      ONote.NF e ∧ ONote.NF a ∧ ONote.TopBelow e a := by
  constructor
  · intro h
    have he : ONote.NF e := h.fst
    haveI : ONote.NF e := he
    exact ⟨he, h.snd, (ONote.nfBelow_iff_topBelow.mp h.snd').2⟩
  · rintro ⟨he, ha, htop⟩
    haveI : ONote.NF e := he
    exact ONote.NF.oadd he n (ONote.nfBelow_iff_topBelow.mpr ⟨ha, htop⟩)

/-- One layer of the normal-form decision procedure. -/
private def nfStep (o : ONote) (rs : List Bool) : Option Bool :=
  if o = 0 then some true
  else some ((rs.getD 0 false) && (rs.getD 1 false) &&
    decide (ONote.TopBelow (exponentPart o) (tailPart o)))

private theorem topBelow_decide_primrec :
    Primrec₂ (fun b o : ONote => decide (ONote.TopBelow b o)) := by
  have h : Primrec (fun p : ONote × ONote =>
      if p.2 = 0 then true
      else decide (ONote.cmp (exponentPart p.2) p.1 = Ordering.lt)) :=
    Primrec.ite
      (Primrec.eq.comp Primrec.snd (Primrec.const (0 : ONote)))
      (Primrec.const true)
      (Primrec.eq.decide.comp
        (onoteCmp₂_primrec.comp
          (exponentPart_primrec.comp Primrec.snd) Primrec.fst)
        (Primrec.const Ordering.lt))
  have h₂ : Primrec₂ (fun b o : ONote =>
      if o = 0 then true
      else decide (ONote.cmp (exponentPart o) b = Ordering.lt)) := by
    change Primrec (fun p : ONote × ONote =>
      if p.2 = 0 then true
      else decide (ONote.cmp (exponentPart p.2) p.1 = Ordering.lt))
    exact h
  apply Primrec₂.of_eq h₂
  intro b o
  cases o <;> simp [ONote.TopBelow]

private theorem nfStep_primrec : Primrec₂ nfStep := by
  let term : Primrec (fun x : ONote × List Bool => x.1) := Primrec.fst
  let answers : Primrec (fun x : ONote × List Bool => x.2) := Primrec.snd
  let r₀ : Primrec (fun x : ONote × List Bool => x.2.getD 0 false) :=
    (Primrec.list_getD false).comp answers (Primrec.const 0)
  let r₁ : Primrec (fun x : ONote × List Bool => x.2.getD 1 false) :=
    (Primrec.list_getD false).comp answers (Primrec.const 1)
  let top : Primrec (fun x : ONote × List Bool =>
      decide (ONote.TopBelow (exponentPart x.1) (tailPart x.1))) :=
    topBelow_decide_primrec.comp
      (exponentPart_primrec.comp term)
      (tailPart_primrec.comp term)
  let body : Primrec (fun x : ONote × List Bool =>
      (x.2.getD 0 false) && (x.2.getD 1 false) &&
        decide (ONote.TopBelow (exponentPart x.1) (tailPart x.1))) :=
    Primrec.and.comp (Primrec.and.comp r₀ r₁) top
  exact Primrec.ite
    (Primrec.eq.comp Primrec.fst (Primrec.const (0 : ONote)))
    (Primrec.const (some true))
    (Primrec.option_some.comp body)

private theorem nf_decide_primrec :
    Primrec (fun o : ONote => decide (ONote.NF o)) := by
  apply onote_rec_primrec (fun o : ONote => decide (ONote.NF o)) nfStep nfStep_primrec
  intro o
  cases o with
  | zero =>
      have : ONote.NF (0 : ONote) := inferInstance
      simp [nfStep, this]
  | oadd e n a =>
      simp [nfStep, children, nf_oadd_iff, Bool.and_assoc]

private theorem validOrdinalCode_primrecPred :
    PrimrecPred ValidOrdinalCode := by
  letI : DecidablePred ValidOrdinalCode := fun c =>
    ONote.decidableNF (decode c)
  apply Primrec.primrecPred
  simpa [ValidOrdinalCode] using nf_decide_primrec.comp decode_primrec

private theorem ordinalLT_primrecRel : PrimrecRel OrdinalLT := by
  let validLeft : PrimrecPred (fun p : ℕ × ℕ => ValidOrdinalCode p.1) :=
    validOrdinalCode_primrecPred.comp Primrec.fst
  let validRight : PrimrecPred (fun p : ℕ × ℕ => ValidOrdinalCode p.2) :=
    validOrdinalCode_primrecPred.comp Primrec.snd
  let comparesLT : PrimrecPred (fun p : ℕ × ℕ =>
      ONote.cmp (decode p.1) (decode p.2) = Ordering.lt) :=
    Primrec.eq.comp
      (onoteCmp₂_primrec.comp
        (decode_primrec.comp Primrec.fst)
        (decode_primrec.comp Primrec.snd))
      (Primrec.const Ordering.lt)
  exact (validLeft.and (validRight.and comparesLT)).of_eq fun p => by
    simp [OrdinalLT]

/-! ## Primitive-recursive ordinal arithmetic -/

/-- Rebuild a raw node from the stored coefficient-minus-one. -/
private def mkNode (e : ONote) (q : ℕ × ONote) : ONote :=
  .oadd e q.1.succPNat q.2

private theorem mkNode_primrec : Primrec₂ mkNode := by
  have codePR : Primrec (fun p : ONote × (ℕ × ONote) =>
      Nat.pair (encode p.1) (Nat.pair p.2.1 (encode p.2.2)) + 1) :=
    Primrec.succ.comp <| Primrec₂.natPair.comp
      (encode_primrec.comp Primrec.fst)
      (Primrec₂.natPair.comp
        (Primrec.fst.comp Primrec.snd)
        (encode_primrec.comp (Primrec.snd.comp Primrec.snd)))
  have decoded : Primrec (fun p : ONote × (ℕ × ONote) =>
      decode (Nat.pair (encode p.1) (Nat.pair p.2.1 (encode p.2.2)) + 1)) :=
    decode_primrec.comp codePR
  have decoded₂ : Primrec₂ (fun (e : ONote) (q : ℕ × ONote) =>
      decode (Nat.pair (encode e) (Nat.pair q.1 (encode q.2)) + 1)) := by
    change Primrec (fun p : ONote × (ℕ × ONote) =>
      decode (Nat.pair (encode p.1) (Nat.pair p.2.1 (encode p.2.2)) + 1))
    exact decoded
  apply Primrec₂.of_eq decoded₂
  intro e q
  simpa [mkNode, encode] using decode_encode (.oadd e q.1.succPNat q.2)

@[simp] private theorem natPred_add (m n : ℕ+) :
    (m + n).natPred = m.natPred + n.natPred + 1 := by
  have hm := PNat.natPred_add_one m
  have hn := PNat.natPred_add_one n
  have hmn := PNat.natPred_add_one (m + n)
  simp only [PNat.add_coe] at hmn
  omega

@[simp] private theorem succPNat_natPred_add (m n : ℕ+) :
    (m.natPred + n.natPred + 1).succPNat = m + n := by
  rw [← natPred_add]
  exact PNat.succPNat_natPred _

/-! Addition recurses only through the tail of its left input. -/
private def addChildren (p : ONote × ONote) : List (ONote × ONote) :=
  if p.1 = 0 then [] else [(tailPart p.1, p.2)]

private theorem addChildren_primrec : Primrec addChildren := by
  exact Primrec.ite
    (Primrec.eq.comp Primrec.fst (Primrec.const (0 : ONote)))
    (Primrec.const [])
    (Primrec.list_cons.comp
      (Primrec.pair (tailPart_primrec.comp Primrec.fst) Primrec.snd)
      (Primrec.const []))

private def addStep (p : ONote × ONote) (rs : List ONote) : Option ONote :=
  if p.1 = 0 then some p.2
  else
    let r := rs.getD 0 0
    if r = 0 then
      some (mkNode (exponentPart p.1) (coefficientPred p.1, 0))
    else
      let c := ONote.cmp (exponentPart p.1) (exponentPart r)
      if c = Ordering.lt then some r
      else if c = Ordering.eq then
        some (mkNode (exponentPart p.1)
          (coefficientPred p.1 + coefficientPred r + 1, tailPart r))
      else some (mkNode (exponentPart p.1) (coefficientPred p.1, r))

private theorem addStep_primrec : Primrec₂ addStep := by
  let source : Primrec (fun x : (ONote × ONote) × List ONote => x.1.1) :=
    Primrec.fst.comp Primrec.fst
  let rightInput : Primrec (fun x : (ONote × ONote) × List ONote => x.1.2) :=
    Primrec.snd.comp Primrec.fst
  let answer : Primrec (fun x : (ONote × ONote) × List ONote => x.2.getD 0 0) :=
    (Primrec.list_getD 0).comp Primrec.snd (Primrec.const 0)
  let sourceExp : Primrec (fun x : (ONote × ONote) × List ONote =>
      exponentPart x.1.1) := exponentPart_primrec.comp source
  let sourceCoeff : Primrec (fun x : (ONote × ONote) × List ONote =>
      coefficientPred x.1.1) := coefficientPred_primrec.comp source
  let answerExp : Primrec (fun x : (ONote × ONote) × List ONote =>
      exponentPart (x.2.getD 0 0)) := exponentPart_primrec.comp answer
  let answerCoeff : Primrec (fun x : (ONote × ONote) × List ONote =>
      coefficientPred (x.2.getD 0 0)) := coefficientPred_primrec.comp answer
  let answerTail : Primrec (fun x : (ONote × ONote) × List ONote =>
      tailPart (x.2.getD 0 0)) := tailPart_primrec.comp answer
  let comparison : Primrec (fun x : (ONote × ONote) × List ONote =>
      ONote.cmp (exponentPart x.1.1) (exponentPart (x.2.getD 0 0))) :=
    onoteCmp₂_primrec.comp sourceExp answerExp
  let originalNode : Primrec (fun x : (ONote × ONote) × List ONote =>
      mkNode (exponentPart x.1.1) (coefficientPred x.1.1, 0)) :=
    mkNode_primrec.comp sourceExp
      (Primrec.pair sourceCoeff (Primrec.const 0))
  let addedCoeff : Primrec (fun x : (ONote × ONote) × List ONote =>
      coefficientPred x.1.1 + coefficientPred (x.2.getD 0 0) + 1) :=
    Primrec.succ.comp (Primrec.nat_add.comp sourceCoeff answerCoeff)
  let mergedNode : Primrec (fun x : (ONote × ONote) × List ONote =>
      mkNode (exponentPart x.1.1)
        (coefficientPred x.1.1 + coefficientPred (x.2.getD 0 0) + 1,
          tailPart (x.2.getD 0 0))) :=
    mkNode_primrec.comp sourceExp (Primrec.pair addedCoeff answerTail)
  let prependedNode : Primrec (fun x : (ONote × ONote) × List ONote =>
      mkNode (exponentPart x.1.1)
        (coefficientPred x.1.1, x.2.getD 0 0)) :=
    mkNode_primrec.comp sourceExp (Primrec.pair sourceCoeff answer)
  exact Primrec.ite
    (Primrec.eq.comp source (Primrec.const (0 : ONote)))
    (Primrec.option_some.comp rightInput)
    (Primrec.ite
      (Primrec.eq.comp answer (Primrec.const (0 : ONote)))
      (Primrec.option_some.comp originalNode)
      (Primrec.ite
        (Primrec.eq.comp comparison (Primrec.const Ordering.lt))
        (Primrec.option_some.comp answer)
        (Primrec.ite
          (Primrec.eq.comp comparison (Primrec.const Ordering.eq))
          (Primrec.option_some.comp mergedNode)
          (Primrec.option_some.comp prependedNode))))

private theorem add_child_measure {p child : ONote × ONote}
    (h : child ∈ addChildren p) : encode child.1 < encode p.1 := by
  rcases p with ⟨o, b⟩
  cases o with
  | zero => simp [addChildren] at h
  | oadd e n a =>
      simp [addChildren] at h
      rw [h]
      exact child_encode_lt (o := .oadd e n a) (by simp [children])

private theorem onoteAdd_primrec :
    Primrec (fun p : ONote × ONote => p.1 + p.2) := by
  apply Primrec.nat_omega_rec'
    (fun p : ONote × ONote => p.1 + p.2)
    (encode_primrec.comp Primrec.fst) addChildren_primrec addStep_primrec
    (fun _ _ h => add_child_measure h)
  rintro ⟨o, b⟩
  cases o with
  | zero => simp [addStep]
  | oadd e n a =>
      simp only [addChildren, addStep, ONote.oadd_add]
      cases hsum : a + b with
      | zero => simp [hsum, mkNode, ONote.addAux]
      | oadd e' n' a' =>
          cases hcmp : ONote.cmp e e' <;>
            simp [hsum, hcmp, ONote.addAux, mkNode]

private theorem onoteAdd₂_primrec : Primrec₂ (fun a b : ONote => a + b) := by
  exact onoteAdd_primrec

private theorem addCode_primrec₂ : Primrec₂ addCode := by
  exact encode_primrec.comp <|
    onoteAdd₂_primrec.comp₂
      (decode_primrec.comp₂ Primrec₂.left)
      (decode_primrec.comp₂ Primrec₂.right)

@[simp] private theorem natPred_mul (m n : ℕ+) :
    (m * n).natPred = m.natPred * n.natPred + m.natPred + n.natPred := by
  have hm := PNat.natPred_add_one m
  have hn := PNat.natPred_add_one n
  have hmn := PNat.natPred_add_one (m * n)
  simp only [PNat.mul_coe] at hmn
  nlinarith

@[simp] private theorem succPNat_natPred_mul (m n : ℕ+) :
    (m.natPred * n.natPred + m.natPred + n.natPred).succPNat = m * n := by
  rw [← natPred_mul]
  exact PNat.succPNat_natPred _

/-! Multiplication recurses through the tail of its right input. -/
private def mulChildren (p : ONote × ONote) : List (ONote × ONote) :=
  if p.1 = 0 then []
  else if p.2 = 0 then []
  else [(p.1, tailPart p.2)]

private theorem mulChildren_primrec : Primrec mulChildren := by
  exact Primrec.ite
    (Primrec.eq.comp Primrec.fst (Primrec.const (0 : ONote)))
    (Primrec.const [])
    (Primrec.ite
      (Primrec.eq.comp Primrec.snd (Primrec.const (0 : ONote)))
      (Primrec.const [])
      (Primrec.list_cons.comp
        (Primrec.pair Primrec.fst (tailPart_primrec.comp Primrec.snd))
        (Primrec.const [])))

private def mulStep (p : ONote × ONote) (rs : List ONote) : Option ONote :=
  if p.1 = 0 then some 0
  else if p.2 = 0 then some 0
  else if exponentPart p.2 = 0 then
    some (mkNode (exponentPart p.1)
      (coefficientPred p.1 * coefficientPred p.2 +
        coefficientPred p.1 + coefficientPred p.2,
        tailPart p.1))
  else
    some (mkNode (exponentPart p.1 + exponentPart p.2)
      (coefficientPred p.2, rs.getD 0 0))

private theorem mulStep_primrec : Primrec₂ mulStep := by
  let leftInput : Primrec (fun x : (ONote × ONote) × List ONote => x.1.1) :=
    Primrec.fst.comp Primrec.fst
  let rightInput : Primrec (fun x : (ONote × ONote) × List ONote => x.1.2) :=
    Primrec.snd.comp Primrec.fst
  let answer : Primrec (fun x : (ONote × ONote) × List ONote => x.2.getD 0 0) :=
    (Primrec.list_getD 0).comp Primrec.snd (Primrec.const 0)
  let leftExp : Primrec (fun x : (ONote × ONote) × List ONote =>
      exponentPart x.1.1) := exponentPart_primrec.comp leftInput
  let rightExp : Primrec (fun x : (ONote × ONote) × List ONote =>
      exponentPart x.1.2) := exponentPart_primrec.comp rightInput
  let leftCoeff : Primrec (fun x : (ONote × ONote) × List ONote =>
      coefficientPred x.1.1) := coefficientPred_primrec.comp leftInput
  let rightCoeff : Primrec (fun x : (ONote × ONote) × List ONote =>
      coefficientPred x.1.2) := coefficientPred_primrec.comp rightInput
  let leftTail : Primrec (fun x : (ONote × ONote) × List ONote =>
      tailPart x.1.1) := tailPart_primrec.comp leftInput
  let coeffProduct : Primrec (fun x : (ONote × ONote) × List ONote =>
      coefficientPred x.1.1 * coefficientPred x.1.2 +
        coefficientPred x.1.1 + coefficientPred x.1.2) :=
    Primrec.nat_add.comp
      (Primrec.nat_add.comp
        (Primrec.nat_mul.comp leftCoeff rightCoeff) leftCoeff)
      rightCoeff
  let finiteNode : Primrec (fun x : (ONote × ONote) × List ONote =>
      mkNode (exponentPart x.1.1)
        (coefficientPred x.1.1 * coefficientPred x.1.2 +
          coefficientPred x.1.1 + coefficientPred x.1.2,
          tailPart x.1.1)) :=
    mkNode_primrec.comp leftExp (Primrec.pair coeffProduct leftTail)
  let exponentSum : Primrec (fun x : (ONote × ONote) × List ONote =>
      exponentPart x.1.1 + exponentPart x.1.2) :=
    onoteAdd₂_primrec.comp leftExp rightExp
  let infiniteNode : Primrec (fun x : (ONote × ONote) × List ONote =>
      mkNode (exponentPart x.1.1 + exponentPart x.1.2)
        (coefficientPred x.1.2, x.2.getD 0 0)) :=
    mkNode_primrec.comp exponentSum (Primrec.pair rightCoeff answer)
  exact Primrec.ite
    (Primrec.eq.comp leftInput (Primrec.const (0 : ONote)))
    (Primrec.const (some (0 : ONote)))
    (Primrec.ite
      (Primrec.eq.comp rightInput (Primrec.const (0 : ONote)))
      (Primrec.const (some (0 : ONote)))
      (Primrec.ite
        (Primrec.eq.comp rightExp (Primrec.const (0 : ONote)))
        (Primrec.option_some.comp finiteNode)
        (Primrec.option_some.comp infiniteNode)))

private theorem mul_child_measure {p child : ONote × ONote}
    (h : child ∈ mulChildren p) : encode child.2 < encode p.2 := by
  rcases p with ⟨a, o⟩
  cases a with
  | zero => simp [mulChildren] at h
  | oadd e₁ n₁ a₁ =>
      cases o with
      | zero => simp [mulChildren] at h
      | oadd e₂ n₂ a₂ =>
          simp [mulChildren] at h
          rw [h]
          exact child_encode_lt (o := .oadd e₂ n₂ a₂) (by simp [children])

private theorem onoteMul_primrec :
    Primrec (fun p : ONote × ONote => p.1 * p.2) := by
  apply Primrec.nat_omega_rec'
    (fun p : ONote × ONote => p.1 * p.2)
    (encode_primrec.comp Primrec.snd) mulChildren_primrec mulStep_primrec
    (fun _ _ h => mul_child_measure h)
  rintro ⟨a, b⟩
  cases a with
  | zero => simp [mulStep]
  | oadd e₁ n₁ a₁ =>
      cases b with
      | zero => simp [mulStep]
      | oadd e₂ n₂ a₂ =>
          by_cases he : e₂ = 0
          · simp [mulStep, ONote.oadd_mul, he, mkNode]
          · simp [mulChildren, mulStep, ONote.oadd_mul, he, mkNode]

private theorem onoteMul₂_primrec : Primrec₂ (fun a b : ONote => a * b) := by
  exact onoteMul_primrec

private theorem mulCode_primrec₂ : Primrec₂ mulCode := by
  exact encode_primrec.comp <|
    onoteMul₂_primrec.comp₂
      (decode_primrec.comp₂ Primrec₂.left)
      (decode_primrec.comp₂ Primrec₂.right)

/-! ### Exponentiation helpers -/

private def splitStep (o : ONote) (rs : List (ONote × ℕ)) :
    Option (ONote × ℕ) :=
  if o = 0 then some (0, 0)
  else if exponentPart o = 0 then some (0, coefficientPred o + 1)
  else
    let r := rs.getD 1 (0, 0)
    some (mkNode (exponentPart o) (coefficientPred o, r.1), r.2)

private theorem splitStep_primrec : Primrec₂ splitStep := by
  let term : Primrec (fun x : ONote × List (ONote × ℕ) => x.1) := Primrec.fst
  let answer : Primrec (fun x : ONote × List (ONote × ℕ) =>
      x.2.getD 1 (0, 0)) :=
    (Primrec.list_getD (0, 0)).comp Primrec.snd (Primrec.const 1)
  let termExp : Primrec (fun x : ONote × List (ONote × ℕ) =>
      exponentPart x.1) := exponentPart_primrec.comp term
  let termCoeff : Primrec (fun x : ONote × List (ONote × ℕ) =>
      coefficientPred x.1) := coefficientPred_primrec.comp term
  let rebuilt : Primrec (fun x : ONote × List (ONote × ℕ) =>
      mkNode (exponentPart x.1)
        (coefficientPred x.1, (x.2.getD 1 (0, 0)).1)) :=
    mkNode_primrec.comp termExp
      (Primrec.pair termCoeff (Primrec.fst.comp answer))
  let recursiveResult : Primrec (fun x : ONote × List (ONote × ℕ) =>
      (mkNode (exponentPart x.1)
        (coefficientPred x.1, (x.2.getD 1 (0, 0)).1),
        (x.2.getD 1 (0, 0)).2)) :=
    Primrec.pair rebuilt (Primrec.snd.comp answer)
  exact Primrec.ite
    (Primrec.eq.comp term (Primrec.const (0 : ONote)))
    (Primrec.const (some ((0 : ONote), 0)))
    (Primrec.ite
      (Primrec.eq.comp termExp (Primrec.const (0 : ONote)))
      (Primrec.option_some.comp <| Primrec.pair
        (Primrec.const (0 : ONote)) (Primrec.succ.comp termCoeff))
      (Primrec.option_some.comp recursiveResult))

private theorem split_primrec : Primrec ONote.split := by
  apply onote_rec_primrec ONote.split splitStep splitStep_primrec
  intro o
  cases o with
  | zero => simp [splitStep, ONote.split]
  | oadd e n a =>
      by_cases he : e = 0
      · subst e
        simp [splitStep, ONote.split, PNat.natPred_add_one]
      · rcases hsplit : ONote.split a with ⟨a', m⟩
        simp [splitStep, children, ONote.split, he, hsplit, mkNode]

/- `scale x o` is structural recursion through the tail of `o`. -/
private def scaleChildren (p : ONote × ONote) : List (ONote × ONote) :=
  if p.2 = 0 then [] else [(p.1, tailPart p.2)]

private theorem scaleChildren_primrec : Primrec scaleChildren := by
  exact Primrec.ite
    (Primrec.eq.comp Primrec.snd (Primrec.const (0 : ONote)))
    (Primrec.const [])
    (Primrec.list_cons.comp
      (Primrec.pair Primrec.fst (tailPart_primrec.comp Primrec.snd))
      (Primrec.const []))

private def scaleStep (p : ONote × ONote) (rs : List ONote) : Option ONote :=
  if p.2 = 0 then some 0
  else some (mkNode (p.1 + exponentPart p.2)
    (coefficientPred p.2, rs.getD 0 0))

private theorem scaleStep_primrec : Primrec₂ scaleStep := by
  let scaleBy : Primrec (fun x : (ONote × ONote) × List ONote => x.1.1) :=
    Primrec.fst.comp Primrec.fst
  let term : Primrec (fun x : (ONote × ONote) × List ONote => x.1.2) :=
    Primrec.snd.comp Primrec.fst
  let answer : Primrec (fun x : (ONote × ONote) × List ONote => x.2.getD 0 0) :=
    (Primrec.list_getD 0).comp Primrec.snd (Primrec.const 0)
  let exponentSum : Primrec (fun x : (ONote × ONote) × List ONote =>
      x.1.1 + exponentPart x.1.2) :=
    onoteAdd₂_primrec.comp scaleBy (exponentPart_primrec.comp term)
  let result : Primrec (fun x : (ONote × ONote) × List ONote =>
      mkNode (x.1.1 + exponentPart x.1.2)
        (coefficientPred x.1.2, x.2.getD 0 0)) :=
    mkNode_primrec.comp exponentSum
      (Primrec.pair (coefficientPred_primrec.comp term) answer)
  exact Primrec.ite
    (Primrec.eq.comp term (Primrec.const (0 : ONote)))
    (Primrec.const (some (0 : ONote)))
    (Primrec.option_some.comp result)

private theorem scale_child_measure {p child : ONote × ONote}
    (h : child ∈ scaleChildren p) : encode child.2 < encode p.2 := by
  rcases p with ⟨x, o⟩
  cases o with
  | zero => simp [scaleChildren] at h
  | oadd e n a =>
      simp [scaleChildren] at h
      rw [h]
      exact child_encode_lt (o := .oadd e n a) (by simp [children])

private theorem scale_primrec₂ : Primrec₂ ONote.scale := by
  apply Primrec.nat_omega_rec'
    (fun p : ONote × ONote => ONote.scale p.1 p.2)
    (encode_primrec.comp Primrec.snd) scaleChildren_primrec scaleStep_primrec
    (fun _ _ h => scale_child_measure h)
  rintro ⟨x, o⟩
  cases o <;> simp [scaleChildren, scaleStep, ONote.scale, mkNode]

private theorem mulNat_primrec₂ : Primrec₂ ONote.mulNat := by
  have h : Primrec (fun p : ONote × ℕ =>
      if p.1 = 0 then 0
      else if p.2 = 0 then 0
      else mkNode (exponentPart p.1)
        (coefficientPred p.1 * p.2.pred + coefficientPred p.1 + p.2.pred,
          tailPart p.1)) := by
    let term : Primrec (fun p : ONote × ℕ => p.1) := Primrec.fst
    let multiplier : Primrec (fun p : ONote × ℕ => p.2) := Primrec.snd
    let multiplierPred : Primrec (fun p : ONote × ℕ => p.2.pred) :=
      Primrec.pred.comp multiplier
    let coeff : Primrec (fun p : ONote × ℕ => coefficientPred p.1) :=
      coefficientPred_primrec.comp term
    let productCoeff : Primrec (fun p : ONote × ℕ =>
        coefficientPred p.1 * p.2.pred + coefficientPred p.1 + p.2.pred) :=
      Primrec.nat_add.comp
        (Primrec.nat_add.comp (Primrec.nat_mul.comp coeff multiplierPred) coeff)
        multiplierPred
    let result : Primrec (fun p : ONote × ℕ =>
        mkNode (exponentPart p.1)
          (coefficientPred p.1 * p.2.pred + coefficientPred p.1 + p.2.pred,
            tailPart p.1)) :=
      mkNode_primrec.comp (exponentPart_primrec.comp term)
        (Primrec.pair productCoeff (tailPart_primrec.comp term))
    exact Primrec.ite
      (Primrec.eq.comp term (Primrec.const (0 : ONote)))
      (Primrec.const (0 : ONote))
      (Primrec.ite
        (Primrec.eq.comp multiplier (Primrec.const 0))
        (Primrec.const (0 : ONote)) result)
  have h₂ : Primrec₂ (fun o m =>
      if o = 0 then 0
      else if m = 0 then 0
      else mkNode (exponentPart o)
        (coefficientPred o * m.pred + coefficientPred o + m.pred,
          tailPart o)) := by
    change Primrec (fun p : ONote × ℕ =>
      if p.1 = 0 then 0
      else if p.2 = 0 then 0
      else mkNode (exponentPart p.1)
        (coefficientPred p.1 * p.2.pred + coefficientPred p.1 + p.2.pred,
          tailPart p.1))
    exact h
  apply Primrec₂.of_eq h₂
  intro o m
  cases o with
  | zero => simp [ONote.mulNat]
  | oadd e n a =>
      cases m with
      | zero => simp [ONote.mulNat]
      | succ m =>
          simp [ONote.mulNat, mkNode]
          exact succPNat_natPred_mul n m.succPNat

/-- The only subtraction needed by exponentiation is subtraction of one. -/
private def subOne (o : ONote) : ONote :=
  if o = 0 then 0
  else if exponentPart o = 0 then
    if coefficientPred o = 0 then tailPart o
    else mkNode 0 (coefficientPred o - 1, tailPart o)
  else o

private theorem subOne_primrec : Primrec subOne := by
  let finiteResult : Primrec (fun o : ONote =>
      mkNode 0 (coefficientPred o - 1, tailPart o)) :=
    mkNode_primrec.comp (Primrec.const (0 : ONote))
      (Primrec.pair
        (Primrec.nat_sub.comp coefficientPred_primrec (Primrec.const 1))
        tailPart_primrec)
  exact Primrec.ite
    (Primrec.eq.comp Primrec.id (Primrec.const (0 : ONote)))
    (Primrec.const (0 : ONote))
    (Primrec.ite
      (Primrec.eq.comp exponentPart_primrec (Primrec.const (0 : ONote)))
      (Primrec.ite
        (Primrec.eq.comp coefficientPred_primrec (Primrec.const 0))
        tailPart_primrec finiteResult)
      Primrec.id)

private theorem subOne_eq (o : ONote) : subOne o = o - 1 := by
  change subOne o = ONote.sub o (.oadd 0 1 0)
  cases o with
  | zero => simp [subOne, ONote.sub]
  | oadd e n a =>
      cases e with
      | zero =>
          rw [← PNat.succPNat_natPred n]
          cases hn : n.natPred with
          | zero =>
              cases a <;>
                simp [subOne, ONote.sub, ONote.cmp,
                  Nat.succPNat, PNat.natPred]
          | succ k =>
              simp [subOne, ONote.sub, ONote.cmp, mkNode,
                Nat.succPNat, PNat.natPred]
      | oadd ee en ea =>
          simp [subOne, ONote.sub, ONote.cmp]

private def splitPrimeStep (o : ONote) (rs : List (ONote × ℕ)) :
    Option (ONote × ℕ) :=
  if o = 0 then some (0, 0)
  else if exponentPart o = 0 then some (0, coefficientPred o + 1)
  else
    let r := rs.getD 1 (0, 0)
    some (mkNode (subOne (exponentPart o))
      (coefficientPred o, r.1), r.2)

private theorem splitPrimeStep_primrec : Primrec₂ splitPrimeStep := by
  let term : Primrec (fun x : ONote × List (ONote × ℕ) => x.1) := Primrec.fst
  let answer : Primrec (fun x : ONote × List (ONote × ℕ) =>
      x.2.getD 1 (0, 0)) :=
    (Primrec.list_getD (0, 0)).comp Primrec.snd (Primrec.const 1)
  let termExp : Primrec (fun x : ONote × List (ONote × ℕ) =>
      exponentPart x.1) := exponentPart_primrec.comp term
  let termCoeff : Primrec (fun x : ONote × List (ONote × ℕ) =>
      coefficientPred x.1) := coefficientPred_primrec.comp term
  let rebuilt : Primrec (fun x : ONote × List (ONote × ℕ) =>
      mkNode (subOne (exponentPart x.1))
        (coefficientPred x.1, (x.2.getD 1 (0, 0)).1)) :=
    mkNode_primrec.comp (subOne_primrec.comp termExp)
      (Primrec.pair termCoeff (Primrec.fst.comp answer))
  let recursiveResult : Primrec (fun x : ONote × List (ONote × ℕ) =>
      (mkNode (subOne (exponentPart x.1))
        (coefficientPred x.1, (x.2.getD 1 (0, 0)).1),
        (x.2.getD 1 (0, 0)).2)) :=
    Primrec.pair rebuilt (Primrec.snd.comp answer)
  exact Primrec.ite
    (Primrec.eq.comp term (Primrec.const (0 : ONote)))
    (Primrec.const (some ((0 : ONote), 0)))
    (Primrec.ite
      (Primrec.eq.comp termExp (Primrec.const (0 : ONote)))
      (Primrec.option_some.comp <| Primrec.pair
        (Primrec.const (0 : ONote)) (Primrec.succ.comp termCoeff))
      (Primrec.option_some.comp recursiveResult))

private theorem split'_primrec : Primrec ONote.split' := by
  apply onote_rec_primrec ONote.split' splitPrimeStep splitPrimeStep_primrec
  intro o
  cases o with
  | zero => simp [splitPrimeStep, ONote.split']
  | oadd e n a =>
      by_cases he : e = 0
      · subst e
        simp [splitPrimeStep, ONote.split', PNat.natPred_add_one]
      · rcases hsplit : ONote.split' a with ⟨a', m⟩
        simp [splitPrimeStep, children, ONote.split', he, hsplit, mkNode, subOne_eq]

private theorem natPow_primrec₂ : Primrec₂ Nat.pow := by
  let step : Primrec₂ (fun a : ℕ => fun q : ℕ × ℕ => a * q.2) :=
    Primrec.nat_mul.comp₂ Primrec₂.left (Primrec.snd.comp₂ Primrec₂.right)
  apply Primrec₂.of_eq (Primrec.nat_rec (Primrec.const 1) step)
  intro a k
  induction k with
  | zero => rfl
  | succ k ih => simp [Nat.pow_succ, ih, Nat.mul_comm]

/- Parameters kept fixed while `opowAux` recurses on its penultimate
natural argument. -/
private abbrev OpowParams := ((ONote × ONote) × ONote) × ℕ

private def opowBase (q : OpowParams) : ONote :=
  if q.2 = 0 then 0 else mkNode q.1.1.1 (q.2.pred, 0)

private theorem opowBase_primrec : Primrec opowBase := by
  exact Primrec.ite
    (Primrec.eq.comp Primrec.snd (Primrec.const 0))
    (Primrec.const (0 : ONote))
    (mkNode_primrec.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.pair (Primrec.pred.comp Primrec.snd)
        (Primrec.const (0 : ONote))))

private def opowSucc (q : OpowParams) (kr : ℕ × ONote) : ONote :=
  if q.2 = 0 then 0
  else ONote.scale (q.1.1.1 + ONote.mulNat q.1.1.2 kr.1) q.1.2 + kr.2

private theorem opowSucc_primrec : Primrec₂ opowSucc := by
  let params : Primrec (fun x : OpowParams × (ℕ × ONote) => x.1) := Primrec.fst
  let exponent : Primrec (fun x : OpowParams × (ℕ × ONote) => x.1.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  let finiteExponent : Primrec (fun x : OpowParams × (ℕ × ONote) => x.1.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  let baseTail : Primrec (fun x : OpowParams × (ℕ × ONote) => x.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  let multiplier : Primrec (fun x : OpowParams × (ℕ × ONote) => x.1.2) :=
    Primrec.snd.comp Primrec.fst
  let index : Primrec (fun x : OpowParams × (ℕ × ONote) => x.2.1) :=
    Primrec.fst.comp Primrec.snd
  let previous : Primrec (fun x : OpowParams × (ℕ × ONote) => x.2.2) :=
    Primrec.snd.comp Primrec.snd
  let finiteProduct : Primrec (fun x : OpowParams × (ℕ × ONote) =>
      ONote.mulNat x.1.1.1.2 x.2.1) :=
    mulNat_primrec₂.comp finiteExponent index
  let scaleExponent : Primrec (fun x : OpowParams × (ℕ × ONote) =>
      x.1.1.1.1 + ONote.mulNat x.1.1.1.2 x.2.1) :=
    onoteAdd₂_primrec.comp exponent finiteProduct
  let scaled : Primrec (fun x : OpowParams × (ℕ × ONote) =>
      ONote.scale (x.1.1.1.1 + ONote.mulNat x.1.1.1.2 x.2.1)
        x.1.1.2) :=
    scale_primrec₂.comp scaleExponent baseTail
  let result : Primrec (fun x : OpowParams × (ℕ × ONote) =>
      ONote.scale (x.1.1.1.1 + ONote.mulNat x.1.1.1.2 x.2.1)
        x.1.1.2 + x.2.2) :=
    onoteAdd₂_primrec.comp scaled previous
  exact Primrec.ite
    (Primrec.eq.comp multiplier (Primrec.const 0))
    (Primrec.const (0 : ONote)) result

private def opowAuxChildren (p : OpowParams × ℕ) :
    List (OpowParams × ℕ) :=
  if p.2 = 0 then [] else [(p.1, p.2.pred)]

private theorem opowAuxChildren_primrec : Primrec opowAuxChildren := by
  exact Primrec.ite
    (Primrec.eq.comp Primrec.snd (Primrec.const 0))
    (Primrec.const [])
    (Primrec.list_cons.comp
      (Primrec.pair Primrec.fst (Primrec.pred.comp Primrec.snd))
      (Primrec.const []))

private def opowAuxStep (p : OpowParams × ℕ) (rs : List ONote) :
    Option ONote :=
  if p.2 = 0 then some (opowBase p.1)
  else some (opowSucc p.1 (p.2.pred, rs.getD 0 0))

private theorem opowAuxStep_primrec : Primrec₂ opowAuxStep := by
  let argument : Primrec (fun x : (OpowParams × ℕ) × List ONote => x.1) :=
    Primrec.fst
  let params : Primrec (fun x : (OpowParams × ℕ) × List ONote => x.1.1) :=
    Primrec.fst.comp Primrec.fst
  let index : Primrec (fun x : (OpowParams × ℕ) × List ONote => x.1.2) :=
    Primrec.snd.comp Primrec.fst
  let answer : Primrec (fun x : (OpowParams × ℕ) × List ONote =>
      x.2.getD 0 0) :=
    (Primrec.list_getD 0).comp Primrec.snd (Primrec.const 0)
  let successor : Primrec (fun x : (OpowParams × ℕ) × List ONote =>
      opowSucc x.1.1 (x.1.2.pred, x.2.getD 0 0)) :=
    opowSucc_primrec.comp params
      (Primrec.pair (Primrec.pred.comp index) answer)
  exact Primrec.ite
    (Primrec.eq.comp index (Primrec.const 0))
    (Primrec.option_some.comp (opowBase_primrec.comp params))
    (Primrec.option_some.comp successor)

private theorem opowAux_child_measure {p child : OpowParams × ℕ}
    (h : child ∈ opowAuxChildren p) : child.2 < p.2 := by
  by_cases hp : p.2 = 0
  · simp [opowAuxChildren, hp] at h
  · have hchild : child = (p.1, p.2.pred) := by
      simpa [opowAuxChildren, hp] using h
    subst child
    exact Nat.pred_lt hp

private theorem opowAux_packed_primrec :
    Primrec (fun p : OpowParams × ℕ =>
      ONote.opowAux p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.2 p.1.2) := by
  apply Primrec.nat_omega_rec'
    (fun p : OpowParams × ℕ =>
      ONote.opowAux p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.2 p.1.2)
    Primrec.snd opowAuxChildren_primrec opowAuxStep_primrec
    (fun _ _ h => opowAux_child_measure h)
  rintro ⟨⟨⟨⟨e, a0⟩, a⟩, m⟩, k⟩
  cases k with
  | zero =>
      cases m with
      | zero => simp [opowAuxStep, opowBase, ONote.opowAux]
      | succ m =>
          simp [opowAuxStep, opowBase, ONote.opowAux, mkNode]
  | succ k =>
      cases m with
      | zero => simp [opowAuxStep, opowSucc, ONote.opowAux]
      | succ m =>
          simp [opowAuxChildren, opowAuxStep, opowSucc, ONote.opowAux]

@[simp] private theorem succPNat_pow_natPred (m k : ℕ) :
    (m.succPNat ^ k).natPred = (m + 1) ^ k - 1 := by
  rw [PNat.natPred]
  simp [PNat.pow_coe]

@[simp] private theorem succPNat_pow_sub_one (m k : ℕ) :
    (((m + 1) ^ k - 1).succPNat) = m.succPNat ^ k := by
  rw [← succPNat_pow_natPred]
  exact PNat.succPNat_natPred _

/-- A branch-friendly presentation of Mathlib's final exponentiation step. -/
private def opowAux2Calc (o₂ : ONote) (o₁ : ONote × ℕ) : ONote :=
  if o₁.1 = 0 then
    if o₁.2 = 0 then (if o₂ = 0 then 1 else 0)
    else if o₁.2 = 1 then 1
    else
      let s := ONote.split' o₂
      mkNode s.1 (o₁.2 ^ s.2 - 1, 0)
  else
    let s := ONote.split o₂
    let a0 := exponentPart o₁.1
    let eb := a0 * s.1
    if s.2 = 0 then mkNode eb (0, 0)
    else
      ONote.scale (eb + ONote.mulNat a0 s.2.pred) o₁.1 +
        ONote.opowAux eb a0 (ONote.mulNat o₁.1 o₁.2)
          s.2.pred o₁.2

private theorem opowAux2Calc_primrec₂ : Primrec₂ opowAux2Calc := by
  let exponent : Primrec (fun x : ONote × (ONote × ℕ) => x.1) := Primrec.fst
  let base : Primrec (fun x : ONote × (ONote × ℕ) => x.2.1) :=
    Primrec.fst.comp Primrec.snd
  let finitePart : Primrec (fun x : ONote × (ONote × ℕ) => x.2.2) :=
    Primrec.snd.comp Primrec.snd
  let splitPrime : Primrec (fun x : ONote × (ONote × ℕ) =>
      ONote.split' x.1) := split'_primrec.comp exponent
  let splitNormal : Primrec (fun x : ONote × (ONote × ℕ) =>
      ONote.split x.1) := split_primrec.comp exponent
  let finitePower : Primrec (fun x : ONote × (ONote × ℕ) =>
      x.2.2 ^ (ONote.split' x.1).2) :=
    natPow_primrec₂.comp finitePart (Primrec.snd.comp splitPrime)
  let finiteCoeff : Primrec (fun x : ONote × (ONote × ℕ) =>
      x.2.2 ^ (ONote.split' x.1).2 - 1) :=
    Primrec.nat_sub.comp finitePower (Primrec.const 1)
  let finiteNode : Primrec (fun x : ONote × (ONote × ℕ) =>
      mkNode (ONote.split' x.1).1
        (x.2.2 ^ (ONote.split' x.1).2 - 1, 0)) :=
    mkNode_primrec.comp (Primrec.fst.comp splitPrime)
      (Primrec.pair finiteCoeff (Primrec.const (0 : ONote)))
  let a0 : Primrec (fun x : ONote × (ONote × ℕ) =>
      exponentPart x.2.1) := exponentPart_primrec.comp base
  let b : Primrec (fun x : ONote × (ONote × ℕ) =>
      (ONote.split x.1).1) := Primrec.fst.comp splitNormal
  let remainder : Primrec (fun x : ONote × (ONote × ℕ) =>
      (ONote.split x.1).2) := Primrec.snd.comp splitNormal
  let k : Primrec (fun x : ONote × (ONote × ℕ) =>
      (ONote.split x.1).2.pred) := Primrec.pred.comp remainder
  let eb : Primrec (fun x : ONote × (ONote × ℕ) =>
      exponentPart x.2.1 * (ONote.split x.1).1) :=
    onoteMul₂_primrec.comp a0 b
  let limitNode : Primrec (fun x : ONote × (ONote × ℕ) =>
      mkNode (exponentPart x.2.1 * (ONote.split x.1).1) (0, 0)) :=
    mkNode_primrec.comp eb (Primrec.const (0, (0 : ONote)))
  let a0k : Primrec (fun x : ONote × (ONote × ℕ) =>
      ONote.mulNat (exponentPart x.2.1) (ONote.split x.1).2.pred) :=
    mulNat_primrec₂.comp a0 k
  let scaleExponent : Primrec (fun x : ONote × (ONote × ℕ) =>
      exponentPart x.2.1 * (ONote.split x.1).1 +
        ONote.mulNat (exponentPart x.2.1) (ONote.split x.1).2.pred) :=
    onoteAdd₂_primrec.comp eb a0k
  let scaled : Primrec (fun x : ONote × (ONote × ℕ) =>
      ONote.scale
        (exponentPart x.2.1 * (ONote.split x.1).1 +
          ONote.mulNat (exponentPart x.2.1) (ONote.split x.1).2.pred)
        x.2.1) :=
    scale_primrec₂.comp scaleExponent base
  let auxiliaryBase : Primrec (fun x : ONote × (ONote × ℕ) =>
      ONote.mulNat x.2.1 x.2.2) :=
    mulNat_primrec₂.comp base finitePart
  let packedParams : Primrec (fun x : ONote × (ONote × ℕ) =>
      ((((exponentPart x.2.1 * (ONote.split x.1).1,
          exponentPart x.2.1), ONote.mulNat x.2.1 x.2.2), x.2.2),
        (ONote.split x.1).2.pred)) :=
    Primrec.pair
      (Primrec.pair
        (Primrec.pair (Primrec.pair eb a0) auxiliaryBase) finitePart)
      k
  let auxiliary : Primrec (fun x : ONote × (ONote × ℕ) =>
      ONote.opowAux
        (exponentPart x.2.1 * (ONote.split x.1).1)
        (exponentPart x.2.1) (ONote.mulNat x.2.1 x.2.2)
        (ONote.split x.1).2.pred x.2.2) :=
    opowAux_packed_primrec.comp packedParams
  let infiniteResult : Primrec (fun x : ONote × (ONote × ℕ) =>
      ONote.scale
          (exponentPart x.2.1 * (ONote.split x.1).1 +
            ONote.mulNat (exponentPart x.2.1) (ONote.split x.1).2.pred)
          x.2.1 +
        ONote.opowAux
          (exponentPart x.2.1 * (ONote.split x.1).1)
          (exponentPart x.2.1) (ONote.mulNat x.2.1 x.2.2)
          (ONote.split x.1).2.pred x.2.2) :=
    onoteAdd₂_primrec.comp scaled auxiliary
  let calculation : Primrec (fun x : ONote × (ONote × ℕ) =>
      opowAux2Calc x.1 x.2) :=
    Primrec.ite
      (Primrec.eq.comp base (Primrec.const (0 : ONote)))
      (Primrec.ite
        (Primrec.eq.comp finitePart (Primrec.const 0))
        (Primrec.ite
          (Primrec.eq.comp exponent (Primrec.const (0 : ONote)))
          (Primrec.const (1 : ONote)) (Primrec.const (0 : ONote)))
        (Primrec.ite
          (Primrec.eq.comp finitePart (Primrec.const 1))
          (Primrec.const (1 : ONote)) finiteNode))
      (Primrec.ite
        (Primrec.eq.comp remainder (Primrec.const 0))
        limitNode infiniteResult)
  change Primrec (fun x : ONote × (ONote × ℕ) => opowAux2Calc x.1 x.2)
  exact calculation

private theorem opowAux2_primrec₂ : Primrec₂ ONote.opowAux2 := by
  apply Primrec₂.of_eq opowAux2Calc_primrec₂
  intro o₂ o₁
  rcases o₁ with ⟨a, m⟩
  cases a with
  | zero =>
      cases m with
      | zero => simp [opowAux2Calc, ONote.opowAux2]
      | succ m =>
          cases m with
          | zero =>
              change (1 : ONote) = ONote.opowAux2 o₂ (0, 1)
              rfl
          | succ m =>
              rcases hsplit : ONote.split' o₂ with ⟨b, k⟩
              have h0 : m + 1 + 1 ≠ 0 := by omega
              have h1 : m + 1 + 1 ≠ 1 := by omega
              unfold opowAux2Calc ONote.opowAux2
              simp only [if_false, h0, h1, hsplit]
              change mkNode b ((m + 2) ^ k - 1, 0) =
                .oadd b ((m + 1).succPNat ^ k) 0
              have hm : m + 2 = (m + 1) + 1 := by omega
              simp [mkNode, hm]
  | oadd a0 n a =>
      rcases hsplit : ONote.split o₂ with ⟨b, r⟩
      cases r with
      | zero =>
          simp [opowAux2Calc, ONote.opowAux2, hsplit, mkNode]
          rfl
      | succ k =>
          simp [opowAux2Calc, ONote.opowAux2, hsplit]

private theorem onoteOpow₂_primrec : Primrec₂ (fun a b : ONote => a ^ b) := by
  apply Primrec₂.of_eq
    (opowAux2_primrec₂.comp₂ Primrec₂.right
      (split_primrec.comp₂ Primrec₂.left))
  intro a b
  rfl

private theorem powCode_primrec₂ : Primrec₂ powCode := by
  exact encode_primrec.comp <|
    onoteOpow₂_primrec.comp₂
      (decode_primrec.comp₂ Primrec₂.left)
      (decode_primrec.comp₂ Primrec₂.right)

/-! ## Actual formulas of Peano arithmetic -/

private theorem vectorGet_primrec {k : ℕ} (i : Fin k) :
    Primrec (fun v : List.Vector ℕ k => v.get i) :=
  Primrec.vector_get.comp Primrec.id (Primrec.const i)

private theorem validVector_primrecPred :
    PrimrecPred (fun v : List.Vector ℕ 1 => ValidOrdinalCode (v.get 0)) :=
  validOrdinalCode_primrecPred.comp (vectorGet_primrec 0)

private theorem ltVector_primrecPred :
    PrimrecPred (fun v : List.Vector ℕ 2 => OrdinalLT (v.get 0) (v.get 1)) :=
  ordinalLT_primrecRel.comp (vectorGet_primrec 0) (vectorGet_primrec 1)

private theorem addVector_primrecPred :
    PrimrecPred (fun v : List.Vector ℕ 3 =>
      OrdinalAdd (v.get 0) (v.get 1) (v.get 2)) := by
  let validLeft : PrimrecPred (fun v : List.Vector ℕ 3 =>
      ValidOrdinalCode (v.get 1)) :=
    validOrdinalCode_primrecPred.comp (vectorGet_primrec 1)
  let validRight : PrimrecPred (fun v : List.Vector ℕ 3 =>
      ValidOrdinalCode (v.get 2)) :=
    validOrdinalCode_primrecPred.comp (vectorGet_primrec 2)
  let computes : Primrec (fun v : List.Vector ℕ 3 =>
      addCode (v.get 1) (v.get 2)) :=
    addCode_primrec₂.comp (vectorGet_primrec 1) (vectorGet_primrec 2)
  let graph : PrimrecPred (fun v : List.Vector ℕ 3 =>
      v.get 0 = addCode (v.get 1) (v.get 2)) :=
    Primrec.eq.comp (vectorGet_primrec 0) computes
  exact (validLeft.and (validRight.and graph)).of_eq fun v => by
    simp [OrdinalAdd]

private theorem mulVector_primrecPred :
    PrimrecPred (fun v : List.Vector ℕ 3 =>
      OrdinalMul (v.get 0) (v.get 1) (v.get 2)) := by
  let validLeft : PrimrecPred (fun v : List.Vector ℕ 3 =>
      ValidOrdinalCode (v.get 1)) :=
    validOrdinalCode_primrecPred.comp (vectorGet_primrec 1)
  let validRight : PrimrecPred (fun v : List.Vector ℕ 3 =>
      ValidOrdinalCode (v.get 2)) :=
    validOrdinalCode_primrecPred.comp (vectorGet_primrec 2)
  let computes : Primrec (fun v : List.Vector ℕ 3 =>
      mulCode (v.get 1) (v.get 2)) :=
    mulCode_primrec₂.comp (vectorGet_primrec 1) (vectorGet_primrec 2)
  let graph : PrimrecPred (fun v : List.Vector ℕ 3 =>
      v.get 0 = mulCode (v.get 1) (v.get 2)) :=
    Primrec.eq.comp (vectorGet_primrec 0) computes
  exact (validLeft.and (validRight.and graph)).of_eq fun v => by
    simp [OrdinalMul]

private theorem powVector_primrecPred :
    PrimrecPred (fun v : List.Vector ℕ 3 =>
      OrdinalPow (v.get 0) (v.get 1) (v.get 2)) := by
  let validLeft : PrimrecPred (fun v : List.Vector ℕ 3 =>
      ValidOrdinalCode (v.get 1)) :=
    validOrdinalCode_primrecPred.comp (vectorGet_primrec 1)
  let validRight : PrimrecPred (fun v : List.Vector ℕ 3 =>
      ValidOrdinalCode (v.get 2)) :=
    validOrdinalCode_primrecPred.comp (vectorGet_primrec 2)
  let computes : Primrec (fun v : List.Vector ℕ 3 =>
      powCode (v.get 1) (v.get 2)) :=
    powCode_primrec₂.comp (vectorGet_primrec 1) (vectorGet_primrec 2)
  let graph : PrimrecPred (fun v : List.Vector ℕ 3 =>
      v.get 0 = powCode (v.get 1) (v.get 2)) :=
    Primrec.eq.comp (vectorGet_primrec 0) computes
  exact (validLeft.and (validRight.and graph)).of_eq fun v => by
    simp [OrdinalPow]

private theorem primrecPred_to_re {α : Type*} [Primcodable α]
    {R : α → Prop} (hR : PrimrecPred R) : REPred R := by
  rcases hR with ⟨decR, hR⟩
  letI : DecidablePred R := decR
  apply ComputablePred.to_re
  rw [ComputablePred.computable_iff]
  exact ⟨fun x => decide (R x), hR.to_comp, by funext x; simp⟩

/-- A partial computation that halts with zero exactly when `R` holds. -/
private def relationPart {α : Type*} (R : α → Prop) (x : α) : Part ℕ :=
  (Part.assert (R x) fun _ => Part.some ()).map fun _ => 0

private theorem relationPart_partrec {α : Type*} [Primcodable α]
    {R : α → Prop} (hR : REPred R) : Partrec (relationPart R) := by
  exact Partrec.map hR (Computable.const 0).to₂

private theorem relationPart_natPartrec' {k : ℕ}
    {R : List.Vector ℕ k → Prop} (hR : REPred R) :
    Nat.Partrec' (relationPart R) :=
  Nat.Partrec'.of_part (relationPart_partrec hR)

private theorem validVector_re :
    REPred (fun v : List.Vector ℕ 1 => ValidOrdinalCode (v.get 0)) :=
  primrecPred_to_re validVector_primrecPred

private theorem ltVector_re :
    REPred (fun v : List.Vector ℕ 2 => OrdinalLT (v.get 0) (v.get 1)) :=
  primrecPred_to_re ltVector_primrecPred

private theorem addVector_re :
    REPred (fun v : List.Vector ℕ 3 =>
      OrdinalAdd (v.get 0) (v.get 1) (v.get 2)) :=
  primrecPred_to_re addVector_primrecPred

private theorem mulVector_re :
    REPred (fun v : List.Vector ℕ 3 =>
      OrdinalMul (v.get 0) (v.get 1) (v.get 2)) :=
  primrecPred_to_re mulVector_primrecPred

private theorem powVector_re :
    REPred (fun v : List.Vector ℕ 3 =>
      OrdinalPow (v.get 0) (v.get 1) (v.get 2)) :=
  primrecPred_to_re powVector_primrecPred

/-!
The representation theorem reserves its zeroth variable for the computation's
output.  Substituting the numeral zero there leaves precisely the advertised
relation variables.  For arithmetic graphs these are deliberately ordered
`(result, left, right)`.
-/

/-- PA formula saying that its sole variable is a valid epsilon-zero code. -/
noncomputable def validOrdinalCodeFormula : ArithmeticSemisentence 1 :=
  (codeOfPartrec' (relationPart fun v : List.Vector ℕ 1 =>
    ValidOrdinalCode (v.get 0)))/[‘0’, #0]

/-- PA formula for strict comparison of valid ordinal codes. -/
noncomputable def ordinalLTFormula : ArithmeticSemisentence 2 :=
  (codeOfPartrec' (relationPart fun v : List.Vector ℕ 2 =>
    OrdinalLT (v.get 0) (v.get 1)))/[‘0’, #0, #1]

/-- Result-first PA formula for the graph of ordinal addition. -/
noncomputable def ordinalAddFormula : ArithmeticSemisentence 3 :=
  (codeOfPartrec' (relationPart fun v : List.Vector ℕ 3 =>
    OrdinalAdd (v.get 0) (v.get 1) (v.get 2)))/[‘0’, #0, #1, #2]

/-- Result-first PA formula for the graph of ordinal multiplication. -/
noncomputable def ordinalMulFormula : ArithmeticSemisentence 3 :=
  (codeOfPartrec' (relationPart fun v : List.Vector ℕ 3 =>
    OrdinalMul (v.get 0) (v.get 1) (v.get 2)))/[‘0’, #0, #1, #2]

/-- Result-first PA formula for the graph of ordinal exponentiation. -/
noncomputable def ordinalPowFormula : ArithmeticSemisentence 3 :=
  (codeOfPartrec' (relationPart fun v : List.Vector ℕ 3 =>
    OrdinalPow (v.get 0) (v.get 1) (v.get 2)))/[‘0’, #0, #1, #2]

@[simp] theorem validOrdinalCodeFormula_spec (c : ℕ) :
    validOrdinalCodeFormula.Evalb (![c]) ↔ ValidOrdinalCode c := by
  simpa [validOrdinalCodeFormula, Semiformula.eval_substs,
    Matrix.comp_vecCons', relationPart]
    using (codeOfPartrec'_spec
      (relationPart_natPartrec' validVector_re) (v := ![c]) (y := 0))

@[simp] theorem ordinalLTFormula_spec (a b : ℕ) :
    ordinalLTFormula.Evalb (![a, b]) ↔ OrdinalLT a b := by
  simpa [ordinalLTFormula, Semiformula.eval_substs,
    Matrix.comp_vecCons', relationPart]
    using (codeOfPartrec'_spec
      (relationPart_natPartrec' ltVector_re) (v := ![a, b]) (y := 0))

@[simp] theorem ordinalAddFormula_spec (z a b : ℕ) :
    ordinalAddFormula.Evalb (![z, a, b]) ↔ OrdinalAdd z a b := by
  simpa [ordinalAddFormula, Semiformula.eval_substs,
    Matrix.comp_vecCons', relationPart]
    using (codeOfPartrec'_spec
      (relationPart_natPartrec' addVector_re) (v := ![z, a, b]) (y := 0))

@[simp] theorem ordinalMulFormula_spec (z a b : ℕ) :
    ordinalMulFormula.Evalb (![z, a, b]) ↔ OrdinalMul z a b := by
  simpa [ordinalMulFormula, Semiformula.eval_substs,
    Matrix.comp_vecCons', relationPart]
    using (codeOfPartrec'_spec
      (relationPart_natPartrec' mulVector_re) (v := ![z, a, b]) (y := 0))

@[simp] theorem ordinalPowFormula_spec (z a b : ℕ) :
    ordinalPowFormula.Evalb (![z, a, b]) ↔ OrdinalPow z a b := by
  simpa [ordinalPowFormula, Semiformula.eval_substs,
    Matrix.comp_vecCons', relationPart]
    using (codeOfPartrec'_spec
      (relationPart_natPartrec' powVector_re) (v := ![z, a, b]) (y := 0))

end PAListCoding.EpsilonZero
