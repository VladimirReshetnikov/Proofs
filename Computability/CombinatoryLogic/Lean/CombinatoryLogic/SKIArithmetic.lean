/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in ../LICENSE-Apache-2.0.
Authors: Thomas Waring, Jesse Alama

Adapted and modified from leanprover/cslib pull request #403 (commit
0c998e71) to `CombinatoryLogic.SKI.Term` and its context-closed `Step`
relation. See ../THIRD_PARTY_NOTICES.md.
-/

import CombinatoryLogic.SKI
import Mathlib.Data.Nat.Pairing
import Mathlib.Tactic

/-!
# Arithmetic and general recursion in the local SKI calculus

This module supplies bracket abstraction, Church numerals, primitive recursion,
unbounded minimization, and the arithmetic needed to realize Mathlib's
`Nat.pair`/`Nat.unpair` coding.  Its construction and proofs are adapted from
the Apache-2.0 CSLib development cited in the file header.
-/

namespace CombinatoryLogic.SKI.Term

/-! ## Compatibility lemmas for the local reduction closure -/

local infix:50 " ↠ " => Steps

private theorem steps_i (x : Term) : (i ⬝ x) ↠ x := Steps.single (.i x)
private theorem steps_k (x y : Term) : (k ⬝ x ⬝ y) ↠ x := Steps.single (.k x y)
private theorem steps_s (x y z : Term) :
    (s ⬝ x ⬝ y ⬝ z) ↠ (x ⬝ z ⬝ (y ⬝ z)) := Steps.single (.s x y z)

private theorem steps_head {a a' : Term} (b : Term) (h : a ↠ a') :
    (a ⬝ b) ↠ (a' ⬝ b) := Steps.appLeft b h

private theorem steps_tail (a : Term) {b b' : Term} (h : b ↠ b') :
    (a ⬝ b) ↠ (a ⬝ b') := Steps.appRight a h

private theorem steps_parallel {a a' b b' : Term} (ha : a ↠ a') (hb : b ↠ b') :
    (a ⬝ b) ↠ (a' ⬝ b') := Steps.app ha hb

/-! ## Bracket abstraction -/

/-- Apply a term to a list of arguments. -/
def applyList (f : Term) (xs : List Term) : Term := List.foldl (· ⬝ ·) f xs

@[simp] theorem applyList_concat (f : Term) (ys : List Term) (z : Term) :
    applyList f (ys ++ [z]) = applyList f ys ⬝ z := by
  simp [applyList]

/-- An SKI polynomial with `n` free variables and arbitrary closed SKI constants. -/
inductive Polynomial (n : Nat) where
  | term : Term → Polynomial n
  | var : Fin n → Polynomial n
  | app : Polynomial n → Polynomial n → Polynomial n

namespace Polynomial

infixl:70 " ⬝' " => app
prefix:71 "&" => var

instance : Coe Term (Polynomial n) := ⟨term⟩

/-- Substitute terms for all variables in a polynomial. -/
def eval (p : Polynomial n) (xs : List Term) (hxs : xs.length = n) : Term :=
  match p with
  | .term x => x
  | .var index => xs[index]
  | .app p q => eval p xs hxs ⬝ eval q xs hxs

/-- Interpret a variable-free polynomial as a term. -/
def varFreeToTerm (p : Polynomial 0) : Term := p.eval [] (by simp)

/-- Eliminate the last variable by the standard `S`/`K`/`I` abstraction. -/
def elimVar : Polynomial (n + 1) → Polynomial n
  | .term x => k ⬝' x
  | .var index => by
      by_cases h : index < n
      · exact k ⬝' (.var <| @Fin.ofNat n ⟨Nat.ne_zero_of_lt h⟩ index)
      · exact .term i
  | .app p q => s ⬝' elimVar p ⬝' elimVar q

theorem elimVar_correct (p : Polynomial (n + 1)) {ys : List Term}
    (hys : ys.length = n) (z : Term) :
    (p.elimVar.eval ys hys ⬝ z) ↠ p.eval (ys ++ [z])
      (by simp [hys]) := by
  match n, p with
  | _, .term x =>
      simp only [elimVar, eval]
      exact steps_k x z
  | _, .app p q =>
      simp only [elimVar, eval]
      exact (steps_s _ _ z).trans
        (steps_parallel (elimVar_correct p hys z) (elimVar_correct q hys z))
  | n, .var index =>
      simp only [elimVar]
      split_ifs with hi
      · have hle : (↑index : Nat) ≤ n := Nat.le_of_lt_succ index.isLt
        have h : (ys ++ [z])[index]'(by simpa [hys] using index.isLt) = ys[↑index] := by
          grind
        simp only [eval, h, Fin.getElem_fin, Fin.val_ofNat, Nat.mod_eq_of_lt hi]
        exact steps_k _ z
      · replace hi := Nat.eq_of_lt_succ_of_not_lt index.isLt hi
        have hlen : (ys ++ [z]).length = n + 1 := by simp [hys]
        have hz : (ys ++ [z])[n]'(by omega) = z := by
          rw [List.getElem_append_right] <;> simp [hys]
        simp only [eval, Fin.getElem_fin, hi, hz]
        exact steps_i z

/-- Close all variables by repeated bracket abstraction. -/
def toTerm : {n : Nat} → Polynomial n → Term
  | 0, p => p.varFreeToTerm
  | _ + 1, p => p.elimVar.toTerm

theorem toTerm_correct (p : Polynomial n) (xs : List Term)
    (hxs : xs.length = n) : applyList p.toTerm xs ↠ p.eval xs hxs := by
  induction n generalizing xs with
  | zero =>
      rw [List.length_eq_zero_iff] at hxs
      subst xs
      simp only [toTerm, varFreeToTerm, applyList, List.foldl_nil]
      convert (.refl : Steps (p.eval [] hxs) (p.eval [] hxs))
  | succ n inductionHypothesis =>
      have hne : xs ≠ [] := List.ne_nil_of_length_eq_add_one hxs
      obtain ⟨ys, z, rfl⟩ := (List.eq_nil_or_concat xs).resolve_left hne
      have hys : ys.length = n := by
        simpa using Nat.succ.inj (by simpa using hxs)
      simp only [toTerm, List.concat_eq_append, applyList_concat]
      exact (steps_head z (inductionHypothesis p.elimVar ys hys)).trans
        (elimVar_correct p hys z)

end Polynomial

/-! ## Basic derived combinators -/

open Polynomial

/-- Argument reversal: `λ x y, y x`. -/
def RPoly : Polynomial 2 := &1 ⬝' &0
def R : Term := RPoly.toTerm
theorem R_def (x y : Term) : (R ⬝ x ⬝ y) ↠ y ⬝ x :=
  RPoly.toTerm_correct [x, y] (by simp)

/-- Composition: `λ f g x, f (g x)`. -/
def BPoly : Polynomial 3 := &0 ⬝' (&1 ⬝' &2)
def B : Term := BPoly.toTerm
theorem B_def (f g x : Term) : (B ⬝ f ⬝ g ⬝ x) ↠ f ⬝ (g ⬝ x) :=
  BPoly.toTerm_correct [f, g, x] (by simp)

/-- Rotate three arguments right: `λ x y z, z x y`. -/
def RotRPoly : Polynomial 3 := &2 ⬝' &0 ⬝' &1
def RotR : Term := RotRPoly.toTerm
theorem rotR_def (x y z : Term) : (RotR ⬝ x ⬝ y ⬝ z) ↠ z ⬝ x ⬝ y :=
  RotRPoly.toTerm_correct [x, y, z] (by simp)

/-- `λ f x, f (x x)`. -/
def HPoly : Polynomial 2 := &0 ⬝' (&1 ⬝' &1)
def H : Term := HPoly.toTerm
theorem H_def (f x : Term) : (H ⬝ f ⬝ x) ↠ f ⬝ (x ⬝ x) :=
  HPoly.toTerm_correct [f, x] (by simp)

/-- An on-the-nose fixed point of `f`. -/
def fixedPoint (f : Term) : Term := H ⬝ f ⬝ (H ⬝ f)
theorem fixedPoint_correct (f : Term) : fixedPoint f ↠ f ⬝ fixedPoint f := H_def f (H ⬝ f)

/-! ## Booleans and pairs -/

/-- Church representation of a Boolean. -/
def IsBool (value : Bool) (term : Term) : Prop :=
  ∀ x y, (term ⬝ x ⬝ y) ↠ if value then x else y

theorem isBool_trans (value : Bool) {a a' : Term} (h : a ↠ a') (ha' : IsBool value a') :
    IsBool value a := by
  intro x y
  exact (steps_head y (steps_head x h)).trans (ha' x y)

def TT : Term := k
theorem TT_correct : IsBool true TT := fun x y => steps_k x y

def FF : Term := k ⬝ i
theorem FF_correct : IsBool false FF := by
  intro x y
  exact (steps_head y (steps_k i x)).trans (steps_i y)

/-- `Cond x y b` chooses `x` when `b` is true and `y` otherwise. -/
def Cond : Term := RotR
theorem cond_correct (a x y : Term) (value : Bool) (h : IsBool value a) :
    (Cond ⬝ x ⬝ y ⬝ a) ↠ if value then x else y :=
  (rotR_def x y a).trans (h x y)

def Neg : Term := Cond ⬝ FF ⬝ TT
theorem neg_correct (a : Term) (value : Bool) (h : IsBool value a) :
    IsBool (!value) (Neg ⬝ a) := by
  apply isBool_trans (!value) (cond_correct a FF TT value h)
  cases value <;> simp [TT_correct, FF_correct]

/-- Church pair constructor. -/
def MkPair : Term := Cond
def Fst : Term := R ⬝ TT
def Snd : Term := R ⬝ FF

theorem fst_correct (a b : Term) : (Fst ⬝ (MkPair ⬝ a ⬝ b)) ↠ a :=
  (R_def TT (MkPair ⬝ a ⬝ b)).trans (cond_correct TT a b true TT_correct)

theorem snd_correct (a b : Term) : (Snd ⬝ (MkPair ⬝ a ⬝ b)) ↠ b :=
  (R_def FF (MkPair ⬝ a ⬝ b)).trans (cond_correct FF a b false FF_correct)

/-! ## Church numerals -/

/-- The body obtained by iterating `f` exactly `n` times on `x`. -/
def Church (n : Nat) (f x : Term) : Term :=
  match n with
  | 0 => x
  | n + 1 => f ⬝ Church n f x

@[simp] theorem Church_zero (f x : Term) : Church 0 f x = x := rfl
@[simp] theorem Church_succ (n : Nat) (f x : Term) : Church (n + 1) f x = f ⬝ Church n f x := rfl

theorem church_steps (n : Nat) {f f' x x' : Term} (hf : f ↠ f') (hx : x ↠ x') :
    Church n f x ↠ Church n f' x' := by
  induction n with
  | zero => exact hx
  | succ n ih => exact steps_parallel hf ih

/-- `a` extensionally behaves as the Church numeral for `n`. -/
def IsChurch (n : Nat) (a : Term) : Prop :=
  ∀ f x, (a ⬝ f ⬝ x) ↠ Church n f x

/-- Church representation is preserved by reducing its representing term. -/
theorem isChurch_trans (n : Nat) {a a' : Term} (h : a ↠ a') :
    IsChurch n a' → IsChurch n a := by
  intro ha' f x
  exact (steps_head x (steps_head f h)).trans (ha' f x)

/-- Church zero, `λ f x, x`. -/
def Zero : Term := k ⬝ i
theorem zero_correct : IsChurch 0 Zero := by
  intro f x
  exact (steps_head x (steps_k i f)).trans (steps_i x)

/-- Church one. -/
def One : Term := i
theorem one_correct : IsChurch 1 One := by
  intro f x
  exact steps_head x (steps_i f)

/-- Church successor, `λ a f x, f (a f x)`. -/
def Succ : Term := s ⬝ B
theorem succ_correct (n : Nat) (a : Term) (h : IsChurch n a) :
    IsChurch (n + 1) (Succ ⬝ a) := by
  intro f x
  exact (steps_head x (steps_s B a f)).trans
    ((B_def f (a ⬝ f) x).trans (steps_tail f (h f x)))

/-- A canonical closed SKI representative for each Church numeral. -/
def toChurch : Nat → Term
  | 0 => Zero
  | n + 1 => Succ ⬝ toChurch n

@[simp] theorem toChurch_zero : toChurch 0 = Zero := rfl
@[simp] theorem toChurch_succ (n : Nat) : toChurch (n + 1) = Succ ⬝ toChurch n := rfl

theorem toChurch_correct (n : Nat) : IsChurch n (toChurch n) := by
  induction n with
  | zero => exact zero_correct
  | succ n ih => exact succ_correct n _ ih

/-! ## Predecessor -/

def PredAuxPoly : Polynomial 1 := MkPair ⬝' (Snd ⬝' &0) ⬝' (Succ ⬝' (Snd ⬝' &0))
def PredAux : Term := PredAuxPoly.toTerm
theorem predAux_def (p : Term) :
    (PredAux ⬝ p) ↠ MkPair ⬝ (Snd ⬝ p) ⬝ (Succ ⬝ (Snd ⬝ p)) :=
  PredAuxPoly.toTerm_correct [p] (by simp)

/-- A Church-encoded pair of Church numerals. -/
def IsChurchPair (ns : Nat × Nat) (p : Term) : Prop :=
  IsChurch ns.1 (Fst ⬝ p) ∧ IsChurch ns.2 (Snd ⬝ p)

theorem isChurchPair_trans (ns : Nat × Nat) {a a' : Term} (h : a ↠ a') :
    IsChurchPair ns a' → IsChurchPair ns a := by
  rintro ⟨ha, hb⟩
  exact ⟨isChurch_trans _ (steps_tail Fst h) ha,
    isChurch_trans _ (steps_tail Snd h) hb⟩

theorem predAux_correct (p : Term) (ns : Nat × Nat) (h : IsChurchPair ns p) :
    IsChurchPair (ns.2, ns.2 + 1) (PredAux ⬝ p) := by
  apply isChurchPair_trans _ (predAux_def p)
  exact ⟨isChurch_trans _ (fst_correct _ _) h.2,
    isChurch_trans _ (snd_correct _ _) (succ_correct _ _ h.2)⟩

theorem predAux_iter_correct (n : Nat) :
    IsChurchPair (n.pred, n) (Church n PredAux (MkPair ⬝ Zero ⬝ Zero)) := by
  induction n with
  | zero =>
      constructor
      · exact isChurch_trans _ (fst_correct Zero Zero) zero_correct
      · exact isChurch_trans _ (snd_correct Zero Zero) zero_correct
  | succ n ih => exact predAux_correct _ _ ih

def PredPoly : Polynomial 1 := Fst ⬝' (&0 ⬝' PredAux ⬝' (MkPair ⬝ Zero ⬝ Zero))
def Pred : Term := PredPoly.toTerm
theorem pred_def (a : Term) :
    (Pred ⬝ a) ↠ Fst ⬝ (a ⬝ PredAux ⬝ (MkPair ⬝ Zero ⬝ Zero)) :=
  PredPoly.toTerm_correct [a] (by simp)

theorem pred_correct (n : Nat) (a : Term) (h : IsChurch n a) :
    IsChurch n.pred (Pred ⬝ a) := by
  apply isChurch_trans _ (pred_def a)
  apply isChurch_trans _ (steps_tail Fst (h PredAux (MkPair ⬝ Zero ⬝ Zero)))
  exact (predAux_iter_correct n).1

/-! ## Primitive recursion -/

def IsZeroPoly : Polynomial 1 := &0 ⬝' (k ⬝ FF) ⬝' TT
def IsZero : Term := IsZeroPoly.toTerm
theorem isZero_def (a : Term) : (IsZero ⬝ a) ↠ a ⬝ (k ⬝ FF) ⬝ TT :=
  IsZeroPoly.toTerm_correct [a] (by simp)

theorem isZero_correct (n : Nat) (a : Term) (h : IsChurch n a) :
    IsBool (n = 0) (IsZero ⬝ a) := by
  apply isBool_trans (n = 0) (isZero_def a)
  by_cases hn : n = 0
  · subst n
    simpa using isBool_trans true (h (k ⬝ FF) TT) TT_correct
  · obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    simp only [Nat.succ_ne_zero, decide_false]
    apply isBool_trans false (h (k ⬝ FF) TT)
    exact isBool_trans false (steps_k FF (Church q (k ⬝ FF) TT)) FF_correct

/-- One unfolding layer of primitive recursion. -/
def RecAuxPoly : Polynomial 4 :=
  Cond ⬝' &1 ⬝' (&2 ⬝' &3 ⬝' (&0 ⬝' &1 ⬝' &2 ⬝' (Pred ⬝' &3))) ⬝'
    (IsZero ⬝' &3)
def RecAux : Term := RecAuxPoly.toTerm
theorem recAux_def (r base step a : Term) :
    (RecAux ⬝ r ⬝ base ⬝ step ⬝ a) ↠
      Cond ⬝ base ⬝ (step ⬝ a ⬝ (r ⬝ base ⬝ step ⬝ (Pred ⬝ a))) ⬝ (IsZero ⬝ a) :=
  RecAuxPoly.toTerm_correct [r, base, step, a] (by simp)

/-- Primitive recursion from a base and an indexed step. -/
def Rec : Term := fixedPoint RecAux
theorem rec_def (base step a : Term) :
    (Rec ⬝ base ⬝ step ⬝ a) ↠
      Cond ⬝ base ⬝ (step ⬝ a ⬝ (Rec ⬝ base ⬝ step ⬝ (Pred ⬝ a))) ⬝ (IsZero ⬝ a) :=
  (steps_head a (steps_head step (steps_head base (fixedPoint_correct RecAux)))).trans
    (recAux_def Rec base step a)

theorem rec_zero (base step a : Term) (ha : IsChurch 0 a) :
    (Rec ⬝ base ⬝ step ⬝ a) ↠ base :=
  (rec_def base step a).trans
    (cond_correct (IsZero ⬝ a) base
      (step ⬝ a ⬝ (Rec ⬝ base ⬝ step ⬝ (Pred ⬝ a))) true (isZero_correct 0 a ha))

theorem rec_succ (n : Nat) (base step a : Term) (ha : IsChurch (n + 1) a) :
    (Rec ⬝ base ⬝ step ⬝ a) ↠
      step ⬝ a ⬝ (Rec ⬝ base ⬝ step ⬝ (Pred ⬝ a)) :=
  (rec_def base step a).trans
    (cond_correct (IsZero ⬝ a) base
      (step ⬝ a ⬝ (Rec ⬝ base ⬝ step ⬝ (Pred ⬝ a))) false
      (by simpa using isZero_correct (n + 1) a ha))

theorem rec_correct (base step : Term) (r : Nat → Nat)
    (hbase : IsChurch (r 0) base)
    (hstep : ∀ n cn previous, IsChurch (n + 1) cn → IsChurch (r n) previous →
      IsChurch (r (n + 1)) (step ⬝ cn ⬝ previous)) :
    ∀ n cn, IsChurch n cn → IsChurch (r n) (Rec ⬝ base ⬝ step ⬝ cn) := by
  intro n
  induction n with
  | zero =>
      intro cn hcn
      exact isChurch_trans _ (rec_zero base step cn hcn) hbase
  | succ n ih =>
      intro cn hcn
      exact isChurch_trans _ (rec_succ n base step cn hcn)
        (hstep n cn (Rec ⬝ base ⬝ step ⬝ (Pred ⬝ cn)) hcn
          (ih (Pred ⬝ cn) (pred_correct _ cn hcn)))

/-! ## Unbounded minimization -/

def RFindAboveAuxPoly : Polynomial 3 :=
  Cond ⬝' &1 ⬝' (&0 ⬝' (Succ ⬝' &1) ⬝' &2) ⬝' (IsZero ⬝' (&2 ⬝' &1))
def RFindAboveAux : Term := RFindAboveAuxPoly.toTerm

theorem rfindAboveAux_def (r a f : Term) :
    (RFindAboveAux ⬝ r ⬝ a ⬝ f) ↠
      Cond ⬝ a ⬝ (r ⬝ (Succ ⬝ a) ⬝ f) ⬝ (IsZero ⬝ (f ⬝ a)) :=
  RFindAboveAuxPoly.toTerm_correct [r, a, f] (by simp)

theorem rfindAboveAux_base (r f a : Term) (hfa : IsChurch 0 (f ⬝ a)) :
    (RFindAboveAux ⬝ r ⬝ a ⬝ f) ↠ a :=
  (rfindAboveAux_def r a f).trans
    (cond_correct (IsZero ⬝ (f ⬝ a)) a (r ⬝ (Succ ⬝ a) ⬝ f) true
      (isZero_correct 0 _ hfa))

theorem rfindAboveAux_step (r f a : Term) {value : Nat}
    (hfa : IsChurch (value + 1) (f ⬝ a)) :
    (RFindAboveAux ⬝ r ⬝ a ⬝ f) ↠ r ⬝ (Succ ⬝ a) ⬝ f :=
  (rfindAboveAux_def r a f).trans
    (cond_correct (IsZero ⬝ (f ⬝ a)) a (r ⬝ (Succ ⬝ a) ⬝ f) false
      (by simpa using isZero_correct (value + 1) _ hfa))

/-- Search for the first zero at or above a represented starting point. -/
def RFindAbove : Term := fixedPoint RFindAboveAux

theorem RFindAbove_unfold (x f : Term) :
    (RFindAbove ⬝ x ⬝ f) ↠ RFindAboveAux ⬝ RFindAbove ⬝ x ⬝ f :=
  steps_head f (steps_head x (fixedPoint_correct RFindAboveAux))

theorem RFindAbove_zero (f x : Term) (hfx : IsChurch 0 (f ⬝ x)) :
    (RFindAbove ⬝ x ⬝ f) ↠ x :=
  (RFindAbove_unfold x f).trans
    (rfindAboveAux_base RFindAbove f x hfx)

theorem RFindAbove_positive (f x : Term) {value : Nat}
    (hfx : IsChurch (value + 1) (f ⬝ x)) :
    (RFindAbove ⬝ x ⬝ f) ↠ RFindAbove ⬝ (Succ ⬝ x) ⬝ f :=
  (RFindAbove_unfold x f).trans
    (rfindAboveAux_step RFindAbove f x hfx)

theorem RFindAbove_correct (f x : Term) (distance start : Nat) (hx : IsChurch start x)
    (hfRoot : ∀ y, IsChurch (start + distance) y → IsChurch 0 (f ⬝ y))
    (hfBelow : ∀ i < distance, ∀ y, IsChurch (start + i) y →
      ∃ value, IsChurch (value + 1) (f ⬝ y)) :
    IsChurch (start + distance) (RFindAbove ⬝ x ⬝ f) := by
  induction distance generalizing start x with
  | zero =>
      exact isChurch_trans _ (RFindAbove_zero f x (hfRoot x (by simpa using hx))) hx
  | succ distance ih =>
      apply isChurch_trans _ (RFindAbove_positive f x
        ((hfBelow 0 (by omega) x (by simpa using hx)).choose_spec))
      have hnext := ih (Succ ⬝ x) (start + 1) (succ_correct start x hx)
        (fun y hy => hfRoot y (by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hy))
        (fun i hi y hy => hfBelow (i + 1)
          (by simpa [Nat.succ_eq_add_one] using Nat.succ_lt_succ hi) y
          (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hy))
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext

/-! ## Arithmetic -/

/-- Addition, `λ n m, n Succ m`. -/
def AddPoly : Polynomial 2 := &0 ⬝' Succ ⬝' &1
def Add : Term := AddPoly.toTerm
theorem add_def (a b : Term) : (Add ⬝ a ⬝ b) ↠ a ⬝ Succ ⬝ b :=
  AddPoly.toTerm_correct [a, b] (by simp)

theorem add_correct (n m : Nat) (a b : Term) (ha : IsChurch n a) (hb : IsChurch m b) :
    IsChurch (n + m) (Add ⬝ a ⬝ b) := by
  apply isChurch_trans _ ((add_def a b).trans (ha Succ b))
  clear ha a
  induction n with
  | zero => simpa using hb
  | succ n ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        succ_correct (n + m) (Church n Succ b) ih

/-- Multiplication, `λ n m, n (Add m) Zero`. -/
def MulPoly : Polynomial 2 := &0 ⬝' (Add ⬝' &1) ⬝' Zero
def Mul : Term := MulPoly.toTerm
theorem mul_def (a b : Term) : (Mul ⬝ a ⬝ b) ↠ a ⬝ (Add ⬝ b) ⬝ Zero :=
  MulPoly.toTerm_correct [a, b] (by simp)

theorem mul_correct {n m : Nat} {a b : Term} (ha : IsChurch n a) (hb : IsChurch m b) :
    IsChurch (n * m) (Mul ⬝ a ⬝ b) := by
  apply isChurch_trans _ ((mul_def a b).trans (ha (Add ⬝ b) Zero))
  clear ha a
  induction n with
  | zero => simpa using zero_correct
  | succ n ih =>
      simpa [Nat.add_mul, Nat.add_comm] using
        add_correct m (n * m) b (Church n (Add ⬝ b) Zero) hb ih

/-- Truncated subtraction, `λ n m, m Pred n`. -/
def SubPoly : Polynomial 2 := &1 ⬝' Pred ⬝' &0
def Sub : Term := SubPoly.toTerm
theorem sub_def (a b : Term) : (Sub ⬝ a ⬝ b) ↠ b ⬝ Pred ⬝ a :=
  SubPoly.toTerm_correct [a, b] (by simp)

theorem sub_correct (n m : Nat) (a b : Term) (ha : IsChurch n a) (hb : IsChurch m b) :
    IsChurch (n - m) (Sub ⬝ a ⬝ b) := by
  apply isChurch_trans _ ((sub_def a b).trans (hb Pred a))
  clear hb b
  induction m with
  | zero => simpa using ha
  | succ m ih =>
      have hindex : n - (m + 1) = (n - m) - 1 := by omega
      rw [hindex]
      simpa only [Church, Nat.pred_eq_sub_one] using
        pred_correct (n - m) (Church m Pred a) ih

/-- Boolean less-than-or-equal comparison. -/
def LEPoly : Polynomial 2 := IsZero ⬝' (Sub ⬝' &0 ⬝' &1)
def LE : Term := LEPoly.toTerm
theorem le_def (a b : Term) : (LE ⬝ a ⬝ b) ↠ IsZero ⬝ (Sub ⬝ a ⬝ b) :=
  LEPoly.toTerm_correct [a, b] (by simp)

theorem le_correct (n m : Nat) (a b : Term) (ha : IsChurch n a) (hb : IsChurch m b) :
    IsBool (n ≤ m) (LE ⬝ a ⬝ b) := by
  apply isBool_trans (n ≤ m) (le_def a b)
  rw [show decide (n ≤ m) = decide (n - m = 0) by
    exact decide_eq_decide.mpr Nat.sub_eq_zero_iff_le.symm]
  exact isZero_correct _ _ (sub_correct n m a b ha hb)

/-! ## Search from zero -/

def RFind : Term := RFindAbove ⬝ Zero

theorem RFind_correct (fNat : Nat → Nat) (f : Term)
    (hf : ∀ i y, IsChurch i y → IsChurch (fNat i) (f ⬝ y))
    (n : Nat) (hroot : fNat n = 0) (hpositive : ∀ i < n, fNat i ≠ 0) :
    IsChurch n (RFind ⬝ f) := by
  simpa [RFind] using RFindAbove_correct f Zero n 0 zero_correct
    (fun y hy => by
      simpa [hroot] using hf n y (by simpa using hy))
    (fun i hi y hy => by
      refine ⟨fNat i - 1, ?_⟩
      have := hf i y (by simpa using hy)
      have hne : fNat i ≠ 0 := hpositive i hi
      have hindex : fNat i - 1 + 1 = fNat i := by omega
      rw [hindex]
      exact this)

/- TEMPORARY ELABORATION BISECT: square-root/pairing

/-! ## Integer square root -/

/-- At `(n,k)`, return zero exactly when `(k+1)^2 > n`. -/
def SqrtCondPoly : Polynomial 2 :=
  Cond ⬝' Zero ⬝' One ⬝'
    (Neg ⬝' (LE ⬝' (Mul ⬝' (Succ ⬝' &1) ⬝' (Succ ⬝' &1)) ⬝' &0))
def SqrtCond : Term := SqrtCondPoly.toTerm

theorem sqrtCond_def (cn ck : Term) :
    (SqrtCond ⬝ cn ⬝ ck) ↠
      Cond ⬝ Zero ⬝ One ⬝
        (Neg ⬝ (LE ⬝ (Mul ⬝ (Succ ⬝ ck) ⬝ (Succ ⬝ ck)) ⬝ cn)) :=
  SqrtCondPoly.toTerm_correct [cn, ck] (by simp)

def SqrtPoly : Polynomial 1 := RFind ⬝' (SqrtCond ⬝' &0)
def Sqrt : Term := SqrtPoly.toTerm
theorem sqrt_def (cn : Term) : (Sqrt ⬝ cn) ↠ RFind ⬝ (SqrtCond ⬝ cn) :=
  SqrtPoly.toTerm_correct [cn] (by simp)

theorem sqrt_correct (n : Nat) (cn : Term) (hcn : IsChurch n cn) :
    IsChurch (Nat.sqrt n) (Sqrt ⬝ cn) := by
  apply isChurch_trans _ (sqrt_def cn)
  apply RFind_correct (fun k => if n < (k + 1) * (k + 1) then 0 else 1) (SqrtCond ⬝ cn)
  · intro index cindex hindex
    apply isChurch_trans _ (sqrtCond_def cn cindex)
    have hsucc := succ_correct index cindex hindex
    have hle := le_correct _ n _ cn (mul_correct hsucc hsucc) hcn
    have hneg := neg_correct _ _ hle
    apply isChurch_trans _ (cond_correct _ _ _ _ hneg)
    split <;> simp_all [zero_correct, one_correct]
  · simp [Nat.lt_succ_sqrt]
  · intro i hi
    simp only [ite_eq_right_iff, one_ne_zero, imp_false, not_lt]
    exact Nat.le_of_lt_succ (Nat.lt_succ_iff.mpr (Nat.le_sqrt.mp (Nat.le_of_lt hi)))

/-! ## Mathlib-compatible natural pairing and unpairing -/

/-- Mathlib's square pairing function on Church numerals. -/
def NatPairPoly : Polynomial 2 :=
  Cond ⬝' (Add ⬝' (Mul ⬝' &1 ⬝' &1) ⬝' &0) ⬝'
    (Add ⬝' (Add ⬝' (Mul ⬝' &0 ⬝' &0) ⬝' &0) ⬝' &1) ⬝'
    (Neg ⬝' (LE ⬝' &1 ⬝' &0))
def NatPair : Term := NatPairPoly.toTerm

theorem natPair_def (ca cb : Term) :
    (NatPair ⬝ ca ⬝ cb) ↠
      Cond ⬝ (Add ⬝ (Mul ⬝ cb ⬝ cb) ⬝ ca) ⬝
        (Add ⬝ (Add ⬝ (Mul ⬝ ca ⬝ ca) ⬝ ca) ⬝ cb) ⬝
        (Neg ⬝ (LE ⬝ cb ⬝ ca)) :=
  NatPairPoly.toTerm_correct [ca, cb] (by simp)

theorem natPair_correct (a b : Nat) (ca cb : Term)
    (ha : IsChurch a ca) (hb : IsChurch b cb) :
    IsChurch (Nat.pair a b) (NatPair ⬝ ca ⬝ cb) := by
  rw [Nat.pair]
  apply isChurch_trans _ (natPair_def ca cb)
  have hcond := neg_correct _ _ (le_correct b a cb ca hb ha)
  apply isChurch_trans _ (cond_correct _ _ _ _ hcond)
  by_cases hab : a < b
  · simp only [hab, if_true]
    exact add_correct _ _ _ _ (mul_correct hb hb) ha
  · simp only [hab, if_false]
    exact add_correct _ _ _ _ (add_correct _ _ _ _ (mul_correct ha ha) ha) hb

/-- Left projection of Mathlib's `Nat.unpair`. -/
def NatUnpairLeftPoly : Polynomial 1 :=
  let root := Sqrt ⬝' &0
  let square := Mul ⬝' root ⬝' root
  let difference := Sub ⬝' &0 ⬝' square
  Cond ⬝' difference ⬝' root ⬝' (Neg ⬝' (LE ⬝' root ⬝' difference))
def NatUnpairLeft : Term := NatUnpairLeftPoly.toTerm

theorem natUnpairLeft_def (cn : Term) :
    (NatUnpairLeft ⬝ cn) ↠
      Cond ⬝ (Sub ⬝ cn ⬝ (Mul ⬝ (Sqrt ⬝ cn) ⬝ (Sqrt ⬝ cn))) ⬝ (Sqrt ⬝ cn) ⬝
        (Neg ⬝ (LE ⬝ (Sqrt ⬝ cn) ⬝
          (Sub ⬝ cn ⬝ (Mul ⬝ (Sqrt ⬝ cn) ⬝ (Sqrt ⬝ cn))))) :=
  NatUnpairLeftPoly.toTerm_correct [cn] (by simp)

private theorem natUnpair_church (n : Nat) (cn : Term) (hcn : IsChurch n cn) :
    IsChurch (Nat.sqrt n) (Sqrt ⬝ cn) ∧
    IsChurch (n - Nat.sqrt n * Nat.sqrt n)
      (Sub ⬝ cn ⬝ (Mul ⬝ (Sqrt ⬝ cn) ⬝ (Sqrt ⬝ cn))) := by
  have hs := sqrt_correct n cn hcn
  exact ⟨hs, sub_correct n _ cn _ hcn (mul_correct hs hs)⟩

theorem natUnpairLeft_correct (n : Nat) (cn : Term) (hcn : IsChurch n cn) :
    IsChurch (Nat.unpair n).1 (NatUnpairLeft ⬝ cn) := by
  apply isChurch_trans _ (natUnpairLeft_def cn)
  obtain ⟨hs, hdifference⟩ := natUnpair_church n cn hcn
  have hcondition := neg_correct _ _ (le_correct _ _ _ _ hs hdifference)
  apply isChurch_trans _ (cond_correct _ _ _ _ hcondition)
  rw [Nat.unpair]
  split_ifs with h
  · simpa [pow_two] using hdifference
  · simpa using hs

/-- Right projection of Mathlib's `Nat.unpair`. -/
def NatUnpairRightPoly : Polynomial 1 :=
  let root := Sqrt ⬝' &0
  let square := Mul ⬝' root ⬝' root
  let difference := Sub ⬝' &0 ⬝' square
  Cond ⬝' root ⬝' (Sub ⬝' difference ⬝' root) ⬝'
    (Neg ⬝' (LE ⬝' root ⬝' difference))
def NatUnpairRight : Term := NatUnpairRightPoly.toTerm

theorem natUnpairRight_def (cn : Term) :
    (NatUnpairRight ⬝ cn) ↠
      Cond ⬝ (Sqrt ⬝ cn) ⬝
        (Sub ⬝ (Sub ⬝ cn ⬝ (Mul ⬝ (Sqrt ⬝ cn) ⬝ (Sqrt ⬝ cn))) ⬝ (Sqrt ⬝ cn)) ⬝
        (Neg ⬝ (LE ⬝ (Sqrt ⬝ cn) ⬝
          (Sub ⬝ cn ⬝ (Mul ⬝ (Sqrt ⬝ cn) ⬝ (Sqrt ⬝ cn))))) :=
  NatUnpairRightPoly.toTerm_correct [cn] (by simp)

theorem natUnpairRight_correct (n : Nat) (cn : Term) (hcn : IsChurch n cn) :
    IsChurch (Nat.unpair n).2 (NatUnpairRight ⬝ cn) := by
  apply isChurch_trans _ (natUnpairRight_def cn)
  obtain ⟨hs, hdifference⟩ := natUnpair_church n cn hcn
  have hcondition := neg_correct _ _ (le_correct _ _ _ _ hs hdifference)
  apply isChurch_trans _ (cond_correct _ _ _ _ hcondition)
  rw [Nat.unpair]
  split_ifs with h
  · simpa using hs
  · simpa [pow_two] using sub_correct _ _ _ _ hdifference hs

-/

end CombinatoryLogic.SKI.Term
