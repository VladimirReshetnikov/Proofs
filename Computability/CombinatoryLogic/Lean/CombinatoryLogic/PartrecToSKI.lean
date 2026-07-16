/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in ../LICENSE-Apache-2.0.
Authors: Jesse Alama

Adapted and modified from leanprover/cslib pull request #403 (commit
0c998e71) to `CombinatoryLogic.SKI.Term` and its context-closed `Step`
relation. See ../THIRD_PARTY_NOTICES.md.
-/

import CombinatoryLogic.SKIArithmetic
import Mathlib.Computability.PartrecCode

/-!
# Defined-case compilation of partial-recursive functions to SKI

The compiler covers every constructor of `Nat.Partrec.Code`.  Its correctness
theorem is deliberately one-sided: when `m ∈ c.eval n`, the compiled term maps
every Church representative of `n` to a Church representative of `m`.  No
claim about undefined inputs or reduction reflection is made here.
-/

namespace CombinatoryLogic.SKI.Term

open Nat.Partrec
open Polynomial

local infix:50 " ↠ " => Steps

/-- A term realizes every defined input/output pair of a partial function. -/
def Computes (term : Term) (f : Nat →. Nat) : Prop :=
  ∀ n cn, IsChurch n cn → ∀ m, m ∈ f n → IsChurch m (term ⬝ cn)

/-- Defined-case SKI computability.  This intentionally carries no converse
or divergence clause. -/
def Computable (f : Nat →. Nat) : Prop := ∃ term, Computes term f

theorem computes_of_total {term : Term} {f : Nat →. Nat} (g : Nat → Nat)
    (heval : ∀ n, f n = Part.some (g n))
    (hcorrect : ∀ n cn, IsChurch n cn → IsChurch (g n) (term ⬝ cn)) :
    Computes term f := by
  intro n cn hcn m hm
  rw [heval] at hm
  obtain rfl := Part.mem_some_iff.mp hm
  exact hcorrect n cn hcn

theorem comp_computes {f g : Nat →. Nat} {tf tg : Term}
    (hf : Computes tf f) (hg : Computes tg g) :
    Computes (B ⬝ tf ⬝ tg) (fun n => g n >>= f) := by
  intro n cn hcn m hm
  obtain ⟨intermediate, hintermediate, hm⟩ := Part.mem_bind_iff.mp hm
  exact isChurch_trans _ (B_def tf tg cn)
    (hf intermediate (tg ⬝ cn) (hg n cn hcn intermediate hintermediate) m hm)

theorem pair_computes {f g : Nat →. Nat} {tf tg : Term}
    (hf : Computes tf f) (hg : Computes tg g) :
    Computes (s ⬝ (B ⬝ NatPair ⬝ tf) ⬝ tg)
      (fun n => Nat.pair <$> f n <*> g n) := by
  intro n cn hcn m hm
  simp only [Seq.seq, Functor.map, Part.mem_bind_iff, Part.mem_map_iff] at hm
  obtain ⟨_, ⟨a, ha, rfl⟩, b, hb, rfl⟩ := hm
  have hs : Steps
      (s ⬝ (B ⬝ NatPair ⬝ tf) ⬝ tg ⬝ cn)
      ((B ⬝ NatPair ⬝ tf) ⬝ cn ⬝ (tg ⬝ cn)) :=
    Steps.single (.s (B ⬝ NatPair ⬝ tf) tg cn)
  exact isChurch_trans _
    (hs.trans (Steps.appLeft (tg ⬝ cn) (B_def NatPair tf cn)))
    (natPair_correct a b _ _ (hf n cn hcn a ha) (hg n cn hcn b hb))

/-! ## Compiler plumbing for primitive recursion and minimization -/

def PrecStepPoly (tg : Term) : Polynomial 3 :=
  tg ⬝' (NatPair ⬝' &0 ⬝' (NatPair ⬝' (Pred ⬝' &1) ⬝' &2))

def PrecStep (tg : Term) : Term := (PrecStepPoly tg).toTerm

theorem precStep_def (tg a cn previous : Term) :
    (PrecStep tg ⬝ a ⬝ cn ⬝ previous) ↠
      tg ⬝ (NatPair ⬝ a ⬝ (NatPair ⬝ (Pred ⬝ cn) ⬝ previous)) :=
  (PrecStepPoly tg).toTerm_correct [a, cn, previous] (by simp)

def PrecTransPoly (tf tg : Term) : Polynomial 1 :=
  Rec ⬝' (tf ⬝' (NatUnpairLeft ⬝' &0)) ⬝'
    (PrecStep tg ⬝' (NatUnpairLeft ⬝' &0)) ⬝'
    (NatUnpairRight ⬝' &0)

def PrecTrans (tf tg : Term) : Term := (PrecTransPoly tf tg).toTerm

theorem precTrans_def (tf tg cn : Term) :
    (PrecTrans tf tg ⬝ cn) ↠
      Rec ⬝ (tf ⬝ (NatUnpairLeft ⬝ cn)) ⬝
        (PrecStep tg ⬝ (NatUnpairLeft ⬝ cn)) ⬝
        (NatUnpairRight ⬝ cn) :=
  (PrecTransPoly tf tg).toTerm_correct [cn] (by simp)

def RFindTransPoly (tf : Term) : Polynomial 1 :=
  RFindAbove ⬝' (NatUnpairRight ⬝' &0) ⬝'
    (B ⬝' tf ⬝' (NatPair ⬝' (NatUnpairLeft ⬝' &0)))

def RFindTrans (tf : Term) : Term := (RFindTransPoly tf).toTerm

theorem rfindTrans_def (tf cn : Term) :
    (RFindTrans tf ⬝ cn) ↠
      RFindAbove ⬝ (NatUnpairRight ⬝ cn) ⬝
        (B ⬝ tf ⬝ (NatPair ⬝ (NatUnpairLeft ⬝ cn))) :=
  (RFindTransPoly tf).toTerm_correct [cn] (by simp)

/-! ## Translation -/

/-- Translate Mathlib's unary partial-recursive codes to closed SKI terms. -/
def codeToSKI : Code → Term
  | .zero => k ⬝ Zero
  | .succ => Succ
  | .left => NatUnpairLeft
  | .right => NatUnpairRight
  | .pair f g => s ⬝ (B ⬝ NatPair ⬝ codeToSKI f) ⬝ codeToSKI g
  | .comp f g => B ⬝ codeToSKI f ⬝ codeToSKI g
  | .prec f g => PrecTrans (codeToSKI f) (codeToSKI g)
  | .rfind' f => RFindTrans (codeToSKI f)

private theorem zero_computes : Computes (k ⬝ Zero) (Code.eval .zero) :=
  computes_of_total (fun _ => 0) (fun _ => rfl)
    (fun _ _ _ => isChurch_trans 0 (Steps.single (.k Zero _)) zero_correct)

private theorem succ_computes : Computes Succ (Code.eval .succ) :=
  computes_of_total (· + 1) (fun _ => rfl) succ_correct

private theorem left_computes : Computes NatUnpairLeft (Code.eval .left) :=
  computes_of_total (fun n => (Nat.unpair n).1) (fun _ => rfl) natUnpairLeft_correct

private theorem right_computes : Computes NatUnpairRight (Code.eval .right) :=
  computes_of_total (fun n => (Nat.unpair n).2) (fun _ => rfl) natUnpairRight_correct

private theorem prec_rec_correct (f g : Code) (tf tg : Term)
    (ihf : Computes tf f.eval) (ihg : Computes tg g.eval)
    (a : Nat) (ca : Term) (hca : IsChurch a ca) :
    ∀ b m, m ∈ Code.eval (f.prec g) (Nat.pair a b) →
      ∀ cb, IsChurch b cb →
        IsChurch m (Rec ⬝ (tf ⬝ ca) ⬝ (PrecStep tg ⬝ ca) ⬝ cb) := by
  intro b
  induction b with
  | zero =>
      intro m hm cb hcb
      rw [Code.eval_prec_zero] at hm
      exact isChurch_trans _ (rec_zero _ _ cb hcb) (ihf a ca hca m hm)
  | succ b ih =>
      intro m hm cb hcb
      rw [Code.eval_prec_succ] at hm
      obtain ⟨previous, hprevious, hm⟩ := Part.mem_bind_iff.mp hm
      have hpred : IsChurch b (Pred ⬝ cb) := pred_correct (b + 1) cb hcb
      set step := PrecStep tg ⬝ ca
      set base := tf ⬝ ca
      have hrec := ih previous hprevious (Pred ⬝ cb) hpred
      have hinner := natPair_correct b previous (Pred ⬝ cb)
        (Rec ⬝ base ⬝ step ⬝ (Pred ⬝ cb)) hpred hrec
      have hfull := natPair_correct a (Nat.pair b previous) ca
        (NatPair ⬝ (Pred ⬝ cb) ⬝ (Rec ⬝ base ⬝ step ⬝ (Pred ⬝ cb))) hca hinner
      have hresult := ihg _ _ hfull m hm
      exact isChurch_trans _
        ((rec_succ b base step cb hcb).trans
          (precStep_def tg ca cb (Rec ⬝ base ⬝ step ⬝ (Pred ⬝ cb)))) hresult

private theorem rfind_eval_aux {f : Code} {a offset j : Nat} {b : Bool}
    (h : b ∈ (fun m => decide (m = 0)) <$> f.eval (Nat.pair a (j + offset))) :
    ∃ value, decide (value = 0) = b ∧ value ∈ f.eval (Nat.pair a (offset + j)) := by
  obtain ⟨value, hvalue, rfl⟩ := (Part.mem_map_iff _).mp h
  rw [Nat.add_comm] at hvalue
  exact ⟨value, rfl, hvalue⟩

private theorem rfind_eval_root {f : Code} {a offset root : Nat}
    (hroot : root ∈ Nat.rfind (fun n =>
      (fun m => decide (m = 0)) <$> f.eval (Nat.pair a (n + offset)))) :
    0 ∈ f.eval (Nat.pair a (offset + root)) := by
  obtain ⟨value, hzero, hvalue⟩ := rfind_eval_aux (Nat.rfind_spec hroot)
  obtain rfl : value = 0 := by simpa using hzero
  exact hvalue

private theorem rfind_eval_positive_below {f : Code} {a offset root : Nat}
    (hroot : root ∈ Nat.rfind (fun n =>
      (fun m => decide (m = 0)) <$> f.eval (Nat.pair a (n + offset)))) :
    ∀ i < root, ∃ value, value ≠ 0 ∧ value ∈ f.eval (Nat.pair a (offset + i)) := by
  intro i hi
  obtain ⟨value, hpositive, hvalue⟩ := rfind_eval_aux (Nat.rfind_min hroot hi)
  exact ⟨value, by simpa using hpositive, hvalue⟩

private theorem prec_computes {f g : Code} {tf tg : Term}
    (ihf : Computes tf f.eval) (ihg : Computes tg g.eval) :
    Computes (PrecTrans tf tg) (f.prec g).eval := by
  intro n cn hcn m hm
  have hleft := natUnpairLeft_correct n cn hcn
  have hright := natUnpairRight_correct n cn hcn
  rw [← Nat.pair_unpair n] at hm
  exact isChurch_trans _ (precTrans_def tf tg cn)
    (prec_rec_correct f g tf tg ihf ihg (Nat.unpair n).1 (NatUnpairLeft ⬝ cn) hleft
      (Nat.unpair n).2 m hm (NatUnpairRight ⬝ cn) hright)

private theorem rfind_computes {f : Code} {tf : Term} (ihf : Computes tf f.eval) :
    Computes (RFindTrans tf) (Code.rfind' f).eval := by
  intro n cn hcn result hresult
  have hleft := natUnpairLeft_correct n cn hcn
  have hright := natUnpairRight_correct n cn hcn
  simp only [Code.eval, Nat.unpaired] at hresult
  set a := (Nat.unpair n).1
  set offset := (Nat.unpair n).2
  obtain ⟨root, hroot, rfl⟩ := (Part.mem_map_iff _).mp hresult
  set callback := B ⬝ tf ⬝ (NatPair ⬝ (NatUnpairLeft ⬝ cn))
  have hcallback : ∀ i ci, IsChurch i ci → ∀ value,
      value ∈ f.eval (Nat.pair a i) → IsChurch value (callback ⬝ ci) := by
    intro i ci hci value hvalue
    exact isChurch_trans _ (B_def tf (NatPair ⬝ (NatUnpairLeft ⬝ cn)) ci)
      (ihf _ _ (natPair_correct a i (NatUnpairLeft ⬝ cn) ci hleft hci) value hvalue)
  have hsearch := RFindAbove_correct callback (NatUnpairRight ⬝ cn) root offset hright
    (fun y hy => hcallback (offset + root) y hy 0 (rfind_eval_root hroot))
    (fun i hi y hy => by
      obtain ⟨value, hne, hvalue⟩ := rfind_eval_positive_below hroot i hi
      exact ⟨value - 1,
        Nat.succ_pred_eq_of_ne_zero hne ▸ hcallback (offset + i) y hy value hvalue⟩)
  rw [Nat.add_comm] at hsearch
  exact isChurch_trans _ (rfindTrans_def tf cn) hsearch

/-- Defined-case correctness for every partial-recursive code. -/
theorem codeToSKI_correct (code : Code) : Computes (codeToSKI code) code.eval := by
  induction code with
  | zero => exact zero_computes
  | succ => exact succ_computes
  | left => exact left_computes
  | right => exact right_computes
  | pair f g ihf ihg =>
      simpa [codeToSKI, Code.eval] using pair_computes ihf ihg
  | comp f g ihf ihg =>
      simpa [codeToSKI, Code.eval] using comp_computes ihf ihg
  | prec f g ihf ihg => simpa [codeToSKI] using prec_computes ihf ihg
  | rfind' f ihf => simpa [codeToSKI] using rfind_computes ihf

/-- Pointwise form of the main theorem, exposing the exact defined-case guarantee. -/
theorem codeToSKI_defined {code : Code} {n m : Nat} (hm : m ∈ code.eval n) :
    ∀ cn, IsChurch n cn → IsChurch m (codeToSKI code ⬝ cn) := by
  intro cn hcn
  exact codeToSKI_correct code n cn hcn m hm

/-- Every Mathlib `Nat.Partrec` function has a defined-case SKI realizer. -/
theorem natPartrec_skiComputable (f : Nat →. Nat) (hf : Nat.Partrec f) : Computable f := by
  obtain ⟨code, rfl⟩ := Code.exists_code.mp hf
  exact ⟨codeToSKI code, codeToSKI_correct code⟩

end CombinatoryLogic.SKI.Term
