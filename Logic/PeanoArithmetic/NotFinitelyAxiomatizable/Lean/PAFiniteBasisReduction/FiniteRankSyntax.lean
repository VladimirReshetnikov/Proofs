import PAFiniteBasisReduction.Hierarchy

/-!
# Finiteness of rank-bounded arithmetic syntax

The rank functions in `Hierarchy` deliberately count both syntax depth and
variable indices.  This file makes the resulting finiteness claim explicit:
it recursively enumerates all terms and formulas of rank at most `n`, proves
the enumerations exact, and uses the formula enumeration to exhibit each
canonical PA rank fragment as a finite set.
-/

namespace LeanProofs
namespace PAFiniteBasisReduction

open SetTheory PA

/-- A predicate is finite when a list enumerates exactly its elements.
This is the list-based notion of finiteness used throughout this project. -/
def FinitelyEnumerated {alpha : Type} (P : alpha → Prop) : Prop :=
  ∃ xs : List alpha, ∀ x, P x ↔ x ∈ xs

/-- All ordered pairs drawn from a finite syntax collection. -/
private def syntaxPairs {alpha : Type} (xs : List alpha) :
    List (alpha × alpha) :=
  xs.flatMap (fun x => xs.map (fun y => (x, y)))

private theorem mem_syntaxPairs {alpha : Type} (xs : List alpha)
    (a b : alpha) :
    (a, b) ∈ syntaxPairs xs ↔ a ∈ xs ∧ b ∈ xs := by
  simp [syntaxPairs]

private theorem termRank_pos_local (t : PA.Term) : 0 < termRank t := by
  cases t <;> simp [termRank]

/-- Explicit enumeration of all PA terms of rank at most `n`. -/
def termsOfRankAtMost : Nat → List PA.Term
  | 0 => []
  | n + 1 =>
      (List.range (n + 1)).map PA.Term.var ++
      [PA.Term.zero] ++
      (termsOfRankAtMost n).map PA.Term.succ ++
      (syntaxPairs (termsOfRankAtMost n)).map
        (fun p => PA.Term.add p.1 p.2) ++
      (syntaxPairs (termsOfRankAtMost n)).map
        (fun p => PA.Term.mul p.1 p.2)

/-- The term enumeration is exact. -/
@[simp] theorem mem_termsOfRankAtMost (n : Nat) (t : PA.Term) :
    t ∈ termsOfRankAtMost n ↔ termRank t ≤ n := by
  induction n generalizing t with
  | zero =>
      simp only [termsOfRankAtMost, List.not_mem_nil, false_iff]
      have := termRank_pos_local t
      omega
  | succ n ih =>
      cases t with
      | var k =>
          simp [termsOfRankAtMost, syntaxPairs, termRank, ih,
            Nat.lt_succ_iff]
      | zero =>
          simp [termsOfRankAtMost, syntaxPairs, termRank, ih]
      | succ t =>
          simp [termsOfRankAtMost, syntaxPairs, termRank, ih]
      | add a b =>
          simp [termsOfRankAtMost, mem_syntaxPairs, termRank, ih,
            Nat.max_le]
      | mul a b =>
          simp [termsOfRankAtMost, mem_syntaxPairs, termRank, ih,
            Nat.max_le]

/-- Every rank-bounded collection of PA terms is finite. -/
theorem termRank_le_finite (n : Nat) :
    FinitelyEnumerated (fun t : PA.Term => termRank t ≤ n) :=
  ⟨termsOfRankAtMost n, fun t => (mem_termsOfRankAtMost n t).symm⟩

private theorem formulaRank_pos_local (phi : PA.Formula) :
    0 < formulaRank phi := by
  cases phi <;> simp [formulaRank]

/-- Explicit enumeration of all PA formulas of rank at most `n`. -/
def formulasOfRankAtMost : Nat → List PA.Formula
  | 0 => []
  | n + 1 =>
      [PA.Formula.bot] ++
      (syntaxPairs (termsOfRankAtMost n)).map
        (fun p => PA.Formula.eq p.1 p.2) ++
      (syntaxPairs (formulasOfRankAtMost n)).map
        (fun p => PA.Formula.imp p.1 p.2) ++
      (syntaxPairs (formulasOfRankAtMost n)).map
        (fun p => PA.Formula.and p.1 p.2) ++
      (syntaxPairs (formulasOfRankAtMost n)).map
        (fun p => PA.Formula.or p.1 p.2) ++
      (formulasOfRankAtMost n).map PA.Formula.all ++
      (formulasOfRankAtMost n).map PA.Formula.ex

/-- The formula enumeration is exact. -/
@[simp] theorem mem_formulasOfRankAtMost (n : Nat) (phi : PA.Formula) :
    phi ∈ formulasOfRankAtMost n ↔ formulaRank phi ≤ n := by
  induction n generalizing phi with
  | zero =>
      simp only [formulasOfRankAtMost, List.not_mem_nil, false_iff]
      have := formulaRank_pos_local phi
      omega
  | succ n ih =>
      cases phi with
      | eq a b =>
          simp [formulasOfRankAtMost, mem_syntaxPairs, formulaRank, ih,
            Nat.max_le]
      | bot =>
          simp [formulasOfRankAtMost, syntaxPairs, formulaRank, ih]
      | imp a b =>
          simp [formulasOfRankAtMost, mem_syntaxPairs, formulaRank, ih,
            Nat.max_le]
      | and a b =>
          simp [formulasOfRankAtMost, mem_syntaxPairs, formulaRank, ih,
            Nat.max_le]
      | or a b =>
          simp [formulasOfRankAtMost, mem_syntaxPairs, formulaRank, ih,
            Nat.max_le]
      | all a =>
          simp [formulasOfRankAtMost, syntaxPairs, formulaRank, ih]
      | ex a =>
          simp [formulasOfRankAtMost, syntaxPairs, formulaRank, ih]

/-- Every rank-bounded collection of PA formulas is finite. -/
theorem formulaRank_le_finite (n : Nat) :
    FinitelyEnumerated (fun phi : PA.Formula => formulaRank phi ≤ n) :=
  ⟨formulasOfRankAtMost n,
    fun phi => (mem_formulasOfRankAtMost n phi).symm⟩

/-- The fixed six non-induction PA axioms. -/
def paBaseAxioms : List PA.Formula :=
  [PA.Formula.sealPA PA.Formula.succInj,
    PA.Formula.sealPA PA.Formula.zeroNotSucc,
    PA.Formula.sealPA PA.Formula.addZero,
    PA.Formula.sealPA PA.Formula.addSucc,
    PA.Formula.sealPA PA.Formula.mulZero,
    PA.Formula.sealPA PA.Formula.mulSucc]

/-- Explicit finite enumeration of the canonical PA rank fragment. -/
def paRankFragmentAxioms (n : Nat) : List PA.Formula :=
  paBaseAxioms ++
    (formulasOfRankAtMost n).map
      (fun phi => PA.Formula.sealPA (PA.Formula.inductionForm phi))

/-- The fragment enumeration is exact. -/
@[simp] theorem mem_paRankFragmentAxioms (n : Nat) (f : PA.Formula) :
    f ∈ paRankFragmentAxioms n ↔ PARankFragment n f := by
  simp [paRankFragmentAxioms, paBaseAxioms, PARankFragment, eq_comm]

/-- Each canonical PA rank fragment is genuinely finite. -/
theorem paRankFragment_finite (n : Nat) :
    FinitelyEnumerated (PARankFragment n) :=
  ⟨paRankFragmentAxioms n,
    fun f => (mem_paRankFragmentAxioms n f).symm⟩

end PAFiniteBasisReduction
end LeanProofs
