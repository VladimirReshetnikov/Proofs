import PAFiniteBasisReduction.ProgramTrace

/-!
# Beta codes denoted by finite Skolem programs

Ambient PA proves that every externally finite list has a beta code, but those
existential witnesses need not belong to a Skolem hull.  This module closes
that gap using two fixed instances of the existing `Program.exSkolem`
constructor: one chooses the canonical prepend step and the second chooses
the canonical prepend code.  External recursion therefore returns programs
denoting both beta parameters.
-/

namespace LeanProofs
namespace PAFiniteBasisReduction

open SetTheory PA

universe u

namespace FiniteSkolemCut
namespace ProgramBetaCoding

/-- Fixed rank support for the two staged prepend selectors and their five
argument slots. -/
def supportRank : Nat :=
  max 5 (max
    (formulaRank (PA.Formula.ex canonicalBetaPrependStepBody))
    (formulaRank (PA.Formula.ex canonicalBetaPrependCodeBody)))

theorem five_le_supportRank : 5 ≤ supportRank := by
  exact Nat.le_max_left _ _

theorem stepBody_rank_le_supportRank :
    formulaRank (PA.Formula.ex canonicalBetaPrependStepBody) ≤
      supportRank := by
  exact Nat.le_trans (Nat.le_max_left _ _)
    (Nat.le_max_right _ _)

theorem codeBody_rank_le_supportRank :
    formulaRank (PA.Formula.ex canonicalBetaPrependCodeBody) ≤
      supportRank := by
  exact Nat.le_trans (Nat.le_max_right _ _)
    (Nat.le_max_right _ _)

end ProgramBetaCoding
namespace Program

/-- Program denoting a standard numeral. -/
def numeral : Nat → Program rank
  | 0 => .zero
  | n + 1 => .succ (numeral n)

@[simp] theorem eval_numeral {alpha : Type u} (M : PA.PreModel alpha)
    (S : CanonicalSelectors M) (star : alpha) (n : Nat) :
    eval M S star (numeral (rank := rank) n) = PA.Term.numeralValue M n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [numeral, eval, PA.Term.numeralValue, ih]

/-- Four argument programs followed by zero padding. -/
def helperArgs4 (a b c d : Program rank) : Fin rank → Program rank :=
  fun i =>
    if i.val = 0 then a else
    if i.val = 1 then b else
    if i.val = 2 then c else
    if i.val = 3 then d else .zero

/-- Five argument programs followed by zero padding. -/
def helperArgs5 (a b c d f : Program rank) : Fin rank → Program rank :=
  fun i =>
    if i.val = 0 then a else
    if i.val = 1 then b else
    if i.val = 2 then c else
    if i.val = 3 then d else
    if i.val = 4 then f else .zero

/-- First staged selector: choose the canonical beta-prepend step. -/
def canonicalBetaPrependStepProgram
    (hSupport : ProgramBetaCoding.supportRank ≤ rank)
    (sourceCode sourceStep head bound : Program rank) : Program rank :=
  .exSkolem canonicalBetaPrependStepBody
    (Nat.le_trans ProgramBetaCoding.stepBody_rank_le_supportRank hSupport)
    (helperArgs4 sourceCode sourceStep head bound)

/-- Second staged selector: choose the canonical beta-prepend code for the
already selected step. -/
def canonicalBetaPrependCodeProgram
    (hSupport : ProgramBetaCoding.supportRank ≤ rank)
    (sourceCode sourceStep head bound : Program rank) : Program rank :=
  let step := canonicalBetaPrependStepProgram hSupport
    sourceCode sourceStep head bound
  .exSkolem canonicalBetaPrependCodeBody
    (Nat.le_trans ProgramBetaCoding.codeBody_rank_le_supportRank hSupport)
    (helperArgs5 step sourceCode sourceStep head bound)

theorem argsEnv_helperArgs4 {alpha : Type u} (M : PA.PreModel alpha)
    (S : CanonicalSelectors M) (star : alpha)
    (hSupport : ProgramBetaCoding.supportRank ≤ rank)
    (a b c d : Program rank) :
    argsEnv M S star (helperArgs4 a b c d) =
      canonicalBetaPrependEnv M (eval M S star a) (eval M S star b)
        (eval M S star c) (eval M S star d) := by
  funext i
  have h5 : 5 ≤ rank := Nat.le_trans
    ProgramBetaCoding.five_le_supportRank hSupport
  by_cases hi : i < rank
  · rw [argsEnv, boundedEnv_of_lt M _ hi]
    by_cases h0 : i = 0
    · subst i
      simp [helperArgs4, canonicalBetaPrependEnv, scons]
    by_cases h1 : i = 1
    · subst i
      simp [helperArgs4, canonicalBetaPrependEnv, scons]
    by_cases h2 : i = 2
    · subst i
      simp [helperArgs4, canonicalBetaPrependEnv, scons]
    by_cases h3 : i = 3
    · subst i
      simp [helperArgs4, canonicalBetaPrependEnv, scons]
    · obtain ⟨k, rfl⟩ : ∃ k, i = k + 4 := ⟨i - 4, by omega⟩
      simp [helperArgs4, canonicalBetaPrependEnv, scons, eval]
  · rw [argsEnv, boundedEnv_of_not_lt M _ hi]
    have hi5 : 5 ≤ i := by omega
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 5 := ⟨i - 5, by omega⟩
    simp [canonicalBetaPrependEnv, scons]

theorem argsEnv_helperArgs5 {alpha : Type u} (M : PA.PreModel alpha)
    (S : CanonicalSelectors M) (star : alpha)
    (hSupport : ProgramBetaCoding.supportRank ≤ rank)
    (a b c d f : Program rank) :
    argsEnv M S star (helperArgs5 a b c d f) =
      scons (eval M S star a)
        (canonicalBetaPrependEnv M (eval M S star b) (eval M S star c)
          (eval M S star d) (eval M S star f)) := by
  funext i
  have h5 : 5 ≤ rank := Nat.le_trans
    ProgramBetaCoding.five_le_supportRank hSupport
  by_cases hi : i < rank
  · rw [argsEnv, boundedEnv_of_lt M _ hi]
    by_cases h0 : i = 0
    · subst i
      simp [helperArgs5, scons]
    by_cases h1 : i = 1
    · subst i
      simp [helperArgs5, canonicalBetaPrependEnv, scons]
    by_cases h2 : i = 2
    · subst i
      simp [helperArgs5, canonicalBetaPrependEnv, scons]
    by_cases h3 : i = 3
    · subst i
      simp [helperArgs5, canonicalBetaPrependEnv, scons]
    by_cases h4 : i = 4
    · subst i
      simp [helperArgs5, canonicalBetaPrependEnv, scons]
    · obtain ⟨k, rfl⟩ : ∃ k, i = k + 5 := ⟨i - 5, by omega⟩
      simp [helperArgs5, canonicalBetaPrependEnv, scons, eval]
  · rw [argsEnv, boundedEnv_of_not_lt M _ hi]
    have hi5 : 5 ≤ i := by omega
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 5 := ⟨i - 5, by omega⟩
    simp [canonicalBetaPrependEnv, scons]

@[simp] theorem eval_canonicalBetaPrependStepProgram {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M) (star : alpha)
    (hSupport : ProgramBetaCoding.supportRank ≤ rank)
    (sourceCode sourceStep head bound : Program rank) :
    eval M S star (canonicalBetaPrependStepProgram hSupport
      sourceCode sourceStep head bound) =
      canonicalBetaPrependStep S
        (eval M S star sourceCode) (eval M S star sourceStep)
        (eval M S star head) (eval M S star bound) := by
  simp only [canonicalBetaPrependStepProgram, eval,
    canonicalBetaPrependStep]
  change canonicalValue S canonicalBetaPrependStepBody
      (argsEnv M S star (helperArgs4 sourceCode sourceStep head bound)) = _
  rw [argsEnv_helperArgs4 M S star hSupport]

@[simp] theorem eval_canonicalBetaPrependCodeProgram {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M) (star : alpha)
    (hSupport : ProgramBetaCoding.supportRank ≤ rank)
    (sourceCode sourceStep head bound : Program rank) :
    eval M S star (canonicalBetaPrependCodeProgram hSupport
      sourceCode sourceStep head bound) =
      canonicalBetaPrependCode S
        (eval M S star sourceCode) (eval M S star sourceStep)
        (eval M S star head) (eval M S star bound) := by
  simp only [canonicalBetaPrependCodeProgram, eval,
    canonicalBetaPrependCode]
  change canonicalValue S canonicalBetaPrependCodeBody
      (argsEnv M S star
        (helperArgs5
          (canonicalBetaPrependStepProgram hSupport
            sourceCode sourceStep head bound)
          sourceCode sourceStep head bound)) = _
  rw [argsEnv_helperArgs5 M S star hSupport]
  simp only [eval_canonicalBetaPrependStepProgram]

end Program

namespace ProgramBetaCoding

/-- Every externally finite list of program-denoted values has beta-code and
beta-step witnesses which are themselves denoted by programs. -/
theorem finite_list_beta_programs {alpha : Type u}
    {M : PA.PreModel alpha} (hPA : RawPASatisfies M)
    (S : CanonicalSelectors M) (star : alpha)
    (hSupport : supportRank ≤ rank) (ps : List (Program rank)) :
    ∃ codeProgram stepProgram : Program rank,
      RawBetaCodesList M (ps.map (Program.eval M S star))
        (Program.eval M S star codeProgram)
        (Program.eval M S star stepProgram) := by
  induction ps with
  | nil =>
      refine ⟨.zero, .zero, ?_⟩
      intro i
      exact Fin.elim0 i
  | cons head tail ih =>
      rcases ih with ⟨sourceCode, sourceStep, hsource⟩
      let boundProgram : Program rank := Program.numeral tail.length
      have hprefix : ∀ idx,
          RawLt M idx (Program.eval M S star boundProgram) →
            ∃ out, RawBetaEntry M out
              (Program.eval M S star sourceCode)
              (Program.eval M S star sourceStep) idx := by
        intro idx hlt
        have hlt' : RawLt M idx
            (PA.Term.numeralValue M tail.length) := by
          simpa [boundProgram] using hlt
        rcases rawLt_numeralValue_cases hPA tail.length hlt' with
          ⟨k, hk, rfl⟩
        let i : Fin (tail.map (Program.eval M S star)).length :=
          ⟨k, by simpa using hk⟩
        exact ⟨(tail.map (Program.eval M S star)).get i, hsource i⟩
      let targetStep : Program rank :=
        Program.canonicalBetaPrependStepProgram hSupport
          sourceCode sourceStep head boundProgram
      let targetCode : Program rank :=
        Program.canonicalBetaPrependCodeProgram hSupport
          sourceCode sourceStep head boundProgram
      have hcanon := canonicalBetaPrepend_spec hPA S
        (Program.eval M S star sourceCode)
        (Program.eval M S star sourceStep)
        (Program.eval M S star head)
        (Program.eval M S star boundProgram) hprefix
      have hhead : RawBetaEntry M (Program.eval M S star head)
          (Program.eval M S star targetCode)
          (Program.eval M S star targetStep) M.zero := by
        simpa [targetCode, targetStep] using hcanon.1
      have hshift : ∀ idx,
          RawLt M idx (Program.eval M S star boundProgram) → ∀ out,
          RawBetaEntry M out
            (Program.eval M S star sourceCode)
            (Program.eval M S star sourceStep) idx →
          RawBetaEntry M out
            (Program.eval M S star targetCode)
            (Program.eval M S star targetStep) (M.succ idx) := by
        simpa [targetCode, targetStep] using hcanon.2
      refine ⟨targetCode, targetStep, ?_⟩
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [RawBetaCodesList, PA.Term.numeralValue] using hhead
      · have hjlt : RawLt M (PA.Term.numeralValue M j.val)
            (Program.eval M S star boundProgram) := by
          have := rawLt_numeralValue_of_lt hPA j.isLt
          simpa [boundProgram] using this
        have hentry := hshift (PA.Term.numeralValue M j.val) hjlt
          ((tail.map (Program.eval M S star)).get j) (hsource j)
        simpa [RawBetaCodesList, PA.Term.numeralValue,
          List.get_eq_getElem] using hentry

end ProgramBetaCoding
end FiniteSkolemCut

end PAFiniteBasisReduction
end LeanProofs
