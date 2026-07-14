import PAFiniteBasisReduction.TraceSupportRank

/-!
# Exact raw semantics of the fixed program evaluator
-/

namespace LeanProofs
namespace PAFiniteBasisReduction

open SetTheory PA

universe u

namespace FiniteSkolemCut
namespace ProgramTrace

/-- Evaluator formula in the environment convention used by the proper-cut
contract: slot 0 is output, slot 1 is code, and slot 2 is the seed. -/
def traceEvaluator (rank : Nat) : PA.Formula :=
  evaluator rank (PA.Term.var 1) (PA.Term.var 0) (PA.Term.var 2)

/-- The row environment appearing beneath the evaluator's two table
witnesses, bounded index, and row-value witness. -/
def evaluatorRowEnv {alpha : Type u}
    (rowValue rowCode betaStep betaCode : alpha)
    (tail : Nat → alpha) : Nat → alpha :=
  scons rowValue (scons rowCode (scons betaStep (scons betaCode tail)))

/-- Exact semantic normal form of `evaluator`.  This lemma is purely an
unfolding theorem and assumes no arithmetic laws. -/
theorem sat_evaluator_iff {alpha : Type u} (M : PA.PreModel alpha)
    (rank : Nat) (code value star : PA.Term) (e : Nat → alpha) :
    PA.Formula.Sat M e (evaluator rank code value star) ↔
      ∃ betaCode betaStep,
        RawBetaEntry M (PA.Term.eval M e value)
          betaCode betaStep (PA.Term.eval M e code) ∧
        ∀ rowCode,
          RawLe M rowCode (PA.Term.eval M e code) →
          ∃ rowValue,
            RawBetaEntry M rowValue betaCode betaStep rowCode ∧
            PA.Formula.Sat M
              (evaluatorRowEnv rowValue rowCode betaStep betaCode e)
              (programStep rank
                (PA.Term.var 1) (PA.Term.var 0)
                (PA.Term.var 3) (PA.Term.var 2)
                (liftTerm 4 star)) := by
  simp only [evaluator, PA.Formula.Sat]
  constructor
  · rintro ⟨betaCode, betaStep, htarget, hrows⟩
    refine ⟨betaCode, betaStep, ?_, ?_⟩
    · have hraw := (sat_betaTermTermAt_iff_raw M
        (liftTerm 2 value) (PA.Term.var 1) (PA.Term.var 0)
        (liftTerm 2 code)
        (scons betaStep (scons betaCode e))).mp htarget
      simpa [liftTerm, PA.Term.eval_rename, PA.Term.eval, scons] using hraw
    · intro rowCode hle
      have hleSat : PA.Formula.Sat M
          (scons rowCode (scons betaStep (scons betaCode e)))
          (PA.Formula.leTermAt (PA.Term.var 0) (liftTerm 3 code)) := by
        apply (sat_leTermAt_iff_raw M
          (PA.Term.var 0) (liftTerm 3 code)
          (scons rowCode (scons betaStep (scons betaCode e)))).mpr
        simpa [liftTerm, PA.Term.eval_rename, PA.Term.eval, scons] using hle
      rcases hrows rowCode hleSat with ⟨rowValue, hentry, hstep⟩
      refine ⟨rowValue, ?_, ?_⟩
      · have hraw := (sat_betaTermTermAt_iff_raw M
          (PA.Term.var 0) (PA.Term.var 3) (PA.Term.var 2)
          (PA.Term.var 1)
          (scons rowValue
            (scons rowCode (scons betaStep (scons betaCode e))))).mp hentry
        simpa [PA.Term.eval, scons] using hraw
      · simpa [evaluatorRowEnv] using hstep
  · rintro ⟨betaCode, betaStep, htarget, hrows⟩
    refine ⟨betaCode, betaStep, ?_, ?_⟩
    · apply (sat_betaTermTermAt_iff_raw M
        (liftTerm 2 value) (PA.Term.var 1) (PA.Term.var 0)
        (liftTerm 2 code)
        (scons betaStep (scons betaCode e))).mpr
      simpa [liftTerm, PA.Term.eval_rename, PA.Term.eval, scons] using htarget
    · intro rowCode hleSat
      have hleRaw := (sat_leTermAt_iff_raw M
        (PA.Term.var 0) (liftTerm 3 code)
        (scons rowCode (scons betaStep (scons betaCode e)))).mp hleSat
      have hle : RawLe M rowCode (PA.Term.eval M e code) := by
        simpa [liftTerm, PA.Term.eval_rename, PA.Term.eval, scons] using hleRaw
      rcases hrows rowCode hle with ⟨rowValue, hentry, hstep⟩
      refine ⟨rowValue, ?_, ?_⟩
      · apply (sat_betaTermTermAt_iff_raw M
          (PA.Term.var 0) (PA.Term.var 3) (PA.Term.var 2)
          (PA.Term.var 1)
          (scons rowValue
            (scons rowCode (scons betaStep (scons betaCode e))))).mpr
        simpa [PA.Term.eval, scons] using hentry
      · simpa [evaluatorRowEnv] using hstep

/-- Assemble evaluator satisfaction from an externally finite standard table.
All arithmetic-specific work is isolated in `hbounded`; the theorem itself
only instantiates the exact semantic normal form above. -/
theorem sat_evaluator_of_standard_table {alpha : Type u}
    (M : PA.PreModel alpha) (rank target : Nat)
    (code value star : PA.Term) (e : Nat → alpha)
    (betaCode betaStep : alpha) (rowValue : Nat → alpha)
    (hcode : PA.Term.eval M e code = PA.Term.numeralValue M target)
    (hvalue : PA.Term.eval M e value = rowValue target)
    (hbounded : ∀ rowCode,
      RawLe M rowCode (PA.Term.numeralValue M target) →
        ∃ k, k ≤ target ∧ rowCode = PA.Term.numeralValue M k)
    (hentry : ∀ k, k ≤ target →
      RawBetaEntry M (rowValue k) betaCode betaStep
        (PA.Term.numeralValue M k))
    (hstep : ∀ k, k ≤ target →
      PA.Formula.Sat M
        (evaluatorRowEnv (rowValue k) (PA.Term.numeralValue M k)
          betaStep betaCode e)
        (programStep rank
          (PA.Term.var 1) (PA.Term.var 0)
          (PA.Term.var 3) (PA.Term.var 2)
          (liftTerm 4 star))) :
    PA.Formula.Sat M e (evaluator rank code value star) := by
  apply (sat_evaluator_iff M rank code value star e).mpr
  refine ⟨betaCode, betaStep, ?_, ?_⟩
  · rw [hcode, hvalue]
    exact hentry target (Nat.le_refl target)
  · intro rowCode hle
    have hle' : RawLe M rowCode (PA.Term.numeralValue M target) := by
      simpa [hcode] using hle
    rcases hbounded rowCode hle' with ⟨k, hk, rfl⟩
    exact ⟨rowValue k, hentry k hk, hstep k hk⟩

end ProgramTrace
end FiniteSkolemCut
end PAFiniteBasisReduction
end LeanProofs
