import PAFiniteBasisReduction.TotalRowCases
import PAFiniteBasisReduction.EvaluatorSemantics
import PAFiniteBasisReduction.EvaluatorCutContract

/-!
# Totality of the standard program trace
-/

namespace LeanProofs
namespace PAFiniteBasisReduction

open SetTheory PA

universe u

namespace FiniteSkolemCut
namespace ProgramTrace

/-- The canonical beta table satisfies the totalized row relation at every
standard code.  On a recognized code we use the genuine constructor; on a
malformed code the exhaustive decoder proves that the canonical value is
zero, and the guarded default is used exactly when no genuine descriptor
exists. -/
theorem sat_programStep_totalRow {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (generator : alpha) (hPA : RawPASatisfies M)
    (hLtRank : formulaRank traceLtFormula ≤ rank)
    (target : Nat) (betaCode betaStep : Carrier M S rank generator)
    (htable : ∀ child, child < target →
      RawBetaEntry (preModel M S rank generator)
        (hullProgramValue M S rank generator
          (totalRowProgram rank child))
        betaCode betaStep
        (PA.Term.numeralValue (preModel M S rank generator) child))
    (tail : Nat → Carrier M S rank generator) (starTerm : PA.Term)
    (hstar : PA.Term.eval (preModel M S rank generator) tail starTerm =
      (⟨generator, Hull.star⟩ : Carrier M S rank generator)) :
    PA.Formula.Sat (preModel M S rank generator)
      (evaluatorRowEnv
        (hullProgramValue M S rank generator
          (totalRowProgram rank target))
        (PA.Term.numeralValue (preModel M S rank generator) target)
        betaStep betaCode tail)
      (programStep rank
        (PA.Term.var 1) (PA.Term.var 0)
        (PA.Term.var 3) (PA.Term.var 2)
        (liftTerm 4 starTerm)) := by
  classical
  let KM := preModel M S rank generator
  let starK : Carrier M S rank generator := ⟨generator, Hull.star⟩
  let canonicalValue := hullProgramValue M S rank generator
    (totalRowProgram rank target)
  let rowEnv := evaluatorRowEnv canonicalValue
    (PA.Term.numeralValue KM target) betaStep betaCode tail
  change PA.Formula.Sat KM rowEnv
    (programStep rank (PA.Term.var 1) (PA.Term.var 0)
      (PA.Term.var 3) (PA.Term.var 2)
      (liftTerm 4 starTerm))
  rw [sat_programStep_iff]
  rcases canonicalStandardRowWitness_or_zero M S rank generator
      betaCode betaStep target htable with hcanonical | hzero
  · left
    apply sat_programCases_of_standardRowWitness M S rank generator hPA
      hLtRank target (PA.Term.var 1) (PA.Term.var 0)
      (PA.Term.var 3) (PA.Term.var 2) (liftTerm 4 starTerm)
      rowEnv
    · simp [rowEnv, KM, evaluatorRowEnv, PA.Term.eval, scons]
    · simpa [rowEnv, evaluatorRowEnv, canonicalValue, starK, hstar,
        liftTerm, PA.Term.eval_rename, PA.Term.eval, scons] using hcanonical
  · by_cases hshape : ∃ v : Carrier M S rank generator,
        StandardRowWitness KM rank target betaCode betaStep starK v
    · left
      rcases hshape with ⟨v, hv⟩
      have hcanonical := canonicalStandardRowWitness_of_shape M S rank
        generator target hv htable
      apply sat_programCases_of_standardRowWitness M S rank generator hPA
        hLtRank target (PA.Term.var 1) (PA.Term.var 0)
        (PA.Term.var 3) (PA.Term.var 2) (liftTerm 4 starTerm)
        rowEnv
      · simp [rowEnv, KM, evaluatorRowEnv, PA.Term.eval, scons]
      · simpa [rowEnv, evaluatorRowEnv, canonicalValue, starK, hstar,
          liftTerm, PA.Term.eval_rename, PA.Term.eval, scons] using hcanonical
    · right
      constructor
      · apply (sat_noProgramCase_iff KM rank
          (PA.Term.var 1) (PA.Term.var 3) (PA.Term.var 2)
          (liftTerm 4 starTerm) rowEnv).mpr
        rintro ⟨proposed, hcases⟩
        apply hshape
        have hwitness := standardRowWitness_of_sat_programCases
          M S rank generator hPA target
          (liftTerm 1 (PA.Term.var 1)) (PA.Term.var 0)
          (liftTerm 1 (PA.Term.var 3)) (liftTerm 1 (PA.Term.var 2))
          (liftTerm 1 (liftTerm 4 starTerm))
          (scons proposed rowEnv)
          (by simp [rowEnv, KM, evaluatorRowEnv, liftTerm,
            PA.Term.eval_rename, PA.Term.eval, scons]) hcases
        refine ⟨proposed, ?_⟩
        simpa [rowEnv, evaluatorRowEnv, starK, hstar, liftTerm,
          PA.Term.eval_rename, PA.Term.eval, scons] using hwitness
      · simp [rowEnv, KM, canonicalValue, hzero, evaluatorRowEnv,
          PA.Term.eval, scons]

/-- The fixed evaluator formula evaluates every standard code to the
canonical total-row value.  Its beta witnesses are Program-denoted, hence
are elements of the hull. -/
theorem sat_evaluator_totalRow {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (generator : alpha) (hPA : RawPASatisfies M)
    (hSupport : ProgramBetaCoding.supportRank ≤ rank)
    (hLtRank : formulaRank traceLtFormula ≤ rank)
    (hBetaRank : formulaRank traceBetaFormula ≤ rank)
    (target : Nat) (code value starTerm : PA.Term)
    (e : Nat → Carrier M S rank generator)
    (hcode : PA.Term.eval (preModel M S rank generator) e code =
      PA.Term.numeralValue (preModel M S rank generator) target)
    (hvalue : PA.Term.eval (preModel M S rank generator) e value =
      hullProgramValue M S rank generator (totalRowProgram rank target))
    (hstar : PA.Term.eval (preModel M S rank generator) e starTerm =
      (⟨generator, Hull.star⟩ : Carrier M S rank generator)) :
    PA.Formula.Sat (preModel M S rank generator) e
      (evaluator rank code value starTerm) := by
  let KM := preModel M S rank generator
  let rowValue : Nat → Carrier M S rank generator := fun k =>
    hullProgramValue M S rank generator (totalRowProgram rank k)
  rcases finite_total_row_beta_hull hPA S rank generator hSupport hBetaRank
      target with ⟨codeProgram, stepProgram, htable⟩
  let betaCode := hullProgramValue M S rank generator codeProgram
  let betaStep := hullProgramValue M S rank generator stepProgram
  apply sat_evaluator_of_standard_table KM rank target code value starTerm e
    betaCode betaStep rowValue
  · exact hcode
  · exact hvalue
  · intro rowCode hle
    exact hull_rawLe_numeralValue_cases M S rank generator hPA target hle
  · intro k hk
    exact htable k hk
  · intro k hk
    apply sat_programStep_totalRow M S rank generator hPA hLtRank k
      betaCode betaStep
    · intro child hchild
      exact htable child (Nat.le_trans (Nat.le_of_lt hchild) hk)
    · exact hstar

/-- The evaluator relation at the code of a genuine program returns the hull
element denoted by that program. -/
theorem traceEvaluator_evaluates_program {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (generator : alpha) (hPA : RawPASatisfies M)
    (hSupport : ProgramBetaCoding.supportRank ≤ rank)
    (hLtRank : formulaRank traceLtFormula ≤ rank)
    (hBetaRank : formulaRank traceBetaFormula ≤ rank)
    (p : Program rank) :
    EvaluatorCutContract.Evaluates (preModel M S rank generator)
      (traceEvaluator rank)
      (⟨generator, Hull.star⟩ : Carrier M S rank generator)
      (PA.Term.numeralValue (preModel M S rank generator) (Program.code p))
      (hullProgramValue M S rank generator p) := by
  let KM := preModel M S rank generator
  let starK : Carrier M S rank generator := ⟨generator, Hull.star⟩
  let output := hullProgramValue M S rank generator p
  let code := PA.Term.numeralValue KM (Program.code p)
  let e := EvaluatorCutContract.evalEnv KM starK code output
  change PA.Formula.Sat KM e
    (evaluator rank (PA.Term.var 1) (PA.Term.var 0) (PA.Term.var 2))
  apply sat_evaluator_totalRow M S rank generator hPA hSupport hLtRank
    hBetaRank (Program.code p) (PA.Term.var 1) (PA.Term.var 0)
    (PA.Term.var 2) e
  · rfl
  · change output = hullProgramValue M S rank generator
      (totalRowProgram rank (Program.code p))
    exact (hullProgramValue_totalRow_code M S rank generator p).symm
  · rfl

/-- Every hull element is hit at a standard code by the fixed trace
evaluator. -/
theorem traceEvaluator_standardCode_total {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (generator : alpha) (hPA : RawPASatisfies M)
    (hSupport : ProgramBetaCoding.supportRank ≤ rank)
    (hLtRank : formulaRank traceLtFormula ≤ rank)
    (hBetaRank : formulaRank traceBetaFormula ≤ rank) :
    ∀ output : Carrier M S rank generator, ∃ code : Nat,
      EvaluatorCutContract.Evaluates (preModel M S rank generator)
        (traceEvaluator rank)
        (⟨generator, Hull.star⟩ : Carrier M S rank generator)
        (PA.Term.numeralValue (preModel M S rank generator) code) output := by
  intro output
  rcases Hull.exists_program output.property with ⟨p, hp⟩
  have houtput : output = hullProgramValue M S rank generator p := by
    apply Subtype.ext
    exact hp.symm
  refine ⟨Program.code p, ?_⟩
  rw [houtput]
  exact traceEvaluator_evaluates_program M S rank generator hPA hSupport
    hLtRank hBetaRank p

end ProgramTrace
end FiniteSkolemCut

end PAFiniteBasisReduction
end LeanProofs
