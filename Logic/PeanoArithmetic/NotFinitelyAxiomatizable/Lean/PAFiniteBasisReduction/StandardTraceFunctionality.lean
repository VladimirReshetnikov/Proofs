import PAFiniteBasisReduction.TotalRowCases
import PAFiniteBasisReduction.EvaluatorSemantics
import PAFiniteBasisReduction.EvaluatorCutContract

/-!
# Strong-induction functionality of standard evaluator tables

This module lifts standard-row inversion to whole beta tables.  The induction
invariant identifies every standard table entry with the canonical value of
`totalRowProgram`; it therefore compares different beta-code/beta-step
witnesses, as required by the evaluator formula.
-/

namespace LeanProofs
namespace PAFiniteBasisReduction

open SetTheory PA

universe u

namespace FiniteSkolemCut
namespace ProgramTrace

/-- Semantic presentation of one standard `programStep` row, retaining the
outer evaluator environment and seed term verbatim. -/
def StandardProgramStep {alpha : Type u} (M : PA.PreModel alpha)
    (rank : Nat) (betaCode betaStep : alpha)
    (code : Nat) (value : alpha) (tail : Nat → alpha)
    (starTerm : PA.Term) : Prop :=
  PA.Formula.Sat M
    (evaluatorRowEnv value (PA.Term.numeralValue M code)
      betaStep betaCode tail)
    (programStep rank
      (PA.Term.var 1) (PA.Term.var 0)
      (PA.Term.var 3) (PA.Term.var 2)
      (liftTerm 4 starTerm))

/-- A beta table equipped with a total standard row through `target`. -/
structure StandardProgramTable {alpha : Type u} (M : PA.PreModel alpha)
    (rank : Nat) (star : alpha) (target : Nat) : Type u where
  betaCode : alpha
  betaStep : alpha
  tail : Nat → alpha
  starTerm : PA.Term
  star_eq : PA.Term.eval M tail starTerm = star
  row : ∀ code, code ≤ target →
    ∃ value,
      RawBetaEntry M value betaCode betaStep
        (PA.Term.numeralValue M code) ∧
      StandardProgramStep M rank betaCode betaStep code value tail starTerm

/-- Strong-induction theorem under the exact canonical-shape dichotomy used
by the default branch.  `TotalRowCases` supplies this dichotomy
unconditionally; keeping the induction engine factored makes its logical
dependency explicit. -/
theorem StandardProgramTable.entry_eq_totalRow_of_dichotomy
    {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (generator : alpha) (hPA : RawPASatisfies M)
    (hLtRank : formulaRank traceLtFormula ≤ rank)
    (hBetaRank : formulaRank traceBetaFormula ≤ rank)
    (target : Nat)
    (table : StandardProgramTable (preModel M S rank generator) rank
      (⟨generator, Hull.star⟩ : Carrier M S rank generator) target)
    (hDichotomy : ∀ code, code ≤ target →
      (∀ child, child < code →
        RawBetaEntry (preModel M S rank generator)
          (hullProgramValue M S rank generator (totalRowProgram rank child))
          table.betaCode table.betaStep
          (PA.Term.numeralValue (preModel M S rank generator) child)) →
      StandardRowWitness (preModel M S rank generator) rank code
          table.betaCode table.betaStep
          (⟨generator, Hull.star⟩ : Carrier M S rank generator)
          (hullProgramValue M S rank generator (totalRowProgram rank code)) ∨
        totalRowProgram rank code = .zero) :
    ∀ code, code ≤ target →
      ∀ {value : Carrier M S rank generator},
        RawBetaEntry (preModel M S rank generator) value
          table.betaCode table.betaStep
          (PA.Term.numeralValue (preModel M S rank generator) code) →
        value = hullProgramValue M S rank generator
          (totalRowProgram rank code) := by
  let KM := preModel M S rank generator
  intro code
  let P : Nat → Prop := fun code => code ≤ target →
    ∀ {value : Carrier M S rank generator},
      RawBetaEntry KM value table.betaCode table.betaStep
        (PA.Term.numeralValue KM code) →
      value = hullProgramValue M S rank generator
        (totalRowProgram rank code)
  change P code
  refine Nat.strongRecOn code (motive := P) ?_
  intro code ih
  change code ≤ target →
    ∀ {value : Carrier M S rank generator},
      RawBetaEntry KM value table.betaCode table.betaStep
        (PA.Term.numeralValue KM code) →
      value = hullProgramValue M S rank generator
        (totalRowProgram rank code)
  intro hcode value hvalueEntry
  · first
    | rcases table.row code hcode with ⟨rowValue, hrowEntry, hrowStep⟩
      have hvalueRow : value = rowValue := by
        exact hull_rawBetaEntry_functional M S rank generator hPA
          (by simpa [traceBetaFormula] using hBetaRank)
          hvalueEntry hrowEntry
      rw [hvalueRow]
      have hcanonicalEntries : ∀ child, child < code →
          RawBetaEntry KM
            (hullProgramValue M S rank generator
              (totalRowProgram rank child))
            table.betaCode table.betaStep
            (PA.Term.numeralValue KM child) := by
        intro child hchild
        rcases table.row child (Nat.le_trans (Nat.le_of_lt hchild) hcode) with
          ⟨childValue, hchildEntry, hchildStep⟩
        have hchildCanonical := ih child hchild
          (Nat.le_trans (Nat.le_of_lt hchild) hcode) hchildEntry
        rw [hchildCanonical] at hchildEntry
        exact hchildEntry
      change PA.Formula.Sat KM
        (evaluatorRowEnv rowValue (PA.Term.numeralValue KM code)
          table.betaStep table.betaCode
          table.tail)
        (programStep rank
          (PA.Term.var 1) (PA.Term.var 0)
          (PA.Term.var 3) (PA.Term.var 2)
          (liftTerm 4 table.starTerm)) at hrowStep
      rw [sat_programStep_iff] at hrowStep
      rcases hrowStep with hcases | hdefault
      · have hrowWitness := standardRowWitness_of_sat_programCases
          M S rank generator hPA code
          (PA.Term.var 1) (PA.Term.var 0)
          (PA.Term.var 3) (PA.Term.var 2)
          (liftTerm 4 table.starTerm)
          (evaluatorRowEnv rowValue (PA.Term.numeralValue KM code)
            table.betaStep table.betaCode
            table.tail)
          (by
            change PA.Term.numeralValue KM code =
              PA.Term.numeralValue KM code
            rfl) hcases
        have hrowWitness' : StandardRowWitness KM rank code
            table.betaCode table.betaStep
            (⟨generator, Hull.star⟩ : Carrier M S rank generator)
            rowValue := by
          simpa [evaluatorRowEnv, table.star_eq, PA.Term.eval, scons,
            liftTerm, PA.Term.eval_rename] using hrowWitness
        exact standardRowWitness_output_eq_totalRow_of_child_entries
          M S rank generator hPA
          (by simpa [traceLtFormula] using hLtRank) code hrowWitness'
          hcanonicalEntries (by
            intro child hchild x y hx hy
            exact hull_rawBetaEntry_functional M S rank generator hPA
              (by simpa [traceBetaFormula] using hBetaRank) hx hy)
      · rcases hDichotomy code hcode hcanonicalEntries with
          hcanonicalRow | hzero
        · have hno := (sat_noProgramCase_iff KM rank
              (PA.Term.var 1) (PA.Term.var 3) (PA.Term.var 2)
              (liftTerm 4 table.starTerm)
              (evaluatorRowEnv rowValue (PA.Term.numeralValue KM code)
                table.betaStep table.betaCode
                table.tail)).mp
              hdefault.1
          apply False.elim
          apply hno
          let canonicalValue := hullProgramValue M S rank generator
            (totalRowProgram rank code)
          let rowEnv := evaluatorRowEnv rowValue
            (PA.Term.numeralValue KM code) table.betaStep table.betaCode table.tail
          let proposedEnv := scons canonicalValue rowEnv
          refine ⟨canonicalValue, ?_⟩
          apply sat_programCases_of_standardRowWitness M S rank generator hPA
            hLtRank code
            (liftTerm 1 (PA.Term.var 1)) (PA.Term.var 0)
            (liftTerm 1 (PA.Term.var 3)) (liftTerm 1 (PA.Term.var 2))
            (liftTerm 1 (liftTerm 4 table.starTerm)) proposedEnv
          · change PA.Term.numeralValue KM code =
              PA.Term.numeralValue KM code
            rfl
          · simpa [proposedEnv, rowEnv, evaluatorRowEnv, canonicalValue,
              table.star_eq, liftTerm, PA.Term.eval_rename, PA.Term.eval,
              scons] using
              hcanonicalRow
        · have hrowZero : rowValue = KM.zero := by
            simpa [evaluatorRowEnv, PA.Term.eval, scons] using hdefault.2
          rw [hrowZero, hzero]
          exact (hullProgramValue_zero M S rank generator).symm

/-- Every entry of an arbitrary valid standard table is the canonical total
row value. -/
theorem StandardProgramTable.entry_eq_totalRow {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (generator : alpha) (hPA : RawPASatisfies M)
    (hLtRank : formulaRank traceLtFormula ≤ rank)
    (hBetaRank : formulaRank traceBetaFormula ≤ rank)
    (target : Nat)
    (table : StandardProgramTable (preModel M S rank generator) rank
      (⟨generator, Hull.star⟩ : Carrier M S rank generator) target) :
    ∀ code, code ≤ target →
      ∀ {value : Carrier M S rank generator},
        RawBetaEntry (preModel M S rank generator) value
          table.betaCode table.betaStep
          (PA.Term.numeralValue (preModel M S rank generator) code) →
        value = hullProgramValue M S rank generator
          (totalRowProgram rank code) := by
  apply table.entry_eq_totalRow_of_dichotomy M S rank generator hPA
    hLtRank hBetaRank target
  intro code hcode htable
  exact canonicalStandardRowWitness_or_zero M S rank generator
    table.betaCode table.betaStep code htable

/-- Consequently, entries from two independently witnessed beta tables agree
at every standard index in their common range. -/
theorem StandardProgramTable.entries_eq {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (generator : alpha) (hPA : RawPASatisfies M)
    (hLtRank : formulaRank traceLtFormula ≤ rank)
    (hBetaRank : formulaRank traceBetaFormula ≤ rank)
    (target : Nat)
    (left right : StandardProgramTable (preModel M S rank generator) rank
      (⟨generator, Hull.star⟩ : Carrier M S rank generator) target)
    (code : Nat) (hcode : code ≤ target)
    {x y : Carrier M S rank generator}
    (hx : RawBetaEntry (preModel M S rank generator) x
      left.betaCode left.betaStep
      (PA.Term.numeralValue (preModel M S rank generator) code))
    (hy : RawBetaEntry (preModel M S rank generator) y
      right.betaCode right.betaStep
      (PA.Term.numeralValue (preModel M S rank generator) code)) :
    x = y := by
  exact (left.entry_eq_totalRow M S rank generator hPA hLtRank hBetaRank
    target code hcode hx).trans
      (right.entry_eq_totalRow M S rank generator hPA hLtRank hBetaRank
        target code hcode hy).symm

/-- Standard hull numerals preserve the external non-strict order.  The
strict case uses bounded-rank transport; reflexivity uses the ambient PA
addition-by-zero axiom and restriction of the hull operations. -/
theorem hull_rawLe_numeralValue_of_le {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (generator : alpha) (hPA : RawPASatisfies M)
    (hLtRank : formulaRank traceLtFormula ≤ rank)
    {left right : Nat} (hle : left ≤ right) :
    RawLe (preModel M S rank generator)
      (PA.Term.numeralValue (preModel M S rank generator) left)
      (PA.Term.numeralValue (preModel M S rank generator) right) := by
  let KM := preModel M S rank generator
  rcases Nat.eq_or_lt_of_le hle with rfl | hlt
  · refine ⟨KM.zero, ?_⟩
    apply Subtype.ext
    have haddZero := sat_of_bprov_axs hPA
      (PA.Formula.BProv_Ax_s_addZero_term (PA.Term.var 0))
      (scons (PA.Term.numeralValue M left) (fun _ => M.zero))
    simpa [KM, PA.Formula.Sat, PA.Term.eval, PA.Term.eval_numeral,
      preModel_add_val, preModel_zero_val, scons] using haddZero
  · rcases hull_rawLt_of_ambient M S rank generator
        (by simpa [traceLtFormula] using hLtRank)
        (x := PA.Term.numeralValue KM left)
        (y := PA.Term.numeralValue KM right)
        (by
          simpa [KM] using
            (rawLt_numeralValue_of_lt hPA hlt)) with ⟨gap, hgap⟩
    exact ⟨KM.succ gap, hgap⟩

/-- The fixed trace evaluator is functional at every standard numeral code,
even when the two satisfying assignments choose unrelated beta codes and
steps. -/
theorem traceEvaluator_standardCode_functional {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (generator : alpha) (hPA : RawPASatisfies M)
    (hLtRank : formulaRank traceLtFormula ≤ rank)
    (hBetaRank : formulaRank traceBetaFormula ≤ rank)
    (target : Nat) {x y : Carrier M S rank generator}
    (hx : EvaluatorCutContract.Evaluates
      (preModel M S rank generator) (traceEvaluator rank)
      (⟨generator, Hull.star⟩ : Carrier M S rank generator)
      (PA.Term.numeralValue (preModel M S rank generator) target) x)
    (hy : EvaluatorCutContract.Evaluates
      (preModel M S rank generator) (traceEvaluator rank)
      (⟨generator, Hull.star⟩ : Carrier M S rank generator)
      (PA.Term.numeralValue (preModel M S rank generator) target) y) :
    x = y := by
  let KM := preModel M S rank generator
  let starK : Carrier M S rank generator := ⟨generator, Hull.star⟩
  let targetK := PA.Term.numeralValue KM target
  let ex := EvaluatorCutContract.evalEnv KM starK targetK x
  let ey := EvaluatorCutContract.evalEnv KM starK targetK y
  have hxSat : PA.Formula.Sat KM ex
      (evaluator rank (PA.Term.var 1) (PA.Term.var 0)
        (PA.Term.var 2)) := by
    simpa [EvaluatorCutContract.Evaluates, traceEvaluator, ex, KM,
      starK, targetK] using hx
  have hySat : PA.Formula.Sat KM ey
      (evaluator rank (PA.Term.var 1) (PA.Term.var 0)
        (PA.Term.var 2)) := by
    simpa [EvaluatorCutContract.Evaluates, traceEvaluator, ey, KM,
      starK, targetK] using hy
  rcases (sat_evaluator_iff KM rank (PA.Term.var 1) (PA.Term.var 0)
      (PA.Term.var 2) ex).mp hxSat with
    ⟨leftCode, leftStep, hxTarget, hxRows⟩
  rcases (sat_evaluator_iff KM rank (PA.Term.var 1) (PA.Term.var 0)
      (PA.Term.var 2) ey).mp hySat with
    ⟨rightCode, rightStep, hyTarget, hyRows⟩
  have hxTarget' : RawBetaEntry KM x leftCode leftStep targetK := by
    simpa [ex, EvaluatorCutContract.evalEnv, PA.Term.eval, targetK] using
      hxTarget
  have hyTarget' : RawBetaEntry KM y rightCode rightStep targetK := by
    simpa [ey, EvaluatorCutContract.evalEnv, PA.Term.eval, targetK] using
      hyTarget
  let leftTable : StandardProgramTable KM rank starK target := {
    betaCode := leftCode
    betaStep := leftStep
    tail := ex
    starTerm := PA.Term.var 2
    star_eq := by
      simp [ex, EvaluatorCutContract.evalEnv, starK, PA.Term.eval]
    row := by
      intro code hcode
      have hle := hull_rawLe_numeralValue_of_le M S rank generator hPA
        hLtRank hcode
      rcases hxRows (PA.Term.numeralValue KM code) hle with
        ⟨rowValue, hentry, hstep⟩
      refine ⟨rowValue, hentry, ?_⟩
      exact hstep
  }
  let rightTable : StandardProgramTable KM rank starK target := {
    betaCode := rightCode
    betaStep := rightStep
    tail := ey
    starTerm := PA.Term.var 2
    star_eq := by
      simp [ey, EvaluatorCutContract.evalEnv, starK, PA.Term.eval]
    row := by
      intro code hcode
      have hle := hull_rawLe_numeralValue_of_le M S rank generator hPA
        hLtRank hcode
      rcases hyRows (PA.Term.numeralValue KM code) hle with
        ⟨rowValue, hentry, hstep⟩
      refine ⟨rowValue, hentry, ?_⟩
      exact hstep
  }
  exact StandardProgramTable.entries_eq M S rank generator hPA hLtRank
    hBetaRank target leftTable rightTable target (Nat.le_refl target)
    hxTarget' hyTarget'

end ProgramTrace
end FiniteSkolemCut

end PAFiniteBasisReduction
end LeanProofs
