import PAFiniteBasisReduction.TotalProgramRows
import PAFiniteBasisReduction.TraceSupportRank

/-!
# Closure-preserving total-row beta tables in the hull
-/

namespace LeanProofs
namespace PAFiniteBasisReduction

open SetTheory PA

universe u

namespace FiniteSkolemCut
namespace ProgramTrace

/-- A standard program evaluation, packaged as an element of its generated
Skolem hull. -/
noncomputable def hullProgramValue {alpha : Type u} (M : PA.PreModel alpha)
    (S : CanonicalSelectors M) (rank : Nat) (star : alpha)
    (p : Program rank) : Carrier M S rank star :=
  ⟨Program.eval M S star p, Program.eval_mem_hull M S star p⟩

@[simp] theorem hullProgramValue_val {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (star : alpha) (p : Program rank) :
    (hullProgramValue M S rank star p).val = Program.eval M S star p :=
  rfl

@[simp] theorem hullProgramValue_zero {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (star : alpha) :
    hullProgramValue M S rank star (.zero : Program rank) =
      (preModel M S rank star).zero := by
  rfl

@[simp] theorem hullProgramValue_star {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (star : alpha) :
    hullProgramValue M S rank star (.star : Program rank) =
      (⟨star, Hull.star⟩ : Carrier M S rank star) := by
  rfl

@[simp] theorem hullProgramValue_succ {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (star : alpha) (p : Program rank) :
    hullProgramValue M S rank star (.succ p) =
      (preModel M S rank star).succ
        (hullProgramValue M S rank star p) := by
  rfl

@[simp] theorem hullProgramValue_add {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (star : alpha) (p q : Program rank) :
    hullProgramValue M S rank star (.add p q) =
      (preModel M S rank star).add
        (hullProgramValue M S rank star p)
        (hullProgramValue M S rank star q) := by
  rfl

@[simp] theorem hullProgramValue_mul {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (star : alpha) (p q : Program rank) :
    hullProgramValue M S rank star (.mul p q) =
      (preModel M S rank star).mul
        (hullProgramValue M S rank star p)
        (hullProgramValue M S rank star q) := by
  rfl

/-- Hull-valued environment denoted by the children of a Skolem program. -/
noncomputable def hullProgramArgsEnv {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (star : alpha) (args : Fin rank → Program rank) :
    Nat → Carrier M S rank star :=
  boundedEnv (preModel M S rank star) rank
    (fun i => hullProgramValue M S rank star (args i))

@[simp] theorem hullProgramArgsEnv_val {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (star : alpha) (args : Fin rank → Program rank) (i : Nat) :
    (hullProgramArgsEnv M S rank star args i).val =
      Program.argsEnv M S star args i := by
  by_cases hi : i < rank
  · simp [hullProgramArgsEnv, Program.argsEnv, boundedEnv_of_lt,
      hi, hullProgramValue]
  · simp [hullProgramArgsEnv, Program.argsEnv, boundedEnv_of_not_lt,
      hi, hullProgramValue]

/-- Exact existential-selector graph for a program node, proved in the hull
by transporting only the body truth from the ambient canonical selector. -/
theorem hullProgramValue_exSkolem_graph {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (star : alpha) (body : PA.Formula)
    (hRank : formulaRank (PA.Formula.ex body) ≤ rank)
    (args : Fin rank → Program rank) :
    PA.Formula.Sat (preModel M S rank star)
      (scons
        (hullProgramValue M S rank star (.exSkolem body hRank args))
        (hullProgramArgsEnv M S rank star args))
      (leastDefaultGraph body) := by
  have hBodyRank : formulaRank body ≤ rank := by
    simp only [formulaRank] at hRank
    omega
  apply hull_leastDefaultGraph_of_ambient M S rank star body
    hBodyRank (hullProgramArgsEnv M S rank star args)
      (hullProgramValue M S rank star (.exSkolem body hRank args))
  simpa only [hullProgramValue_val, hullProgramArgsEnv_val] using
    Program.eval_exSkolem_graph M S star body hRank args

/-- Exact universal-counterexample selector graph for a program node in the
hull, again using body-only transport. -/
theorem hullProgramValue_allSkolem_graph {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (star : alpha) (body : PA.Formula)
    (hRank : formulaRank (PA.Formula.all body) ≤ rank)
    (args : Fin rank → Program rank) :
    PA.Formula.Sat (preModel M S rank star)
      (scons
        (hullProgramValue M S rank star (.allSkolem body hRank args))
        (hullProgramArgsEnv M S rank star args))
      (leastCounterexampleGraph body) := by
  have hNegBodyRank :
      formulaRank (PA.Formula.imp body PA.Formula.bot) ≤ rank := by
    have hpos : 1 ≤ formulaRank body := by
      cases body <;> simp [formulaRank]
    have hmax : Nat.max (formulaRank body) 1 = formulaRank body :=
      Nat.max_eq_left hpos
    simp only [formulaRank, hmax] at hRank ⊢
    exact hRank
  apply hull_leastCounterexampleGraph_of_ambient M S rank star body
    hNegBodyRank (hullProgramArgsEnv M S rank star args)
      (hullProgramValue M S rank star (.allSkolem body hRank args))
  simpa only [hullProgramValue_val, hullProgramArgsEnv_val] using
    Program.eval_allSkolem_graph M S star body hRank args

/-- The finite total-row beta table constructed by programs transports to an
exact beta table inside the hull.  PA is still assumed only for the ambient
model. -/
theorem finite_total_row_beta_hull {alpha : Type u}
    {M : PA.PreModel alpha} (hPA : RawPASatisfies M)
    (S : CanonicalSelectors M) (rank : Nat) (star : alpha)
    (hSupport : ProgramBetaCoding.supportRank ≤ rank)
    (hBetaRank : formulaRank traceBetaFormula ≤ rank)
    (target : Nat) :
    ∃ codeProgram stepProgram : Program rank,
      ∀ k, k ≤ target →
        RawBetaEntry (preModel M S rank star)
          (hullProgramValue M S rank star (totalRowProgram rank k))
          (hullProgramValue M S rank star codeProgram)
          (hullProgramValue M S rank star stepProgram)
          (PA.Term.numeralValue (preModel M S rank star) k) := by
  rcases finite_total_row_beta_programs hPA S star hSupport target with
    ⟨codeProgram, stepProgram, htable⟩
  refine ⟨codeProgram, stepProgram, ?_⟩
  intro k hk
  exact (hull_rawBetaEntry_iff_ambient M S rank star
    (by simpa [traceBetaFormula] using hBetaRank)).mpr
      (by simpa only [hullProgramValue_val,
          hull_numeralValue_val_transport] using htable k hk)

/-- On a genuine program code, the distinguished total-row value is exactly
the hull element denoted by that program. -/
@[simp] theorem hullProgramValue_totalRow_code {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (star : alpha) (p : Program rank) :
    hullProgramValue M S rank star
        (totalRowProgram rank (Program.code p)) =
      hullProgramValue M S rank star p := by
  rw [totalRowProgram_code]

end ProgramTrace
end FiniteSkolemCut
end PAFiniteBasisReduction
end LeanProofs
