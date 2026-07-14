import PAFiniteBasisReduction.CanonicalSelectors

/-!
# External finite beta coding in raw PA models

Every externally finite list of elements of a raw model satisfying PA can be
packed into one Gödel-beta sequence.  This is the semantic bridge needed by
the finite-program trace evaluator: the list length is standard, while its
entries may be arbitrary (and in particular nonstandard) model elements.

The construction uses the beta-prepend theorem already proved syntactically
in `PAHF.PASyntax`; soundness transports that theorem to an arbitrary raw PA
model.  No division operation or meta-level induction principle is added to
the model.
-/

namespace LeanProofs
namespace PAFiniteBasisReduction

open SetTheory PA

universe u

namespace FiniteSkolemCut

/-- Raw semantic beta entry.  The two witnesses are respectively the beta
modulus and the quotient in the bounded remainder equation. -/
def RawBetaEntry {alpha : Type u} (M : PA.PreModel alpha)
    (out code step idx : alpha) : Prop :=
  ∃ modulus,
    modulus = M.succ (M.mul (M.succ idx) step) ∧
    ∃ quotient,
      RawLt M out modulus ∧
      code = M.add (M.mul quotient modulus) out

@[simp] theorem sat_betaTermTermAt_iff_raw {alpha : Type u}
    (M : PA.PreModel alpha) (out code step idx : PA.Term)
    (e : Nat → alpha) :
    PA.Formula.Sat M e
        (PA.Formula.betaTermTermAt out code step idx) ↔
      RawBetaEntry M
        (PA.Term.eval M e out) (PA.Term.eval M e code)
        (PA.Term.eval M e step) (PA.Term.eval M e idx) := by
  simp [RawBetaEntry, RawLt, PA.Formula.betaTermTermAt,
    PA.Formula.betaModTermTerm, PA.Formula.remTermTermAt,
    PA.Formula.ltTermAt, PA.Formula.Sat,
    PA.Term.eval, PA.Term.eval_rename, scons]

theorem sat_betaTermTermAt_vars_iff {alpha : Type u}
    (M : PA.PreModel alpha) (out code step idx : alpha)
    (e : Nat → alpha) :
    PA.Formula.Sat M
      (scons out (scons code (scons step (scons idx e))))
      (PA.Formula.betaTermTermAt
        (PA.Term.var 0) (PA.Term.var 1)
        (PA.Term.var 2) (PA.Term.var 3)) ↔
      RawBetaEntry M out code step idx := by
  simp [PA.Term.eval, scons]

@[simp] theorem sat_betaEntryExistsPrefixTermAt_iff_raw
    {alpha : Type u} (M : PA.PreModel alpha)
    (code step bound : PA.Term) (e : Nat → alpha) :
    PA.Formula.Sat M e
        (PA.Formula.betaEntryExistsPrefixTermAt code step bound) ↔
      ∀ idx, RawLt M idx (PA.Term.eval M e bound) →
        ∃ out, RawBetaEntry M out
          (PA.Term.eval M e code) (PA.Term.eval M e step) idx := by
  simp [PA.Formula.betaEntryExistsPrefixTermAt,
    PA.Formula.betaEntryExistsTermAt, RawLt,
    PA.Formula.ltTermAt, PA.Formula.Sat,
    PA.Term.eval, PA.Term.eval_rename, scons]

/-- Semantic shape of the source-prefix availability formula. -/
theorem sat_betaEntryExistsPrefix_vars_iff {alpha : Type u}
    (M : PA.PreModel alpha) (code step bound : alpha)
    (e : Nat → alpha) :
    PA.Formula.Sat M (scons code (scons step (scons bound e)))
      (PA.Formula.betaEntryExistsPrefixTermAt
        (PA.Term.var 0) (PA.Term.var 1) (PA.Term.var 2)) ↔
      ∀ idx, RawLt M idx bound →
        ∃ out, RawBetaEntry M out code step idx := by
  simp [PA.Formula.betaEntryExistsPrefixTermAt,
    PA.Formula.betaEntryExistsTermAt, RawLt,
    PA.Formula.ltTermAt, PA.Formula.Sat,
    PA.Term.eval, PA.Term.eval_rename, scons]

/-- Semantic shape of beta prepend: a fresh code and step put `head` at zero
and shift every available source entry below `bound` by one. -/
theorem sat_betaPrependExists_vars_iff {alpha : Type u}
    (M : PA.PreModel alpha)
    (sourceCode sourceStep head bound : alpha) (e : Nat → alpha) :
    PA.Formula.Sat M
      (scons sourceCode (scons sourceStep (scons head (scons bound e))))
      (PA.Formula.betaPrependExistsTermAt
        (PA.Term.var 0) (PA.Term.var 1)
        (PA.Term.var 2) (PA.Term.var 3)) ↔
      ∃ targetStep targetCode,
        RawBetaEntry M head targetCode targetStep M.zero ∧
        ∀ idx, RawLt M idx bound → ∀ out,
          RawBetaEntry M out sourceCode sourceStep idx →
          RawBetaEntry M out targetCode targetStep (M.succ idx) := by
  simp [PA.Formula.betaPrependExistsTermAt,
    PA.Formula.betaPrependPrefixCodeExistsTermAt,
    PA.Formula.betaPrependPrefixTermAt,
    PA.Formula.betaUnshiftPrefixTermAt, RawLt,
    PA.Formula.ltTermAt, PA.Formula.Sat,
    PA.Term.eval, PA.Term.eval_rename, scons]

@[simp] theorem sat_betaPrependExistsTermAt_iff_raw
    {alpha : Type u} (M : PA.PreModel alpha)
    (sourceCode sourceStep head bound : PA.Term) (e : Nat → alpha) :
    PA.Formula.Sat M e
        (PA.Formula.betaPrependExistsTermAt
          sourceCode sourceStep head bound) ↔
      ∃ targetStep targetCode,
        RawBetaEntry M (PA.Term.eval M e head)
          targetCode targetStep M.zero ∧
        ∀ idx, RawLt M idx (PA.Term.eval M e bound) → ∀ out,
          RawBetaEntry M out
            (PA.Term.eval M e sourceCode) (PA.Term.eval M e sourceStep) idx →
          RawBetaEntry M out targetCode targetStep (M.succ idx) := by
  simp [PA.Formula.betaPrependExistsTermAt,
    PA.Formula.betaPrependPrefixCodeExistsTermAt,
    PA.Formula.betaPrependPrefixTermAt,
    PA.Formula.betaUnshiftPrefixTermAt, RawLt,
    PA.Formula.ltTermAt, PA.Formula.Sat,
    PA.Term.eval, PA.Term.eval_rename, scons]

@[simp] theorem sat_betaPrependPrefixTermAt_iff_raw
    {alpha : Type u} (M : PA.PreModel alpha)
    (sourceCode sourceStep head targetCode targetStep bound : PA.Term)
    (e : Nat → alpha) :
    PA.Formula.Sat M e
        (PA.Formula.betaPrependPrefixTermAt
          sourceCode sourceStep head targetCode targetStep bound) ↔
      RawBetaEntry M (PA.Term.eval M e head)
          (PA.Term.eval M e targetCode) (PA.Term.eval M e targetStep)
          M.zero ∧
        ∀ idx, RawLt M idx (PA.Term.eval M e bound) → ∀ out,
          RawBetaEntry M out (PA.Term.eval M e sourceCode)
            (PA.Term.eval M e sourceStep) idx →
          RawBetaEntry M out (PA.Term.eval M e targetCode)
            (PA.Term.eval M e targetStep) (M.succ idx) := by
  simp [PA.Formula.betaPrependPrefixTermAt,
    PA.Formula.betaUnshiftPrefixTermAt, RawLt,
    PA.Formula.ltTermAt, PA.Formula.Sat,
    PA.Term.eval, PA.Term.eval_rename, scons]

theorem rawLt_numeralValue_cases {alpha : Type u}
    {M : PA.PreModel alpha} (hPA : RawPASatisfies M) {x : alpha} :
    ∀ n, RawLt M x (PA.Term.numeralValue M n) →
      ∃ k, k < n ∧ x = PA.Term.numeralValue M k
  | 0, hlt => False.elim (not_rawLt_zero hPA x (by
      simpa [PA.Term.numeralValue] using hlt))
  | n+1, hlt => by
      have hlt' : RawLt M x (M.succ (PA.Term.numeralValue M n)) := by
        simpa [PA.Term.numeralValue] using hlt
      rcases rawLt_succ_cases hPA hlt' with hprev | heq
      · rcases rawLt_numeralValue_cases hPA n hprev with ⟨k, hk, hx⟩
        exact ⟨k, by omega, hx⟩
      · exact ⟨n, Nat.lt_succ_self n, heq⟩

theorem rawLt_numeralValue_of_lt {alpha : Type u}
    {M : PA.PreModel alpha} (hPA : RawPASatisfies M)
    {m n : Nat} (hmn : m < n) :
    RawLt M (PA.Term.numeralValue M m) (PA.Term.numeralValue M n) := by
  let e : Nat → alpha := fun _ => M.zero
  have hproof : PA.Formula.BProv PA.Formula.Ax_s []
      (PA.Formula.ltTermAt (PA.Term.numeral m) (PA.Term.numeral n)) := by
    simpa [PA.Formula.ltTermAt, PA.Term.rename] using
      (PA.Formula.BProv_Ax_s_ltConst_closed (G := []) hmn)
  have hsat := sat_of_bprov_axs hPA hproof e
  simpa [RawLt, PA.Formula.ltTermAt, PA.Formula.Sat,
    PA.Term.eval, PA.Term.eval_rename, PA.Term.eval_numeral, scons] using hsat

/-- Every element non-strictly below a standard numeral is itself a standard
numeral at an index no larger than the bound. -/
theorem rawLe_numeralValue_cases {alpha : Type u}
    {M : PA.PreModel alpha} (hPA : RawPASatisfies M) {x : alpha} :
    ∀ n, RawLe M x (PA.Term.numeralValue M n) →
      ∃ k, k ≤ n ∧ x = PA.Term.numeralValue M k := by
  intro n hle
  rcases rawLe_or_gt hPA (PA.Term.numeralValue M n) x with
      hreverse | hstrict
  · refine ⟨n, Nat.le_refl n, ?_⟩
    exact rawLe_antisymm hPA hle hreverse
  · rcases rawLt_numeralValue_cases hPA n hstrict with ⟨k, hk, hx⟩
    exact ⟨k, Nat.le_of_lt hk, hx⟩

/-- One beta code realizes every entry of a finite external list at its
standard numeral index. -/
def RawBetaCodesList {alpha : Type u} (M : PA.PreModel alpha)
    (xs : List alpha) (code step : alpha) : Prop :=
  ∀ i : Fin xs.length,
    RawBetaEntry M (xs.get i) code step
      (PA.Term.numeralValue M i.val)

/-- One semantic beta-prepend step in any raw PA model.  This is the reusable
closure boundary: later explicit hull constructors choose these two witnesses
canonically, so the witnesses themselves remain inside the hull. -/
theorem rawBetaPrepend_exists_of_prefix {alpha : Type u}
    {M : PA.PreModel alpha} (hPA : RawPASatisfies M)
    (sourceCode sourceStep head bound : alpha)
    (hprefixRaw : ∀ idx, RawLt M idx bound →
      ∃ out, RawBetaEntry M out sourceCode sourceStep idx) :
    ∃ targetStep targetCode,
      RawBetaEntry M head targetCode targetStep M.zero ∧
      ∀ idx, RawLt M idx bound → ∀ out,
        RawBetaEntry M out sourceCode sourceStep idx →
        RawBetaEntry M out targetCode targetStep (M.succ idx) := by
  let prefixFormula : PA.Formula :=
    PA.Formula.betaEntryExistsPrefixTermAt
      (PA.Term.var 0) (PA.Term.var 1) (PA.Term.var 3)
  let G : List PA.Formula := [prefixFormula]
  have hass : PA.Formula.BProv PA.Formula.Ax_s G prefixFormula :=
    PA.Formula.BProv_ass (B := PA.Formula.Ax_s) (G := G) (by simp [G])
  have hprepend : PA.Formula.BProv PA.Formula.Ax_s G
      (PA.Formula.betaPrependExistsTermAt
        (PA.Term.var 0) (PA.Term.var 1)
        (PA.Term.var 2) (PA.Term.var 3)) :=
    PA.Formula.BProv_Ax_s_betaPrependExistsTermAt_of_entries
      (head := PA.Term.var 2) hass
  let e : Nat → alpha := fun _ => M.zero
  let v : Nat → alpha :=
    scons sourceCode (scons sourceStep (scons head (scons bound e)))
  have hprefixSat : PA.Formula.Sat M v prefixFormula := by
    apply (sat_betaEntryExistsPrefixTermAt_iff_raw M
      (PA.Term.var 0) (PA.Term.var 1) (PA.Term.var 3) v).mpr
    simpa [v, PA.Term.eval, scons] using hprefixRaw
  have hprependSat := sat_of_bprov_axs_context hPA hprepend v (by
    intro g hg
    have hg' : g = prefixFormula := by simpa [G] using hg
    simpa [hg'] using hprefixSat)
  have hraw := (sat_betaPrependExistsTermAt_iff_raw M
    (PA.Term.var 0) (PA.Term.var 1)
    (PA.Term.var 2) (PA.Term.var 3) v).mp hprependSat
  simpa [v, PA.Term.eval, scons] using hraw

/-! ## Canonical closure-preserving prepend helpers -/

/-- Fixed four-parameter prepend formula.  Its first existential witness is
the target step and its second is the target code. -/
def canonicalBetaPrependFormula : PA.Formula :=
  PA.Formula.betaPrependExistsTermAt
    (PA.Term.var 0) (PA.Term.var 1) (PA.Term.var 2) (PA.Term.var 3)

/-- Body opened after choosing the target step. -/
def canonicalBetaPrependStepBody : PA.Formula :=
  PA.Formula.betaPrependExistsTermAtBody
    (PA.Term.var 0) (PA.Term.var 1) (PA.Term.var 2) (PA.Term.var 3)

/-- Body opened after subsequently choosing the target code. -/
def canonicalBetaPrependCodeBody : PA.Formula :=
  PA.Formula.betaPrependPrefixCodeExistsTermAtBody
    (PA.Term.rename Nat.succ (PA.Term.var 0))
    (PA.Term.rename Nat.succ (PA.Term.var 1))
    (PA.Term.rename Nat.succ (PA.Term.var 2))
    (PA.Term.var 0)
    (PA.Term.rename Nat.succ (PA.Term.var 3))

theorem canonicalBetaPrependFormula_eq :
    canonicalBetaPrependFormula =
      PA.Formula.ex canonicalBetaPrependStepBody := by
  rfl

theorem canonicalBetaPrependStepBody_eq :
    canonicalBetaPrependStepBody =
      PA.Formula.ex canonicalBetaPrependCodeBody := by
  rfl

def canonicalBetaPrependEnv {alpha : Type u} (M : PA.PreModel alpha)
    (sourceCode sourceStep head bound : alpha) : Nat → alpha :=
  scons sourceCode (scons sourceStep (scons head
    (scons bound (fun _ => M.zero))))

noncomputable def canonicalBetaPrependStep {alpha : Type u}
    {M : PA.PreModel alpha} (S : CanonicalSelectors M)
    (sourceCode sourceStep head bound : alpha) : alpha :=
  canonicalValue S canonicalBetaPrependStepBody
    (canonicalBetaPrependEnv M sourceCode sourceStep head bound)

noncomputable def canonicalBetaPrependCode {alpha : Type u}
    {M : PA.PreModel alpha} (S : CanonicalSelectors M)
    (sourceCode sourceStep head bound : alpha) : alpha :=
  canonicalValue S canonicalBetaPrependCodeBody
    (scons (canonicalBetaPrependStep S sourceCode sourceStep head bound)
      (canonicalBetaPrependEnv M sourceCode sourceStep head bound))

/-- Exact joint specification of the two staged canonical helpers. -/
theorem canonicalBetaPrepend_spec {alpha : Type u} {M : PA.PreModel alpha}
    (hPA : RawPASatisfies M) (S : CanonicalSelectors M)
    (sourceCode sourceStep head bound : alpha)
    (hprefixRaw : ∀ idx, RawLt M idx bound →
      ∃ out, RawBetaEntry M out sourceCode sourceStep idx) :
    RawBetaEntry M head
        (canonicalBetaPrependCode S sourceCode sourceStep head bound)
        (canonicalBetaPrependStep S sourceCode sourceStep head bound)
        M.zero ∧
      ∀ idx, RawLt M idx bound → ∀ out,
        RawBetaEntry M out sourceCode sourceStep idx →
        RawBetaEntry M out
          (canonicalBetaPrependCode S sourceCode sourceStep head bound)
          (canonicalBetaPrependStep S sourceCode sourceStep head bound)
          (M.succ idx) := by
  let env := canonicalBetaPrependEnv M sourceCode sourceStep head bound
  rcases rawBetaPrepend_exists_of_prefix hPA
      sourceCode sourceStep head bound hprefixRaw with
    ⟨someStep, someCode, hhead, hshift⟩
  have hfullRaw : ∃ targetStep targetCode,
      RawBetaEntry M head targetCode targetStep M.zero ∧
      ∀ idx, RawLt M idx bound → ∀ out,
        RawBetaEntry M out sourceCode sourceStep idx →
        RawBetaEntry M out targetCode targetStep (M.succ idx) :=
    ⟨someStep, someCode, hhead, hshift⟩
  have hfull : PA.Formula.Sat M env canonicalBetaPrependFormula := by
    apply (sat_betaPrependExistsTermAt_iff_raw M
      (PA.Term.var 0) (PA.Term.var 1)
      (PA.Term.var 2) (PA.Term.var 3) env).mpr
    simpa [env, canonicalBetaPrependEnv, PA.Term.eval, scons] using hfullRaw
  have hstepExists : ∃ step,
      PA.Formula.Sat M (scons step env)
        canonicalBetaPrependStepBody := by
    rw [canonicalBetaPrependFormula_eq] at hfull
    exact hfull
  have hstep : PA.Formula.Sat M
      (scons (canonicalBetaPrependStep S sourceCode sourceStep head bound) env)
      canonicalBetaPrependStepBody := by
    exact canonicalValue_spec S canonicalBetaPrependStepBody env hstepExists
  have hcodeExists : ∃ code,
      PA.Formula.Sat M
        (scons code
          (scons (canonicalBetaPrependStep S sourceCode sourceStep head bound)
            env)) canonicalBetaPrependCodeBody := by
    rw [canonicalBetaPrependStepBody_eq] at hstep
    exact hstep
  have hcode : PA.Formula.Sat M
      (scons (canonicalBetaPrependCode S sourceCode sourceStep head bound)
        (scons (canonicalBetaPrependStep S sourceCode sourceStep head bound)
          env)) canonicalBetaPrependCodeBody := by
    exact canonicalValue_spec S canonicalBetaPrependCodeBody
      (scons (canonicalBetaPrependStep S sourceCode sourceStep head bound) env)
      hcodeExists
  simpa [canonicalBetaPrependCodeBody,
    PA.Formula.betaPrependPrefixCodeExistsTermAtBody,
    env, canonicalBetaPrependEnv,
    PA.Term.eval, PA.Term.eval_rename, scons] using hcode

theorem finite_list_beta_code {alpha : Type u} {M : PA.PreModel alpha}
    (hPA : RawPASatisfies M) (xs : List alpha) :
    ∃ code step, RawBetaCodesList M xs code step := by
  induction xs with
  | nil =>
      refine ⟨M.zero, M.zero, ?_⟩
      intro i
      exact Fin.elim0 i
  | cons head tail ih =>
      rcases ih with ⟨sourceCode, sourceStep, hsource⟩
      let bound := PA.Term.numeralValue M tail.length
      have hprefixRaw : ∀ idx, RawLt M idx bound →
          ∃ out, RawBetaEntry M out sourceCode sourceStep idx := by
        intro idx hlt
        rcases rawLt_numeralValue_cases hPA tail.length hlt with
          ⟨k, hk, rfl⟩
        let i : Fin tail.length := ⟨k, hk⟩
        exact ⟨tail.get i, hsource i⟩
      rcases rawBetaPrepend_exists_of_prefix hPA
          sourceCode sourceStep head bound hprefixRaw with
        ⟨targetStep, targetCode, hhead, hshift⟩
      refine ⟨targetCode, targetStep, ?_⟩
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [RawBetaCodesList, PA.Term.numeralValue] using hhead
      · have hjlt : RawLt M (PA.Term.numeralValue M j.val) bound := by
          exact rawLt_numeralValue_of_lt hPA j.isLt
        have hentry := hshift (PA.Term.numeralValue M j.val) hjlt
          (tail.get j) (hsource j)
        simpa [RawBetaCodesList, PA.Term.numeralValue] using hentry

theorem finite_vector_beta_code {alpha : Type u} {M : PA.PreModel alpha}
    (hPA : RawPASatisfies M) {n : Nat} (v : Fin n → alpha) :
    ∃ code step, ∀ i : Fin n,
      RawBetaEntry M (v i) code step
        (PA.Term.numeralValue M i.val) := by
  rcases finite_list_beta_code hPA (List.ofFn v) with
    ⟨code, step, hcode⟩
  refine ⟨code, step, ?_⟩
  intro i
  let j : Fin (List.ofFn v).length :=
    Fin.cast (List.length_ofFn (f := v)).symm i
  have hj := hcode j
  simpa [RawBetaCodesList, j, List.get_eq_getElem,
    List.getElem_ofFn] using hj

/-- A fixed beta code and step have at most one output at each index. -/
theorem rawBetaEntry_functional {alpha : Type u} {M : PA.PreModel alpha}
    (hPA : RawPASatisfies M) {x y code step idx : alpha}
    (hx : RawBetaEntry M x code step idx)
    (hy : RawBetaEntry M y code step idx) : x = y := by
  let f1 := PA.Formula.betaTermTermAt
    (PA.Term.var 0) (PA.Term.var 2) (PA.Term.var 3) (PA.Term.var 4)
  let f2 := PA.Formula.betaTermTermAt
    (PA.Term.var 1) (PA.Term.var 2) (PA.Term.var 3) (PA.Term.var 4)
  let G : List PA.Formula := [f1, f2]
  have hass1 : PA.Formula.BProv PA.Formula.Ax_s G f1 :=
    PA.Formula.BProv_ass (B := PA.Formula.Ax_s) (G := G) (by simp [G])
  have hass2 : PA.Formula.BProv PA.Formula.Ax_s G f2 :=
    PA.Formula.BProv_ass (B := PA.Formula.Ax_s) (G := G) (by simp [G])
  have heq : PA.Formula.BProv PA.Formula.Ax_s G
      (PA.Formula.eq (PA.Term.var 1) (PA.Term.var 0)) :=
    PA.Formula.BProv_Ax_s_eq_of_betaTermTermAt_betaTermTermAt_same_index
      hass1 hass2
  let e : Nat → alpha := fun _ => M.zero
  let v : Nat → alpha :=
    scons x (scons y (scons code (scons step (scons idx e))))
  have hsat1 : PA.Formula.Sat M v f1 := by
    simpa [f1, v, PA.Term.eval, scons] using hx
  have hsat2 : PA.Formula.Sat M v f2 := by
    simpa [f2, v, PA.Term.eval, scons] using hy
  have hout := sat_of_bprov_axs_context hPA heq v (by
    intro g hg
    simp [G] at hg
    rcases hg with rfl | rfl
    · exact hsat1
    · exact hsat2)
  simpa [v, PA.Formula.Sat, PA.Term.eval, scons] using hout.symm

theorem not_rawLt_self {alpha : Type u} {M : PA.PreModel alpha}
    (hPA : RawPASatisfies M) (x : alpha) : ¬RawLt M x x := by
  intro hlt
  let f := PA.Formula.ltTermAt (PA.Term.var 0) (PA.Term.var 0)
  let G : List PA.Formula := [f]
  have hass : PA.Formula.BProv PA.Formula.Ax_s G f :=
    PA.Formula.BProv_ass (B := PA.Formula.Ax_s) (G := G) (by simp [G])
  have hrefl : PA.Formula.BProv PA.Formula.Ax_s G
      (PA.Formula.leTermAt (PA.Term.var 0) (PA.Term.var 0)) :=
    PA.Formula.BProv_Ax_s_leTermAt_refl (PA.Term.var 0)
  have hbot : PA.Formula.BProv PA.Formula.Ax_s G PA.Formula.bot :=
    PA.Formula.BProv_Ax_s_ltTermAt_leTermAt_bot hass hrefl
  let e : Nat → alpha := fun _ => M.zero
  have hsat : PA.Formula.Sat M (scons x e) f := by
    simpa [f, RawLt, PA.Formula.ltTermAt, PA.Formula.Sat,
      PA.Term.eval, PA.Term.eval_rename, scons] using hlt
  exact sat_of_bprov_axs_context hPA hbot (scons x e) (by
    intro g hg
    have : g = f := by simpa [G] using hg
    simpa [this] using hsat)

theorem numeralValue_injective_of_pa {alpha : Type u}
    {M : PA.PreModel alpha} (hPA : RawPASatisfies M) :
    Function.Injective (PA.Term.numeralValue M) := by
  intro m n hmnValue
  apply Classical.byContradiction
  intro hmn
  rcases Nat.lt_or_gt_of_ne hmn with hlt | hgt
  · have hraw := rawLt_numeralValue_of_lt hPA hlt
    rw [hmnValue] at hraw
    exact not_rawLt_self hPA _ hraw
  · have hraw := rawLt_numeralValue_of_lt hPA hgt
    rw [hmnValue] at hraw
    exact not_rawLt_self hPA _ hraw

/-- Every element of a PA model is either one of the external standard
numerals or lies above all of them. -/
theorem raw_standard_or_above {alpha : Type u} {M : PA.PreModel alpha}
    (hPA : RawPASatisfies M) (x : alpha) :
    (∃ n, x = PA.Term.numeralValue M n) ∨
      (∀ n, RawLt M (PA.Term.numeralValue M n) x) := by
  classical
  by_cases hstandard : ∃ n, x = PA.Term.numeralValue M n
  · exact Or.inl hstandard
  · right
    intro n
    rcases rawLe_or_gt hPA x (PA.Term.numeralValue M n) with
        hxle | hnlt
    · rcases rawLe_or_gt hPA (PA.Term.numeralValue M n) x with
          hnle | hxlt
      · exact False.elim
          (hstandard ⟨n, rawLe_antisymm hPA hxle hnle⟩)
      · rcases rawLt_numeralValue_cases hPA n hxlt with
          ⟨k, _, hx⟩
        exact False.elim (hstandard ⟨k, hx⟩)
    · exact hnlt

theorem raw_above_of_nonstandard {alpha : Type u} {M : PA.PreModel alpha}
    (hPA : RawPASatisfies M) {x : alpha}
    (hnonstandard : ¬∃ n, x = PA.Term.numeralValue M n) :
    ∀ n, RawLt M (PA.Term.numeralValue M n) x := by
  rcases raw_standard_or_above hPA x with hstandard | habove
  · exact False.elim (hnonstandard hstandard)
  · exact habove

/-- The compactness witness from `NonstandardHFFin` is above every standard
numeral in the extracted raw PA algebra. -/
theorem fofam_star_above_all_numerals {alpha : Type u}
    (M : AckermannHF.FirstOrderFiniteAdjunctionModel alpha)
    (star : AckermannHF.PAInHF.FOFAMOrdinal M)
    (hbound : ∀ n,
      AckermannHF.PAInHF.fofamPAFormulaSat M (fun _ => star)
        (NonstandardHFFin.paLtNumeralAt n)) :
    ∀ n, RawLt (AckermannHF.PAInHF.fofamPAPreModel M)
      (PA.Term.numeralValue
        (AckermannHF.PAInHF.fofamPAPreModel M) n) star := by
  intro n
  have h := hbound n
  simpa [AckermannHF.PAInHF.fofamPAFormulaSat,
    NonstandardHFFin.paLtNumeralAt, RawLt,
    PA.Formula.ltTermAt, PA.Formula.Sat,
    PA.Term.eval, PA.Term.eval_rename, PA.Term.eval_numeral, scons] using h

end FiniteSkolemCut
end PAFiniteBasisReduction
end LeanProofs
