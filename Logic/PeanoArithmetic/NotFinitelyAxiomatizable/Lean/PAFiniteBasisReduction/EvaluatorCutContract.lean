import PAFiniteBasisReduction.RankZero
import PAFiniteBasisReduction.FiniteBetaCoding
import Init.Data.List.OfFn
import Init.Data.List.Erase

/-!
# The evaluator-independent proper-cut argument

This module isolates the second half of the finite-Skolem-hull construction.
It assumes a single arithmetic formula which, at each standard numeral code,
is a partial function whose standard codes collectively name every element of
the carrier.  Elementary facts about standard numerals and a distinguished
nonstandard seed then suffice to define the external standard cut internally,
and hence to falsify one genuine sealed induction axiom.

No claim about how the evaluator formula is constructed occurs here.  In
particular, the contract below is the precise interface which the later
finite-program trace construction must implement.
-/

namespace LeanProofs
namespace PAFiniteBasisReduction

open SetTheory PA

universe u
universe v

namespace EvaluatorCutContract

/-- Core Lean's small-list pigeonhole lemma, stated in the form needed below.
The reduction project deliberately has no Mathlib dependency of its own. -/
private theorem nodup_ofFn_of_injective {beta : Type v} {n : Nat}
    (f : Fin n → beta) (hf : Function.Injective f) :
    (List.ofFn f).Nodup := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.nodup_cons]
      constructor
      · intro hmem
        rw [List.mem_ofFn] at hmem
        obtain ⟨i, hi⟩ := hmem
        have hzeroSucc : (0 : Fin (n + 1)) = i.succ := hf hi.symm
        exact Nat.noConfusion (congrArg Fin.val hzeroSucc)
      · exact ih (fun i => f i.succ) (fun _ _ hij => by
          apply Fin.ext
          simpa using congrArg Fin.val (hf hij))

private theorem length_le_of_nodup_lt {xs : List Nat} {bound : Nat}
    (hnodup : xs.Nodup)
    (hlt : ∀ x, x ∈ xs → x < bound) :
    xs.length ≤ bound := by
  induction bound generalizing xs with
  | zero =>
      cases xs with
      | nil => simp
      | cons x xs =>
          have := hlt x (by simp)
          omega
  | succ bound ih =>
      by_cases hmem : bound ∈ xs
      · have heraseNodup : (xs.erase bound).Nodup := hnodup.erase bound
        have heraseLt : ∀ x, x ∈ xs.erase bound → x < bound := by
          intro x hx
          have hxparts := hnodup.mem_erase_iff.mp hx
          have hxlt := hlt x hxparts.2
          omega
        have hlength := ih heraseNodup heraseLt
        rw [List.length_erase_of_mem hmem] at hlength
        have hpositive : 0 < xs.length := List.length_pos_of_mem hmem
        omega
      · have hlt' : ∀ x, x ∈ xs → x < bound := by
          intro x hx
          have hxlt := hlt x hx
          have hxne : x ≠ bound := by
            intro heq
            exact hmem (heq ▸ hx)
          omega
        exact Nat.le.step (ih hnodup hlt')

private theorem no_injective_fin_succ (bound : Nat)
    (f : Fin (bound + 1) → Fin bound) :
    ¬Function.Injective f := by
  intro hinj
  let values : List Nat := List.ofFn (fun i => (f i).val)
  have hvaluesNodup : values.Nodup :=
    nodup_ofFn_of_injective (fun i => (f i).val)
      (fun i j hij => hinj (Fin.ext hij))
  have hvaluesLt : ∀ x, x ∈ values → x < bound := by
    intro x hx
    rw [List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    exact (f i).isLt
  have hlength := length_le_of_nodup_lt hvaluesNodup hvaluesLt
  simp [values] at hlength
  omega

/-- The environment convention for the object-language evaluator is
`0 = output`, `1 = standard program code`, and `2 = distinguished seed`.
All unused variables are set to arithmetic zero. -/
def evalEnv {alpha : Type u} (M : PA.PreModel alpha)
    (seed code output : alpha) : Nat → alpha
  | 0 => output
  | 1 => code
  | 2 => seed
  | _ => M.zero

/-- Semantic evaluation relation induced by an arbitrary fixed PA formula. -/
def Evaluates {alpha : Type u} (M : PA.PreModel alpha)
    (evalFormula : PA.Formula) (seed code output : alpha) : Prop :=
  PA.Formula.Sat M (evalEnv M seed code output) evalFormula

/-- The strict order relation expressed by PA's term-parametric `<` macro. -/
def StrictLt {alpha : Type u} (M : PA.PreModel alpha)
    (a b : alpha) : Prop :=
  ∃ gap, M.add a (M.succ gap) = b

/-- An element is externally standard when it is the value of a standard
PA numeral. -/
def IsStandard {alpha : Type u} (M : PA.PreModel alpha) (x : alpha) : Prop :=
  ∃ n, x = PA.Term.numeralValue M n

/-- An element is above every externally standard numeral. -/
def AboveAllNumerals {alpha : Type u} (M : PA.PreModel alpha)
    (x : alpha) : Prop :=
  ∀ n, StrictLt M (PA.Term.numeralValue M n) x

/-- The exact semantic interface required from the finite-program evaluator
and its hull.  Functionality is required only at standard numeral codes.
`lt_numeral` is the bounded-standardness fact for the discrete PA order;
`standard_or_above` is the corresponding standard/nonstandard dichotomy. -/
structure Contract {alpha : Type u} (M : PA.PreModel alpha)
    (evalFormula : PA.Formula) (seed : alpha) : Prop where
  standardCode_total :
    ∀ output, ∃ code : Nat,
      Evaluates M evalFormula seed (PA.Term.numeralValue M code) output
  standardCode_functional :
    ∀ (code : Nat) {x y},
      Evaluates M evalFormula seed (PA.Term.numeralValue M code) x →
      Evaluates M evalFormula seed (PA.Term.numeralValue M code) y →
      x = y
  numeral_injective : Function.Injective (PA.Term.numeralValue M)
  lt_numeral :
    ∀ {x : alpha} {bound : Nat},
      StrictLt M x (PA.Term.numeralValue M bound) →
      ∃ n : Nat, n < bound ∧ x = PA.Term.numeralValue M n
  standard_or_above : ∀ x, IsStandard M x ∨ AboveAllNumerals M x
  seed_above : AboveAllNumerals M seed

/-! ## Transporting ambient PA arithmetic to a bounded-rank hull -/

/-- The only auxiliary formula whose elementarity is needed by the
evaluator-independent cut argument. -/
def hullLtFormula : PA.Formula :=
  PA.Formula.ltTermAt (PA.Term.var 0) (PA.Term.var 1)

/-- A closure rank large enough both for the requested PA fragment and for
transporting strict-order witnesses from the ambient PA model. -/
def cutConstructionRank (n : Nat) : Nat :=
  Nat.max (FiniteSkolemCut.fragmentSemanticRank n) (formulaRank hullLtFormula)

theorem fragmentSemanticRank_le_cutConstructionRank (n : Nat) :
    FiniteSkolemCut.fragmentSemanticRank n ≤ cutConstructionRank n :=
  Nat.le_max_left _ _

theorem hullLtFormula_rank_le_cutConstructionRank (n : Nat) :
    formulaRank hullLtFormula ≤ cutConstructionRank n :=
  Nat.le_max_right _ _

theorem sat_hullLtFormula_iff {alpha : Type u} (M : PA.PreModel alpha)
    (e : Nat → alpha) :
    PA.Formula.Sat M e hullLtFormula ↔ StrictLt M (e 0) (e 1) := by
  simp [hullLtFormula, StrictLt, PA.Formula.ltTermAt, PA.Formula.Sat,
    PA.Term.eval, PA.Term.rename, SetTheory.scons]

/-- The subtype inclusion sends every hull numeral to the corresponding
ambient numeral. -/
@[simp] theorem hull_numeralValue_val {alpha : Type u}
    (M : PA.PreModel alpha) (S : FiniteSkolemCut.CanonicalSelectors M)
    (rank : Nat) (star : alpha) :
    ∀ n,
      (PA.Term.numeralValue (FiniteSkolemCut.preModel M S rank star) n).val =
        PA.Term.numeralValue M n
  | 0 => rfl
  | n + 1 => by
      simp only [PA.Term.numeralValue,
        FiniteSkolemCut.preModel_succ_val,
        hull_numeralValue_val M S rank star n]

/-- Ambient strict inequalities whose endpoints lie in the hull lift back to
the hull whenever the fixed `<` formula is below the closure rank.  The new
gap witness is supplied by bounded-rank elementarity. -/
theorem hull_strictLt_of_ambient {alpha : Type u}
    (M : PA.PreModel alpha) (S : FiniteSkolemCut.CanonicalSelectors M)
    (rank : Nat) (star : alpha)
    (hLtRank : formulaRank hullLtFormula ≤ rank)
    {x y : FiniteSkolemCut.Carrier M S rank star}
    (hxy : FiniteSkolemCut.RawLt M x.val y.val) :
    StrictLt (FiniteSkolemCut.preModel M S rank star) x y := by
  let KM := FiniteSkolemCut.preModel M S rank star
  let e : Nat → FiniteSkolemCut.Carrier M S rank star :=
    SetTheory.scons x (SetTheory.scons y (fun _ => KM.zero))
  apply (sat_hullLtFormula_iff KM e).mp
  apply (FiniteSkolemCut.sat_iff_ambient M S rank star hullLtFormula
    hLtRank e).mpr
  apply (sat_hullLtFormula_iff M (fun i => (e i).val)).mpr
  simpa [e, SetTheory.scons, StrictLt, FiniteSkolemCut.RawLt] using hxy

/-- The six base axioms and induction in the ambient model give the bounded
standardness facts used by `Contract`; no PA validity is assumed for the
hull itself. -/
theorem hull_contract_of_ambient_pa {alpha : Type u}
    (M : PA.PreModel alpha) (S : FiniteSkolemCut.CanonicalSelectors M)
    (rank : Nat) (star : alpha)
    (hPA : FiniteSkolemCut.RawPASatisfies M)
    (hLtRank : formulaRank hullLtFormula ≤ rank)
    (hstar : ∀ n,
      FiniteSkolemCut.RawLt M (PA.Term.numeralValue M n) star)
    (evalFormula : PA.Formula)
    (hTotal : ∀ output : FiniteSkolemCut.Carrier M S rank star,
      ∃ code : Nat,
        Evaluates (FiniteSkolemCut.preModel M S rank star) evalFormula
          (⟨star, FiniteSkolemCut.Hull.star⟩ :
            FiniteSkolemCut.Carrier M S rank star)
          (PA.Term.numeralValue
            (FiniteSkolemCut.preModel M S rank star) code)
          output)
    (hFunctional : ∀ (code : Nat)
        {x y : FiniteSkolemCut.Carrier M S rank star},
      Evaluates (FiniteSkolemCut.preModel M S rank star) evalFormula
          (⟨star, FiniteSkolemCut.Hull.star⟩ :
            FiniteSkolemCut.Carrier M S rank star)
          (PA.Term.numeralValue
            (FiniteSkolemCut.preModel M S rank star) code) x →
      Evaluates (FiniteSkolemCut.preModel M S rank star) evalFormula
          (⟨star, FiniteSkolemCut.Hull.star⟩ :
            FiniteSkolemCut.Carrier M S rank star)
          (PA.Term.numeralValue
            (FiniteSkolemCut.preModel M S rank star) code) y →
      x = y) :
    Contract (FiniteSkolemCut.preModel M S rank star) evalFormula
      (⟨star, FiniteSkolemCut.Hull.star⟩ :
        FiniteSkolemCut.Carrier M S rank star) := by
  let KM := FiniteSkolemCut.preModel M S rank star
  let starK : FiniteSkolemCut.Carrier M S rank star :=
    ⟨star, FiniteSkolemCut.Hull.star⟩
  refine {
    standardCode_total := hTotal
    standardCode_functional := hFunctional
    numeral_injective := ?_
    lt_numeral := ?_
    standard_or_above := ?_
    seed_above := ?_ }
  · intro m n hmn
    apply FiniteSkolemCut.numeralValue_injective_of_pa hPA
    simpa [KM] using congrArg Subtype.val hmn
  · intro x bound hlt
    obtain ⟨gap, hgap⟩ := hlt
    have hambient : FiniteSkolemCut.RawLt M x.val
        (PA.Term.numeralValue M bound) := by
      refine ⟨gap.val, ?_⟩
      simpa [KM] using congrArg Subtype.val hgap
    obtain ⟨n, hn, hx⟩ :=
      FiniteSkolemCut.rawLt_numeralValue_cases hPA bound hambient
    refine ⟨n, hn, ?_⟩
    apply Subtype.ext
    simpa [KM] using hx
  · intro x
    rcases FiniteSkolemCut.raw_standard_or_above hPA x.val with
      hstandard | habove
    · left
      obtain ⟨n, hx⟩ := hstandard
      refine ⟨n, ?_⟩
      apply Subtype.ext
      simpa [KM] using hx
    · right
      intro n
      apply hull_strictLt_of_ambient M S rank star hLtRank
      simpa [KM] using habove n
  · intro n
    apply hull_strictLt_of_ambient M S rank star hLtRank
    simpa [KM, starK] using hstar n

/-- The rank-fragment transfer theorem at any enlarged construction rank. -/
theorem hull_sat_rankFragment_of_le {alpha : Type u}
    (M : PA.PreModel alpha) (S : FiniteSkolemCut.CanonicalSelectors M)
    (rank : Nat) (star : alpha) (n : Nat)
    (hrank : FiniteSkolemCut.fragmentSemanticRank n ≤ rank)
    (hPA : FiniteSkolemCut.RawPASatisfies M)
    (e : Nat → FiniteSkolemCut.Carrier M S rank star) :
    ∀ f, PARankFragment n f →
      PA.Formula.Sat (FiniteSkolemCut.preModel M S rank star) e f := by
  intro f hf
  apply (FiniteSkolemCut.sat_iff_ambient M S rank star f
    (Nat.le_trans (FiniteSkolemCut.fragment_axiom_rank_le hf) hrank) e).mpr
  exact hPA (fun i => (e i).val) f (paRankFragment_subset_ax_s hf)

/-- Under the two binders introduced by `coverAt`, instantiate the evaluator
variables by output `#1`, code `#0`, and seed `#3`. -/
def evalInCoverSubst : Nat → PA.Term
  | 0 => PA.Term.var 1
  | 1 => PA.Term.var 0
  | 2 => PA.Term.var 3
  | _ => PA.Term.zero

/-- `coverAt evalFormula` has free variables `0 = bound`, `1 = seed` and says
that every element has an evaluator code strictly below the bound. -/
def coverAt (evalFormula : PA.Formula) : PA.Formula :=
  PA.Formula.all (PA.Formula.ex (PA.Formula.and
    (PA.Formula.ltTermAt (PA.Term.var 0) (PA.Term.var 2))
    (PA.Formula.subst evalInCoverSubst evalFormula)))

/-- The internally definable cut is the set of bounds which do not cover the
whole hull by evaluator codes.  Its free variables are again `0 = bound` and
`1 = seed`. -/
def cutAt (evalFormula : PA.Formula) : PA.Formula :=
  PA.Formula.imp (coverAt evalFormula) PA.Formula.bot

/-- Semantic counterpart of `coverAt`. -/
def Covers {alpha : Type u} (M : PA.PreModel alpha)
    (evalFormula : PA.Formula) (seed bound : alpha) : Prop :=
  ∀ output, ∃ code,
    StrictLt M code bound ∧ Evaluates M evalFormula seed code output

theorem sat_coverAt_iff {alpha : Type u} (M : PA.PreModel alpha)
    (evalFormula : PA.Formula) (e : Nat → alpha) :
    PA.Formula.Sat M e (coverAt evalFormula) ↔
      Covers M evalFormula (e 1) (e 0) := by
  simp only [coverAt, PA.Formula.Sat, Covers]
  constructor
  · intro h output
    obtain ⟨code, hlt, heval⟩ := h output
    refine ⟨code, ?_, ?_⟩
    · simpa [StrictLt, PA.Formula.ltTermAt, PA.Formula.Sat,
        PA.Term.eval, PA.Term.rename, SetTheory.scons] using hlt
    · rw [PA.Formula.Sat_subst] at heval
      apply (PA.Formula.Sat_ext M evalFormula (e := _)
        (e' := evalEnv M (e 1) code output) ?_).mp heval
      intro n
      rcases n with _ | _ | _ | n <;>
        simp [evalInCoverSubst, evalEnv, PA.Term.eval, SetTheory.scons]
  · intro h output
    obtain ⟨code, hlt, heval⟩ := h output
    refine ⟨code, ?_, ?_⟩
    · simpa [StrictLt, PA.Formula.ltTermAt, PA.Formula.Sat,
        PA.Term.eval, PA.Term.rename, SetTheory.scons] using hlt
    · rw [PA.Formula.Sat_subst]
      apply (PA.Formula.Sat_ext M evalFormula (e := _)
        (e' := evalEnv M (e 1) code output) ?_).mpr heval
      intro n
      rcases n with _ | _ | _ | n <;>
        simp [evalInCoverSubst, evalEnv, PA.Term.eval, SetTheory.scons]

theorem sat_cutAt_iff {alpha : Type u} (M : PA.PreModel alpha)
    (evalFormula : PA.Formula) (e : Nat → alpha) :
    PA.Formula.Sat M e (cutAt evalFormula) ↔
      ¬Covers M evalFormula (e 1) (e 0) := by
  simp [cutAt, PA.Formula.Sat, sat_coverAt_iff]

/-- A bound above every standard numeral covers the whole carrier: choose a
standard evaluator code for each output. -/
theorem covers_of_aboveAllNumerals {alpha : Type u}
    {M : PA.PreModel alpha} {evalFormula : PA.Formula} {seed bound : alpha}
    (h : Contract M evalFormula seed) (hbound : AboveAllNumerals M bound) :
    Covers M evalFormula seed bound := by
  intro output
  obtain ⟨code, hcode⟩ := h.standardCode_total output
  exact ⟨PA.Term.numeralValue M code, hbound code, hcode⟩

/-- No standard numeral bound covers the carrier.  Otherwise the `bound`
standard codes below it would, by functionality, give an injection from
`Fin (bound + 1)` into `Fin bound`. -/
theorem not_covers_numeral {alpha : Type u}
    {M : PA.PreModel alpha} {evalFormula : PA.Formula} {seed : alpha}
    (h : Contract M evalFormula seed) (bound : Nat) :
    ¬Covers M evalFormula seed (PA.Term.numeralValue M bound) := by
  intro hcover
  classical
  have hcode (i : Fin (bound + 1)) :
      ∃ code : Fin bound,
        Evaluates M evalFormula seed
          (PA.Term.numeralValue M code.val)
          (PA.Term.numeralValue M i.val) := by
    obtain ⟨codeValue, hlt, heval⟩ :=
      hcover (PA.Term.numeralValue M i.val)
    obtain ⟨code, hcodeLt, rfl⟩ := h.lt_numeral hlt
    exact ⟨⟨code, hcodeLt⟩, heval⟩
  let codeOf : Fin (bound + 1) → Fin bound := fun i => (hcode i).choose
  have codeOf_spec (i : Fin (bound + 1)) :
      Evaluates M evalFormula seed
        (PA.Term.numeralValue M (codeOf i).val)
        (PA.Term.numeralValue M i.val) :=
    (hcode i).choose_spec
  have hinj : Function.Injective codeOf := by
    intro i j hij
    have hvalue : PA.Term.numeralValue M i.val =
        PA.Term.numeralValue M j.val :=
      h.standardCode_functional (codeOf i).val
        (codeOf_spec i)
        (by simpa [hij] using codeOf_spec j)
    exact Fin.ext (h.numeral_injective hvalue)
  exact no_injective_fin_succ bound codeOf hinj

/-- `cutAt` defines exactly the externally standard elements. -/
theorem sat_cutAt_iff_isStandard {alpha : Type u}
    {M : PA.PreModel alpha} {evalFormula : PA.Formula} {seed : alpha}
    (h : Contract M evalFormula seed) (tail : Nat → alpha) (x : alpha) :
    PA.Formula.Sat M
        (SetTheory.scons x (SetTheory.scons seed tail))
        (cutAt evalFormula) ↔
      IsStandard M x := by
  rw [sat_cutAt_iff]
  constructor
  · intro hnotCover
    rcases h.standard_or_above x with hstandard | habove
    · exact hstandard
    · exact False.elim (hnotCover (covers_of_aboveAllNumerals h habove))
  · rintro ⟨n, hx⟩
    simpa [SetTheory.scons, hx] using not_covers_numeral h n

theorem sat_cutAt_zero {alpha : Type u}
    {M : PA.PreModel alpha} {evalFormula : PA.Formula} {seed : alpha}
    (h : Contract M evalFormula seed) (tail : Nat → alpha) :
    PA.Formula.Sat M
      (SetTheory.scons M.zero (SetTheory.scons seed tail))
      (cutAt evalFormula) := by
  rw [sat_cutAt_iff_isStandard h tail]
  exact ⟨0, rfl⟩

theorem sat_cutAt_succ {alpha : Type u}
    {M : PA.PreModel alpha} {evalFormula : PA.Formula} {seed : alpha}
    (h : Contract M evalFormula seed) (tail : Nat → alpha) (x : alpha)
    (hx : PA.Formula.Sat M
      (SetTheory.scons x (SetTheory.scons seed tail))
      (cutAt evalFormula)) :
    PA.Formula.Sat M
      (SetTheory.scons (M.succ x) (SetTheory.scons seed tail))
      (cutAt evalFormula) := by
  rw [sat_cutAt_iff_isStandard h tail] at hx ⊢
  obtain ⟨n, rfl⟩ := hx
  exact ⟨n + 1, rfl⟩

theorem not_sat_cutAt_seed {alpha : Type u}
    {M : PA.PreModel alpha} {evalFormula : PA.Formula} {seed : alpha}
    (h : Contract M evalFormula seed) (tail : Nat → alpha) :
    ¬PA.Formula.Sat M
      (SetTheory.scons seed (SetTheory.scons seed tail))
      (cutAt evalFormula) := by
  rw [sat_cutAt_iff]
  exact not_not_intro (covers_of_aboveAllNumerals h h.seed_above)

/-- The unsealed induction axiom for `cutAt` is false: zero belongs to the
cut, the cut is successor-closed, but the distinguished seed is outside it. -/
theorem not_sat_inductionForm {alpha : Type u}
    {M : PA.PreModel alpha} {evalFormula : PA.Formula} {seed : alpha}
    (h : Contract M evalFormula seed) (tail : Nat → alpha) :
    ¬PA.Formula.Sat M (SetTheory.scons seed tail)
      (PA.Formula.inductionForm (cutAt evalFormula)) := by
  intro hind
  have hantecedent :
      PA.Formula.Sat M (SetTheory.scons seed tail)
        (PA.Formula.and
          (PA.Formula.subst PA.Formula.substZero (cutAt evalFormula))
          (PA.Formula.all
            (PA.Formula.imp (cutAt evalFormula)
              (PA.Formula.subst PA.Formula.substSuccVar
                (cutAt evalFormula))))) := by
    constructor
    · exact (PA.Formula.sat_substZero M (cutAt evalFormula)
        (SetTheory.scons seed tail)).mpr
        (sat_cutAt_zero h tail)
    · intro x hx
      exact (PA.Formula.sat_substSuccVar M (cutAt evalFormula)
        (SetTheory.scons seed tail) x).mpr
        (sat_cutAt_succ h tail x hx)
  have hall := hind hantecedent
  exact not_sat_cutAt_seed h tail (hall seed)

/-- The genuine sealed PA induction axiom for `cutAt` is false at every
ambient valuation. -/
theorem not_sat_sealed_induction {alpha : Type u}
    {M : PA.PreModel alpha} {evalFormula : PA.Formula} {seed : alpha}
    (h : Contract M evalFormula seed) (e : Nat → alpha) :
    ¬PA.Formula.Sat M e
      (PA.Formula.sealPA
        (PA.Formula.inductionForm (cutAt evalFormula))) := by
  intro hsealed
  let induction := PA.Formula.inductionForm (cutAt evalFormula)
  have hallSealed : ∀ e' : Nat → alpha,
      PA.Formula.Sat M e' (PA.Formula.sealPA induction) := by
    intro e'
    apply (PA.Formula.Sat_ext_free M (PA.Formula.sealPA induction)
      (e := e) (e' := e') ?_).mp hsealed
    intro n hfree
    exact False.elim (PA.Formula.sealPA_sentence induction n hfree)
  have hallInduction : ∀ e' : Nat → alpha,
      PA.Formula.Sat M e' induction :=
    (PA.Formula.seal_valid M induction).mp hallSealed
  exact not_sat_inductionForm h (fun _ => M.zero)
    (hallInduction (SetTheory.scons seed (fun _ => M.zero)))

theorem sealed_induction_is_ax_s (evalFormula : PA.Formula) :
    PA.Formula.Ax_s
      (PA.Formula.sealPA
        (PA.Formula.inductionForm (cutAt evalFormula))) :=
  PA.Formula.Ax_s_induction (cutAt evalFormula)

/-! ## Packaging the remaining evaluator-realization boundary -/

/-- The exact remaining model-construction obligation: at every fragment
rank, produce a raw model satisfying that fragment together with one fixed
evaluator formula satisfying `Contract`. -/
def ContractCountermodels : Prop :=
  ∀ n : Nat,
    ∃ (alpha : Type u) (M : PA.PreModel alpha)
      (evalFormula : PA.Formula) (seed : alpha) (e : Nat → alpha),
      Contract M evalFormula seed ∧
      ∀ f, PARankFragment n f → PA.Formula.Sat M e f

/-- Contract countermodels are ordinary rank-fragment countermodels, with
the missed PA axiom supplied canonically by the definable cut. -/
theorem rankFragmentCountermodels_of_contracts
    (hmodels : ContractCountermodels.{u}) :
    PARankFragmentCountermodels.{u} := by
  intro n
  obtain ⟨alpha, M, evalFormula, seed, e, hcontract, hfragment⟩ :=
    hmodels n
  let missed := PA.Formula.sealPA
    (PA.Formula.inductionForm (cutAt evalFormula))
  exact ⟨alpha, M, e, missed, hfragment,
    sealed_induction_is_ax_s evalFormula,
    not_sat_sealed_induction hcontract e⟩

/-- Once the evaluator realization satisfies the isolated contract, the
repository's general semantic reduction yields non-finite axiomatizability. -/
theorem pa_not_finitely_axiomatizable_of_contracts
    (hmodels : ContractCountermodels.{u}) :
    ¬FiniteAxiomatization PA.Formula.Ax_s :=
  pa_not_finitely_axiomatizable_of_rankFragmentCountermodels
    (rankFragmentCountermodels_of_contracts hmodels)

end EvaluatorCutContract
end PAFiniteBasisReduction
end LeanProofs
