import PAFiniteBasisReduction.FiniteBetaCoding

/-!
# Transport lemmas for traces in a bounded-rank Skolem hull

The induced hull is only a raw arithmetic structure; it is not assumed to be
a model of PA.  Functionality facts used by the program evaluator are instead
transported to the ambient PA model through bounded-rank elementarity.
-/

namespace LeanProofs
namespace PAFiniteBasisReduction

open SetTheory PA

universe u

namespace FiniteSkolemCut

/-- Elementarity specialized to an environment extended by one hull value. -/
theorem hull_sat_scons_iff_ambient {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (star : alpha) (phi : PA.Formula)
    (hRank : formulaRank phi ≤ rank)
    (out : Carrier M S rank star) (e : Nat → Carrier M S rank star) :
    PA.Formula.Sat (preModel M S rank star) (scons out e) phi ↔
      PA.Formula.Sat M (scons out.val (fun i => (e i).val)) phi := by
  rw [sat_iff_ambient M S rank star phi hRank (scons out e)]
  exact Sat_valEnv_scons M S rank star phi out e

/-- Ambient strict order between hull elements lifts to the hull using only
the fixed low-rank order formula. -/
theorem hull_rawLt_of_ambient {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (star : alpha)
    (hLtRank : formulaRank
      (PA.Formula.ltTermAt (PA.Term.var 0) (PA.Term.var 1)) ≤ rank)
    {x y : Carrier M S rank star} (hxy : RawLt M x.val y.val) :
    RawLt (preModel M S rank star) x y := by
  let KM := preModel M S rank star
  let tailK : Nat → Carrier M S rank star := fun _ => KM.zero
  apply (sat_ltTermAt_vars_iff KM x y tailK).mp
  apply (sat_iff_ambient M S rank star
    (PA.Formula.ltTermAt (PA.Term.var 0) (PA.Term.var 1))
    hLtRank (scons x (scons y tailK))).mpr
  apply (sat_ltTermAt_vars_iff M x.val y.val
    (fun i => (tailK i).val)).mpr
  exact hxy

/-- Projecting a hull strict-order witness to the ambient carrier needs no
logical assumptions: the hull arithmetic operations are restrictions of the
ambient ones. -/
theorem ambient_rawLt_of_hull {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (star : alpha) {x y : Carrier M S rank star}
    (hxy : RawLt (preModel M S rank star) x y) : RawLt M x.val y.val := by
  rcases hxy with ⟨gap, hgap⟩
  refine ⟨gap.val, ?_⟩
  exact congrArg Subtype.val hgap

/-- Projection of hull numerals to ambient numerals. -/
@[simp] theorem hull_numeralValue_val_transport {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (star : alpha) :
    ∀ n,
      (PA.Term.numeralValue (preModel M S rank star) n).val =
        PA.Term.numeralValue M n
  | 0 => rfl
  | n + 1 => by
      simp only [PA.Term.numeralValue, preModel_succ_val,
        hull_numeralValue_val_transport M S rank star n]

/-- Projecting a hull non-strict-order witness is likewise purely
algebraic. -/
theorem ambient_rawLe_of_hull {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (star : alpha) {x y : Carrier M S rank star}
    (hxy : RawLe (preModel M S rank star) x y) : RawLe M x.val y.val := by
  rcases hxy with ⟨gap, hgap⟩
  refine ⟨gap.val, ?_⟩
  exact congrArg Subtype.val hgap

/-- A hull element non-strictly below a standard hull numeral is a standard
hull numeral.  PA is used only after projecting the witness to the ambient
model. -/
theorem hull_rawLe_numeralValue_cases {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (star : alpha) (hPA : RawPASatisfies M)
    {x : Carrier M S rank star} (n : Nat)
    (hle : RawLe (preModel M S rank star) x
      (PA.Term.numeralValue (preModel M S rank star) n)) :
    ∃ k, k ≤ n ∧
      x = PA.Term.numeralValue (preModel M S rank star) k := by
  have hambient : RawLe M x.val (PA.Term.numeralValue M n) := by
    simpa only [hull_numeralValue_val_transport] using
      (ambient_rawLe_of_hull M S rank star hle)
  rcases rawLe_numeralValue_cases hPA n hambient with ⟨k, hk, hx⟩
  refine ⟨k, hk, ?_⟩
  apply Subtype.ext
  simpa only [hull_numeralValue_val_transport] using hx

/-- Strictly bounded hull codes are standard with a strictly smaller
external index. -/
theorem hull_rawLt_numeralValue_cases {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (star : alpha) (hPA : RawPASatisfies M)
    {x : Carrier M S rank star} (n : Nat)
    (hlt : RawLt (preModel M S rank star) x
      (PA.Term.numeralValue (preModel M S rank star) n)) :
    ∃ k, k < n ∧
      x = PA.Term.numeralValue (preModel M S rank star) k := by
  have hambient : RawLt M x.val (PA.Term.numeralValue M n) := by
    simpa only [hull_numeralValue_val_transport] using
      (ambient_rawLt_of_hull M S rank star hlt)
  rcases rawLt_numeralValue_cases hPA n hambient with ⟨k, hk, hx⟩
  refine ⟨k, hk, ?_⟩
  apply Subtype.ext
  simpa only [hull_numeralValue_val_transport] using hx

/-- The discrete linear order inherited from ambient PA is trichotomous on
the hull, without any PA-satisfaction assumption on the hull. -/
theorem hull_raw_order_trichotomy {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (star : alpha) (hPA : RawPASatisfies M)
    (hLtRank : formulaRank
      (PA.Formula.ltTermAt (PA.Term.var 0) (PA.Term.var 1)) ≤ rank)
    (x y : Carrier M S rank star) :
    x = y ∨ RawLt (preModel M S rank star) x y ∨
      RawLt (preModel M S rank star) y x := by
  rcases raw_order_trichotomy hPA x.val y.val with hxy | hxy | hyx
  · exact Or.inl (Subtype.ext hxy)
  · exact Or.inr (Or.inl
      (hull_rawLt_of_ambient M S rank star hLtRank hxy))
  · exact Or.inr (Or.inr
      (hull_rawLt_of_ambient M S rank star hLtRank hyx))

/-- Exact transport of the fixed beta-entry relation between the hull and
the ambient PA model.  This is useful both for table construction and for
table uniqueness. -/
theorem hull_rawBetaEntry_iff_ambient {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (star : alpha)
    (hBetaRank : formulaRank
      (PA.Formula.betaTermTermAt
        (PA.Term.var 0) (PA.Term.var 1)
        (PA.Term.var 2) (PA.Term.var 3)) ≤ rank)
    {out code step idx : Carrier M S rank star} :
    RawBetaEntry (preModel M S rank star) out code step idx ↔
      RawBetaEntry M out.val code.val step.val idx.val := by
  let KM := preModel M S rank star
  let betaFormula := PA.Formula.betaTermTermAt
    (PA.Term.var 0) (PA.Term.var 1)
    (PA.Term.var 2) (PA.Term.var 3)
  let tailK : Nat → Carrier M S rank star := fun _ => KM.zero
  let envK : Nat → Carrier M S rank star :=
    scons out (scons code (scons step (scons idx tailK)))
  constructor
  · intro h
    have hK : PA.Formula.Sat KM envK betaFormula := by
      apply (sat_betaTermTermAt_iff_raw KM
        (PA.Term.var 0) (PA.Term.var 1)
        (PA.Term.var 2) (PA.Term.var 3) envK).mpr
      simpa [envK, tailK, KM, PA.Term.eval, scons] using h
    have hA := (sat_iff_ambient M S rank star betaFormula
      hBetaRank envK).mp hK
    have hRaw := (sat_betaTermTermAt_iff_raw M
      (PA.Term.var 0) (PA.Term.var 1)
      (PA.Term.var 2) (PA.Term.var 3)
      (fun i => (envK i).val)).mp hA
    simpa [envK, tailK, KM, PA.Term.eval, scons] using hRaw
  · intro h
    have hA : PA.Formula.Sat M
        (fun i => (envK i).val) betaFormula := by
      apply (sat_betaTermTermAt_iff_raw M
        (PA.Term.var 0) (PA.Term.var 1)
        (PA.Term.var 2) (PA.Term.var 3)
        (fun i => (envK i).val)).mpr
      simpa [envK, tailK, KM, PA.Term.eval, scons] using h
    have hK := (sat_iff_ambient M S rank star betaFormula
      hBetaRank envK).mpr hA
    have hRaw := (sat_betaTermTermAt_iff_raw KM
      (PA.Term.var 0) (PA.Term.var 1)
      (PA.Term.var 2) (PA.Term.var 3) envK).mp hK
    simpa [envK, tailK, KM, PA.Term.eval, scons] using hRaw

/-- Beta lookup remains functional in a bounded-rank hull whenever the fixed
beta-entry formula lies below the construction rank.  The proof deliberately
uses PA only in the ambient model. -/
theorem hull_rawBetaEntry_functional {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (star : alpha) (hPA : RawPASatisfies M)
    (hBetaRank : formulaRank
      (PA.Formula.betaTermTermAt
        (PA.Term.var 0) (PA.Term.var 1)
        (PA.Term.var 2) (PA.Term.var 3)) ≤ rank)
    {x y code step idx : Carrier M S rank star}
    (hx : RawBetaEntry (preModel M S rank star) x code step idx)
    (hy : RawBetaEntry (preModel M S rank star) y code step idx) :
    x = y := by
  have hxAmbient : RawBetaEntry M x.val code.val step.val idx.val := by
    exact (hull_rawBetaEntry_iff_ambient M S rank star hBetaRank).mp hx
  have hyAmbient : RawBetaEntry M y.val code.val step.val idx.val := by
    exact (hull_rawBetaEntry_iff_ambient M S rank star hBetaRank).mp hy
  apply Subtype.ext
  exact rawBetaEntry_functional hPA hxAmbient hyAmbient

/-- Selector graphs are functional in the hull from low-rank order
elementarity alone.  In contrast with transporting the whole graph, this
lemma has no rank hypothesis on `body`, so it remains usable for formulas at
the top of the hull's closure rank. -/
theorem hull_leastDefaultGraph_functional_of_order {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (star : alpha) (hPA : RawPASatisfies M)
    (hLtRank : formulaRank
      (PA.Formula.ltTermAt (PA.Term.var 0) (PA.Term.var 1)) ≤ rank)
    (body : PA.Formula) (e : Nat → Carrier M S rank star)
    {x y : Carrier M S rank star}
    (hx : PA.Formula.Sat (preModel M S rank star)
      (scons x e) (leastDefaultGraph body))
    (hy : PA.Formula.Sat (preModel M S rank star)
      (scons y e) (leastDefaultGraph body)) :
    x = y := by
  let KM := preModel M S rank star
  rcases (sat_leastDefaultGraph_iff KM body x e).mp hx with
      hxLeast | hxNone
  · rcases (sat_leastDefaultGraph_iff KM body y e).mp hy with
        hyLeast | hyNone
    · rcases hull_raw_order_trichotomy M S rank star hPA hLtRank x y with
          hxy | hxy | hyx
      · exact hxy
      · exact False.elim (hyLeast.2 x
          ((sat_ltTermAt_vars_iff KM x y e).mpr hxy) hxLeast.1)
      · exact False.elim (hxLeast.2 y
          ((sat_ltTermAt_vars_iff KM y x e).mpr hyx) hyLeast.1)
    · exact False.elim (hyNone.1 ⟨x, hxLeast.1⟩)
  · rcases (sat_leastDefaultGraph_iff KM body y e).mp hy with
        hyLeast | hyNone
    · exact False.elim (hxNone.1 ⟨y, hyLeast.1⟩)
    · apply Subtype.ext
      rw [hxNone.2, hyNone.2]

/-- The same rank-independent selector functionality for universal
counterexample rows. -/
theorem hull_leastCounterexampleGraph_functional_of_order {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (star : alpha) (hPA : RawPASatisfies M)
    (hLtRank : formulaRank
      (PA.Formula.ltTermAt (PA.Term.var 0) (PA.Term.var 1)) ≤ rank)
    (body : PA.Formula) (e : Nat → Carrier M S rank star)
    {x y : Carrier M S rank star}
    (hx : PA.Formula.Sat (preModel M S rank star)
      (scons x e) (leastCounterexampleGraph body))
    (hy : PA.Formula.Sat (preModel M S rank star)
      (scons y e) (leastCounterexampleGraph body)) :
    x = y := by
  exact hull_leastDefaultGraph_functional_of_order M S rank star hPA
    hLtRank (PA.Formula.imp body PA.Formula.bot) e hx hy

/-- A canonical ambient selector row whose body is below the closure rank is
also true in the hull.  Only the body is transported; the larger
least/default graph is unfolded semantically.  This avoids the impossible
requirement that every top-rank body have a still-larger graph below the same
rank. -/
theorem hull_leastDefaultGraph_of_ambient {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (star : alpha) (body : PA.Formula)
    (hBodyRank : formulaRank body ≤ rank)
    (e : Nat → Carrier M S rank star) (out : Carrier M S rank star)
    (hAmbient : PA.Formula.Sat M
      (scons out.val (fun i => (e i).val)) (leastDefaultGraph body)) :
    PA.Formula.Sat (preModel M S rank star)
      (scons out e) (leastDefaultGraph body) := by
  let KM := preModel M S rank star
  apply (sat_leastDefaultGraph_iff KM body out e).mpr
  rcases (sat_leastDefaultGraph_iff M body out.val
      (fun i => (e i).val)).mp hAmbient with hLeast | hNone
  · left
    refine ⟨(hull_sat_scons_iff_ambient M S rank star body
      hBodyRank out e).mpr hLeast.1, ?_⟩
    intro z hzLt hzBody
    have hzLtRaw : RawLt KM z out :=
      (sat_ltTermAt_vars_iff KM z out e).mp hzLt
    have hzLtAmbientRaw : RawLt M z.val out.val :=
      ambient_rawLt_of_hull M S rank star hzLtRaw
    have hzLtAmbient : PA.Formula.Sat M
        (scons z.val (scons out.val (fun i => (e i).val)))
        (PA.Formula.ltTermAt (PA.Term.var 0) (PA.Term.var 1)) :=
      (sat_ltTermAt_vars_iff M z.val out.val
        (fun i => (e i).val)).mpr hzLtAmbientRaw
    have hzBodyAmbient : PA.Formula.Sat M
        (scons z.val (fun i => (e i).val)) body :=
      (hull_sat_scons_iff_ambient M S rank star body
        hBodyRank z e).mp hzBody
    exact hLeast.2 z.val hzLtAmbient hzBodyAmbient
  · right
    refine ⟨?_, ?_⟩
    · rintro ⟨z, hzBody⟩
      apply hNone.1
      exact ⟨z.val, (hull_sat_scons_iff_ambient M S rank star body
        hBodyRank z e).mp hzBody⟩
    · apply Subtype.ext
      exact hNone.2

/-- Counterexample-selector rows have the same body-only transport. -/
theorem hull_leastCounterexampleGraph_of_ambient {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (star : alpha) (body : PA.Formula)
    (hNegBodyRank : formulaRank
      (PA.Formula.imp body PA.Formula.bot) ≤ rank)
    (e : Nat → Carrier M S rank star) (out : Carrier M S rank star)
    (hAmbient : PA.Formula.Sat M
      (scons out.val (fun i => (e i).val))
      (leastCounterexampleGraph body)) :
    PA.Formula.Sat (preModel M S rank star)
      (scons out e) (leastCounterexampleGraph body) := by
  exact hull_leastDefaultGraph_of_ambient M S rank star
    (PA.Formula.imp body PA.Formula.bot) hNegBodyRank e out hAmbient

/-- The fixed least/default selector graph remains functional in the hull
when that graph is below the closure rank.  This is a direct elementarity
argument and does not assert that the hull satisfies PA. -/
theorem hull_leastDefaultGraph_functional {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (star : alpha) (body : PA.Formula)
    (hGraphRank : formulaRank (leastDefaultGraph body) ≤ rank)
    (e : Nat → Carrier M S rank star) {x y : Carrier M S rank star}
    (hx : PA.Formula.Sat (preModel M S rank star)
      (scons x e) (leastDefaultGraph body))
    (hy : PA.Formula.Sat (preModel M S rank star)
      (scons y e) (leastDefaultGraph body)) :
    x = y := by
  have hxRawEnv : PA.Formula.Sat M
      (fun i => (scons x e i).val) (leastDefaultGraph body) :=
    (sat_iff_ambient M S rank star (leastDefaultGraph body)
      hGraphRank (scons x e)).mp hx
  have hyRawEnv : PA.Formula.Sat M
      (fun i => (scons y e i).val) (leastDefaultGraph body) :=
    (sat_iff_ambient M S rank star (leastDefaultGraph body)
      hGraphRank (scons y e)).mp hy
  have hxAmbient : PA.Formula.Sat M
      (scons x.val (fun i => (e i).val)) (leastDefaultGraph body) :=
    (Sat_valEnv_scons M S rank star (leastDefaultGraph body) x e).mp
      hxRawEnv
  have hyAmbient : PA.Formula.Sat M
      (scons y.val (fun i => (e i).val)) (leastDefaultGraph body) :=
    (Sat_valEnv_scons M S rank star (leastDefaultGraph body) y e).mp
      hyRawEnv
  apply Subtype.ext
  exact S.graph_functional body (fun i => (e i).val) hxAmbient hyAmbient

/-- Universal-counterexample selector rows inherit the same hull
functionality through their definition as a least/default graph. -/
theorem hull_leastCounterexampleGraph_functional {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (star : alpha) (body : PA.Formula)
    (hGraphRank : formulaRank (leastCounterexampleGraph body) ≤ rank)
    (e : Nat → Carrier M S rank star) {x y : Carrier M S rank star}
    (hx : PA.Formula.Sat (preModel M S rank star)
      (scons x e) (leastCounterexampleGraph body))
    (hy : PA.Formula.Sat (preModel M S rank star)
      (scons y e) (leastCounterexampleGraph body)) :
    x = y := by
  exact hull_leastDefaultGraph_functional M S rank star
    (PA.Formula.imp body PA.Formula.bot) hGraphRank e hx hy

end FiniteSkolemCut
end PAFiniteBasisReduction
end LeanProofs
