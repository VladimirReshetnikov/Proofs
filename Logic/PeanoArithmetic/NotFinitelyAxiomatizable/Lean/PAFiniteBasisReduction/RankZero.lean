import PAFiniteBasisReduction.Hierarchy

/-!
# An explicit countermodel for the rank-zero PA fragment

The carrier consists of two disjoint successor chains.  The ordinary chain
starts at the interpretation of zero; the second chain has an extra root
which is neither zero nor a successor.  Addition and multiplication recurse
on the numeric coordinate of their right argument, so all six non-induction
axioms hold.  Induction fails for the formula saying that an element is zero
or a successor.
-/

namespace LeanProofs
namespace PAFiniteBasisReduction

open SetTheory PA

/-- Two disjoint copies of the natural-number successor chain. -/
abbrev TwoChain := Bool × Nat

/-- The raw arithmetic structure used to separate the rank-zero fragment. -/
def twoChainPreModel : PA.PreModel TwoChain where
  zero := (false, 0)
  succ a := (a.1, a.2 + 1)
  add a b := (a.1, a.2 + b.2)
  mul a b := (false, a.2 * b.2)

theorem twoChain_succ_injective {a b : TwoChain}
    (h : twoChainPreModel.succ a = twoChainPreModel.succ b) : a = b := by
  rcases a with ⟨ta, na⟩
  rcases b with ⟨tb, nb⟩
  simp only [twoChainPreModel, Prod.mk.injEq] at h ⊢
  exact ⟨h.1, by omega⟩

theorem twoChain_zero_not_succ (a : TwoChain) :
    twoChainPreModel.succ a ≠ twoChainPreModel.zero := by
  rcases a with ⟨tag, n⟩
  simp [twoChainPreModel]

theorem twoChain_add_zero (a : TwoChain) :
    twoChainPreModel.add a twoChainPreModel.zero = a := by
  rcases a with ⟨tag, n⟩
  simp [twoChainPreModel]

theorem twoChain_add_succ (a b : TwoChain) :
    twoChainPreModel.add a (twoChainPreModel.succ b) =
      twoChainPreModel.succ (twoChainPreModel.add a b) := by
  rcases a with ⟨ta, na⟩
  rcases b with ⟨tb, nb⟩
  simp [twoChainPreModel, Nat.add_assoc]

theorem twoChain_mul_zero (a : TwoChain) :
    twoChainPreModel.mul a twoChainPreModel.zero =
      twoChainPreModel.zero := by
  rcases a with ⟨tag, n⟩
  simp [twoChainPreModel]

theorem twoChain_mul_succ (a b : TwoChain) :
    twoChainPreModel.mul a (twoChainPreModel.succ b) =
      twoChainPreModel.add (twoChainPreModel.mul a b) a := by
  rcases a with ⟨ta, na⟩
  rcases b with ⟨tb, nb⟩
  simp [twoChainPreModel, Nat.mul_succ]

/-- `x` is zero or has a predecessor.  Under the existential binder the old
free variable `x` is de Bruijn variable `1`, and the witness is variable `0`. -/
def zeroOrSuccFormula : PA.Formula :=
  PA.Formula.or
    (PA.Formula.eq (PA.Term.var 0) PA.Term.zero)
    (PA.Formula.ex
      (PA.Formula.eq (PA.Term.var 1) (PA.Term.succ (PA.Term.var 0))))

theorem twoChain_zeroOrSucc_zero (e : Nat → TwoChain) :
    PA.Formula.Sat twoChainPreModel
      (SetTheory.scons twoChainPreModel.zero e) zeroOrSuccFormula := by
  exact Or.inl rfl

theorem twoChain_zeroOrSucc_succ (e : Nat → TwoChain) (a : TwoChain) :
    PA.Formula.Sat twoChainPreModel
      (SetTheory.scons (twoChainPreModel.succ a) e) zeroOrSuccFormula := by
  right
  exact ⟨a, rfl⟩

/-- The root of the second chain is neither zero nor a successor. -/
theorem twoChain_zeroOrSucc_extraRoot_false (e : Nat → TwoChain) :
    ¬PA.Formula.Sat twoChainPreModel
      (SetTheory.scons (true, 0) e) zeroOrSuccFormula := by
  rintro (hzero | ⟨a, ha⟩)
  · simp [PA.Formula.Sat, PA.Term.eval,
      twoChainPreModel, SetTheory.scons] at hzero
  · rcases a with ⟨tag, n⟩
    simp [PA.Formula.Sat, PA.Term.eval,
      twoChainPreModel, SetTheory.scons] at ha

/-- The induction antecedent for `zeroOrSuccFormula` holds in the two-chain
structure: zero has the property and every successor has a predecessor. -/
theorem twoChain_zeroOrSucc_inductionAntecedent (e : Nat → TwoChain) :
    PA.Formula.Sat twoChainPreModel e
      (PA.Formula.and
        (PA.Formula.subst PA.Formula.substZero zeroOrSuccFormula)
        (PA.Formula.all
          (PA.Formula.imp zeroOrSuccFormula
            (PA.Formula.subst PA.Formula.substSuccVar zeroOrSuccFormula)))) := by
  constructor
  · exact (PA.Formula.sat_substZero twoChainPreModel
      zeroOrSuccFormula e).mpr (twoChain_zeroOrSucc_zero e)
  · intro a _
    exact (PA.Formula.sat_substSuccVar twoChainPreModel
      zeroOrSuccFormula e a).mpr (twoChain_zeroOrSucc_succ e a)

/-- The unsealed induction axiom fails at every ambient valuation. -/
theorem twoChain_not_sat_inductionForm (e : Nat → TwoChain) :
    ¬PA.Formula.Sat twoChainPreModel e
      (PA.Formula.inductionForm zeroOrSuccFormula) := by
  intro hind
  have hall := hind (twoChain_zeroOrSucc_inductionAntecedent e)
  exact twoChain_zeroOrSucc_extraRoot_false e (hall (true, 0))

/-- Every arithmetic formula has positive structural rank. -/
theorem formulaRank_pos (phi : PA.Formula) : 0 < formulaRank phi := by
  cases phi <;> simp [formulaRank]

theorem twoChain_sat_succInj (e : Nat → TwoChain) :
    PA.Formula.Sat twoChainPreModel e PA.Formula.succInj := by
  intro a b h
  exact twoChain_succ_injective h

theorem twoChain_sat_zeroNotSucc (e : Nat → TwoChain) :
    PA.Formula.Sat twoChainPreModel e PA.Formula.zeroNotSucc := by
  intro a h
  exact twoChain_zero_not_succ a h

theorem twoChain_sat_addZero (e : Nat → TwoChain) :
    PA.Formula.Sat twoChainPreModel e PA.Formula.addZero := by
  intro a
  exact twoChain_add_zero a

theorem twoChain_sat_addSucc (e : Nat → TwoChain) :
    PA.Formula.Sat twoChainPreModel e PA.Formula.addSucc := by
  intro a b
  exact twoChain_add_succ a b

theorem twoChain_sat_mulZero (e : Nat → TwoChain) :
    PA.Formula.Sat twoChainPreModel e PA.Formula.mulZero := by
  intro a
  exact twoChain_mul_zero a

theorem twoChain_sat_mulSucc (e : Nat → TwoChain) :
    PA.Formula.Sat twoChainPreModel e PA.Formula.mulSucc := by
  intro a b
  exact twoChain_mul_succ a b

theorem twoChain_sat_sealed_succInj (e : Nat → TwoChain) :
    PA.Formula.Sat twoChainPreModel e
      (PA.Formula.sealPA PA.Formula.succInj) :=
  (PA.Formula.seal_valid twoChainPreModel PA.Formula.succInj).mpr
    (fun e => twoChain_sat_succInj e) e

theorem twoChain_sat_sealed_zeroNotSucc (e : Nat → TwoChain) :
    PA.Formula.Sat twoChainPreModel e
      (PA.Formula.sealPA PA.Formula.zeroNotSucc) :=
  (PA.Formula.seal_valid twoChainPreModel PA.Formula.zeroNotSucc).mpr
    (fun e => twoChain_sat_zeroNotSucc e) e

theorem twoChain_sat_sealed_addZero (e : Nat → TwoChain) :
    PA.Formula.Sat twoChainPreModel e
      (PA.Formula.sealPA PA.Formula.addZero) :=
  (PA.Formula.seal_valid twoChainPreModel PA.Formula.addZero).mpr
    (fun e => twoChain_sat_addZero e) e

theorem twoChain_sat_sealed_addSucc (e : Nat → TwoChain) :
    PA.Formula.Sat twoChainPreModel e
      (PA.Formula.sealPA PA.Formula.addSucc) :=
  (PA.Formula.seal_valid twoChainPreModel PA.Formula.addSucc).mpr
    (fun e => twoChain_sat_addSucc e) e

theorem twoChain_sat_sealed_mulZero (e : Nat → TwoChain) :
    PA.Formula.Sat twoChainPreModel e
      (PA.Formula.sealPA PA.Formula.mulZero) :=
  (PA.Formula.seal_valid twoChainPreModel PA.Formula.mulZero).mpr
    (fun e => twoChain_sat_mulZero e) e

theorem twoChain_sat_sealed_mulSucc (e : Nat → TwoChain) :
    PA.Formula.Sat twoChainPreModel e
      (PA.Formula.sealPA PA.Formula.mulSucc) :=
  (PA.Formula.seal_valid twoChainPreModel PA.Formula.mulSucc).mpr
    (fun e => twoChain_sat_mulSucc e) e

/-- Rank zero contains no induction instances, since formula ranks are
positive.  Thus the two-chain structure satisfies the entire fragment. -/
theorem twoChain_sat_rankZero (e : Nat → TwoChain) :
    ∀ f, PARankFragment 0 f → PA.Formula.Sat twoChainPreModel e f := by
  intro f hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | ⟨phi, hphi, rfl⟩
  · exact twoChain_sat_sealed_succInj e
  · exact twoChain_sat_sealed_zeroNotSucc e
  · exact twoChain_sat_sealed_addZero e
  · exact twoChain_sat_sealed_addSucc e
  · exact twoChain_sat_sealed_mulZero e
  · exact twoChain_sat_sealed_mulSucc e
  · have := formulaRank_pos phi
    omega

/-- Eliminating a finite block of universal quantifiers produces some
valuation of its body.  This one-way lemma is enough for countermodels and
does not require a general free-variable invariance theorem. -/
theorem exists_sat_of_sat_closeN {alpha : Type} (M : PA.PreModel alpha)
    (k : Nat) (phi : PA.Formula) (e : Nat → alpha)
    (h : PA.Formula.Sat M e (PA.Formula.closeN k phi)) :
    ∃ e' : Nat → alpha, PA.Formula.Sat M e' phi := by
  induction k generalizing phi e with
  | zero =>
      exact ⟨e, h⟩
  | succ k ih =>
      obtain ⟨e', hall⟩ := ih (phi := PA.Formula.all phi) (e := e) h
      exact ⟨SetTheory.scons M.zero e', hall M.zero⟩

/-- The sealed induction instance also fails in the two-chain structure. -/
theorem twoChain_not_sat_sealed_induction (e : Nat → TwoChain) :
    ¬PA.Formula.Sat twoChainPreModel e
      (PA.Formula.sealPA
        (PA.Formula.inductionForm zeroOrSuccFormula)) := by
  intro hsealed
  obtain ⟨e', hind⟩ := exists_sat_of_sat_closeN twoChainPreModel
    (PA.Formula.bound (PA.Formula.inductionForm zeroOrSuccFormula))
    (PA.Formula.inductionForm zeroOrSuccFormula) e hsealed
  exact twoChain_not_sat_inductionForm e' hind

/-- The first unconditional strictness witness: the rank-zero PA fragment
does not derive the displayed genuine PA induction axiom. -/
theorem rankZero_not_bprov_induction :
    ¬PA.Formula.BProv (PARankFragment 0) []
      (PA.Formula.sealPA
        (PA.Formula.inductionForm zeroOrSuccFormula)) := by
  exact not_bprov_of_preModel_counterexample twoChainPreModel
    (fun _ => twoChainPreModel.zero)
    (twoChain_sat_rankZero (fun _ => twoChainPreModel.zero))
    (twoChain_not_sat_sealed_induction
      (fun _ => twoChainPreModel.zero))

theorem rankZero_witness_is_pa_axiom :
    PA.Formula.Ax_s
      (PA.Formula.sealPA
        (PA.Formula.inductionForm zeroOrSuccFormula)) :=
  PA.Formula.Ax_s_induction zeroOrSuccFormula

theorem rankZero_strictness_witness :
    ∃ phi : PA.Formula,
      ¬PA.Formula.BProv (PARankFragment 0) []
        (PA.Formula.sealPA (PA.Formula.inductionForm phi)) :=
  ⟨zeroOrSuccFormula, rankZero_not_bprov_induction⟩

/-- Rank zero misses a concrete genuine sealed PA axiom. -/
theorem rankZero_pa_axiom_separation :
    ∃ psi : PA.Formula,
      PA.Formula.Ax_s psi ∧
      ¬PA.Formula.BProv (PARankFragment 0) [] psi :=
  ⟨PA.Formula.sealPA
      (PA.Formula.inductionForm zeroOrSuccFormula),
    rankZero_witness_is_pa_axiom,
    rankZero_not_bprov_induction⟩

end PAFiniteBasisReduction
end LeanProofs
