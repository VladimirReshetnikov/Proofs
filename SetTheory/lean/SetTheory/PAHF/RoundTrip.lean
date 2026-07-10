/-
  SetTheory.PAHF.RoundTrip

  Syntactic infrastructure for the two PA/HFFin composite interpretations.
  This module defines an internal PA graph for Ackermann's finite-ordinal
  code function, proves its exact standard semantics, and isolates the
  remaining proof-theoretic totality, range, injectivity, term-compatibility,
  and paired-variable formula-induction obligations.
-/
import SetTheory.PAHF.Interpretation

namespace SetTheory
namespace PA
namespace Formula

/-- Standard-model semantics of the term-parametric Ackermann-membership
macro. -/
theorem hfMemTermAt_exact (e : Nat → Nat) (elem : Nat)
    (setCode : Term) :
    Sat natModel e (hfMemTermAt elem setCode) ↔
      AckermannHF.Mem (e elem) (Term.eval natModel e setCode) := by
  rw [← subst_instTerm_hfMemAt_succ_zero]
  rw [Sat_subst]
  have henv : ∀ n,
      Term.eval natModel e (instTerm setCode n) =
        scons (Term.eval natModel e setCode) e n := by
    intro n
    cases n <;> rfl
  exact
    (Sat_ext natModel (hfMemAt (elem+1) 0) henv).trans
      (hfMemAt_exact
        (scons (Term.eval natModel e setCode) e) (elem+1) 0)

/-- In the standard model, the term-parametric graph is precisely Ackermann
adjunction on the values of its three parameter terms. -/
theorem hfAdjoinGraphTermAt_exact (e : Nat → Nat)
    (newCode oldCode elemCode : Term) :
    Sat natModel e (hfAdjoinGraphTermAt newCode oldCode elemCode) ↔
      Term.eval natModel e newCode =
        AckermannHF.adjoin
          (Term.eval natModel e oldCode)
          (Term.eval natModel e elemCode) := by
  constructor
  · intro hgraph
    apply AckermannHF.ext
    intro x
    have hpoint := hgraph x
    rw [Sat_iffForm] at hpoint
    have hor :
        Sat natModel (scons x e)
            (or
              (hfMemTermAt 0 (Term.rename Nat.succ oldCode))
              (eq (Term.var 0) (Term.rename Nat.succ elemCode))) ↔
          (Sat natModel (scons x e)
              (hfMemTermAt 0 (Term.rename Nat.succ oldCode)) ∨
            Sat natModel (scons x e)
              (eq (Term.var 0) (Term.rename Nat.succ elemCode))) :=
      Iff.rfl
    rw [hor] at hpoint
    have heq : Sat natModel (scons x e)
          (eq (Term.var 0) (Term.rename Nat.succ elemCode)) ↔
        x = Term.eval natModel e elemCode := by
      simp [Sat, Term.eval_rename, Term.eval, scons]
    rw [heq] at hpoint
    rw [hfMemTermAt_exact,
      hfMemTermAt_exact] at hpoint
    simpa [Term.eval_rename, Term.eval, scons,
      AckermannHF.mem_adjoin] using hpoint
  · intro hnew x
    rw [Sat_iffForm]
    have hor :
        Sat natModel (scons x e)
            (or
              (hfMemTermAt 0 (Term.rename Nat.succ oldCode))
              (eq (Term.var 0) (Term.rename Nat.succ elemCode))) ↔
          (Sat natModel (scons x e)
              (hfMemTermAt 0 (Term.rename Nat.succ oldCode)) ∨
            Sat natModel (scons x e)
              (eq (Term.var 0) (Term.rename Nat.succ elemCode))) :=
      Iff.rfl
    rw [hor]
    have heq : Sat natModel (scons x e)
          (eq (Term.var 0) (Term.rename Nat.succ elemCode)) ↔
        x = Term.eval natModel e elemCode := by
      simp [Sat, Term.eval_rename, Term.eval, scons]
    rw [heq]
    rw [hfMemTermAt_exact,
      hfMemTermAt_exact]
    simp [hnew, Term.eval_rename, scons,
      AckermannHF.mem_adjoin]

/-- A beta-coded trace of the recursive finite-ordinal code construction.
The sequence starts at the empty code and each successor entry is obtained by
Ackermann adjunction of the current entry to itself. -/
def OrdinalCodeBetaTrace
    (raw coded sequenceCode sequenceStep : Nat) : Prop :=
  BetaEntry sequenceCode sequenceStep 0 0 ∧
    BetaEntry sequenceCode sequenceStep raw coded ∧
      ∀ i, i < raw →
        ∃ current next,
          BetaEntry sequenceCode sequenceStep i current ∧
          BetaEntry sequenceCode sequenceStep (i+1) next ∧
          next = AckermannHF.adjoin current current

theorem OrdinalCodeBetaTrace_value
    {raw coded sequenceCode sequenceStep : Nat}
    (h : OrdinalCodeBetaTrace raw coded sequenceCode sequenceStep) :
    coded = AckermannHF.ordinalCode raw := by
  induction raw generalizing coded with
  | zero =>
      exact BetaEntry_functional h.2.1 h.1
  | succ raw ih =>
      rcases h.2.2 raw (Nat.lt_succ_self raw) with
        ⟨current, next, hcurrent, hnext, hadjoin⟩
      have hprefix : OrdinalCodeBetaTrace
          raw current sequenceCode sequenceStep :=
        ⟨h.1, hcurrent, fun i hi ↦ h.2.2 i (by omega)⟩
      have hcurrentCode : current = AckermannHF.ordinalCode raw :=
        ih hprefix
      have hcodedNext : coded = next :=
        BetaEntry_functional h.2.1 hnext
      calc
        coded = next := hcodedNext
        _ = AckermannHF.adjoin current current := hadjoin
        _ = AckermannHF.adjoin
              (AckermannHF.ordinalCode raw)
              (AckermannHF.ordinalCode raw) := by rw [hcurrentCode]
        _ = AckermannHF.ordinalCode (raw+1) :=
          (AckermannHF.ordinalCode_succ raw).symm

theorem OrdinalCodeBetaTrace_exists (raw : Nat) :
    ∃ sequenceCode sequenceStep,
      OrdinalCodeBetaTrace raw (AckermannHF.ordinalCode raw)
        sequenceCode sequenceStep := by
  let scale : Nat := AckermannHF.ordinalCode raw + 1
  let sequenceStep : Nat := betaFact raw * scale
  have hvalue_le : ∀ i, i ≤ raw →
      AckermannHF.ordinalCode i ≤ AckermannHF.ordinalCode raw := by
    intro i hi
    rcases Nat.lt_or_eq_of_le hi with hlt | rfl
    · exact Nat.le_of_lt (AckermannHF.ordinalCode_lt_of_lt hlt)
    · exact Nat.le_refl _
  have hsmall : ∀ i, i ≤ raw →
      AckermannHF.ordinalCode i < BetaModulus sequenceStep i := by
    intro i hi
    have hltScale : AckermannHF.ordinalCode i < scale := by
      simp only [scale]
      exact Nat.lt_succ_of_le (hvalue_le i hi)
    have hfact : 1 ≤ betaFact raw := betaFact_pos raw
    have hscaleStep : scale ≤ sequenceStep := by
      calc
        scale = 1 * scale := by simp
        _ ≤ betaFact raw * scale := Nat.mul_le_mul_right scale hfact
    have hstepMod : sequenceStep ≤ BetaModulus sequenceStep i := by
      simp only [BetaModulus]
      have hone : 1 ≤ i + 1 := by omega
      have hmul : sequenceStep ≤ (i+1) * sequenceStep := by
        simpa using Nat.mul_le_mul_right sequenceStep hone
      omega
    exact Nat.lt_of_lt_of_le hltScale
      (Nat.le_trans hscaleStep hstepMod)
  rcases beta_entries_exist_through_mul_betaFact
      (N := raw) (scale := scale) AckermannHF.ordinalCode (by
        simpa [sequenceStep] using hsmall) with
    ⟨sequenceCode, hentries⟩
  refine ⟨sequenceCode, sequenceStep, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [sequenceStep, AckermannHF.ordinalCode_zero,
      AckermannHF.empty] using hentries 0 (by omega)
  · exact hentries raw (Nat.le_refl raw)
  · intro i hi
    refine ⟨AckermannHF.ordinalCode i,
      AckermannHF.ordinalCode (i+1), ?_, ?_, ?_⟩
    · exact hentries i (by omega)
    · exact hentries (i+1) (by omega)
    · exact AckermannHF.ordinalCode_succ i

/-- Fully term-parametric one-step witness for the ordinal-code trace. -/
def ordinalCodeStepWitnessTermAt
    (sequenceCode sequenceStep index : Term) : Formula :=
  ex (ex
    (and
      (betaTermTermAt (Term.var 1)
        (Term.rename (fun n ↦ n+2) sequenceCode)
        (Term.rename (fun n ↦ n+2) sequenceStep)
        (Term.rename (fun n ↦ n+2) index))
      (and
        (betaTermTermAt (Term.var 0)
          (Term.rename (fun n ↦ n+2) sequenceCode)
          (Term.rename (fun n ↦ n+2) sequenceStep)
          (Term.succ (Term.rename (fun n ↦ n+2) index)))
        (hfAdjoinGraphTermAt
          (Term.var 0) (Term.var 1) (Term.var 1)))))

/-- Every adjacent beta entry below `raw` follows Ackermann ordinal
successor. -/
def ordinalCodeStepsTermAt
    (sequenceCode sequenceStep raw : Term) : Formula :=
  all
    (imp
      (ltTermAt (Term.var 0) (Term.rename Nat.succ raw))
      (ordinalCodeStepWitnessTermAt
        (Term.rename Nat.succ sequenceCode)
        (Term.rename Nat.succ sequenceStep)
        (Term.var 0)))

/-- Internal PA graph for Ackermann's finite-ordinal code function. -/
def ordinalCodeGraphTermAt (raw coded : Term) : Formula :=
  ex (ex
    (and
      (betaTermTermAt Term.zero (Term.var 1) (Term.var 0) Term.zero)
      (and
        (betaTermTermAt
          (Term.rename (fun n ↦ n+2) coded)
          (Term.var 1) (Term.var 0)
          (Term.rename (fun n ↦ n+2) raw))
        (ordinalCodeStepsTermAt
          (Term.var 1) (Term.var 0)
          (Term.rename (fun n ↦ n+2) raw)))))

def ordinalCodeGraphAt (raw coded : Nat) : Formula :=
  ordinalCodeGraphTermAt (Term.var raw) (Term.var coded)

theorem ordinalCodeStepWitnessTermAt_exact
    (e : Nat → Nat) (sequenceCode sequenceStep index : Term) :
    Sat natModel e
        (ordinalCodeStepWitnessTermAt sequenceCode sequenceStep index) ↔
      ∃ current next,
        BetaEntry
            (Term.eval natModel e sequenceCode)
            (Term.eval natModel e sequenceStep)
            (Term.eval natModel e index) current ∧
          BetaEntry
            (Term.eval natModel e sequenceCode)
            (Term.eval natModel e sequenceStep)
            (Term.eval natModel e index + 1) next ∧
          next = AckermannHF.adjoin current current := by
  constructor
  · intro h
    rcases h with ⟨current, next, hcurrent, hnext, hadjoin⟩
    refine ⟨current, next, ?_, ?_, ?_⟩
    · have hraw := (betaTermTermAt_nat_entry
          (scons next (scons current e))
          (Term.var 1)
          (Term.rename (fun n ↦ n+2) sequenceCode)
          (Term.rename (fun n ↦ n+2) sequenceStep)
          (Term.rename (fun n ↦ n+2) index)).mp hcurrent
      simpa [Term.eval_rename, Term.eval, scons] using hraw
    · have hraw := (betaTermTermAt_nat_entry
          (scons next (scons current e))
          (Term.var 0)
          (Term.rename (fun n ↦ n+2) sequenceCode)
          (Term.rename (fun n ↦ n+2) sequenceStep)
          (Term.succ (Term.rename (fun n ↦ n+2) index))).mp hnext
      simpa [Term.eval_rename, Term.eval, natModel, scons] using hraw
    · have hraw := (hfAdjoinGraphTermAt_exact
          (scons next (scons current e))
          (Term.var 0) (Term.var 1) (Term.var 1)).mp hadjoin
      simpa [Term.eval, natModel, scons] using hraw
  · intro h
    rcases h with ⟨current, next, hcurrent, hnext, hadjoin⟩
    refine ⟨current, next, ?_, ?_, ?_⟩
    · apply (betaTermTermAt_nat_entry
        (scons next (scons current e))
        (Term.var 1)
        (Term.rename (fun n ↦ n+2) sequenceCode)
        (Term.rename (fun n ↦ n+2) sequenceStep)
        (Term.rename (fun n ↦ n+2) index)).mpr
      simpa [Term.eval_rename, Term.eval, scons] using hcurrent
    · apply (betaTermTermAt_nat_entry
        (scons next (scons current e))
        (Term.var 0)
        (Term.rename (fun n ↦ n+2) sequenceCode)
        (Term.rename (fun n ↦ n+2) sequenceStep)
        (Term.succ (Term.rename (fun n ↦ n+2) index))).mpr
      simpa [Term.eval_rename, Term.eval, natModel, scons] using hnext
    · apply (hfAdjoinGraphTermAt_exact
        (scons next (scons current e))
        (Term.var 0) (Term.var 1) (Term.var 1)).mpr
      simpa [Term.eval, scons] using hadjoin

theorem ordinalCodeStepsTermAt_exact
    (e : Nat → Nat) (sequenceCode sequenceStep raw : Term) :
    Sat natModel e
        (ordinalCodeStepsTermAt sequenceCode sequenceStep raw) ↔
      ∀ i, i < Term.eval natModel e raw →
        ∃ current next,
          BetaEntry
              (Term.eval natModel e sequenceCode)
              (Term.eval natModel e sequenceStep)
              i current ∧
            BetaEntry
              (Term.eval natModel e sequenceCode)
              (Term.eval natModel e sequenceStep)
              (i+1) next ∧
            next = AckermannHF.adjoin current current := by
  constructor
  · intro h i hi
    have hlt : Sat natModel (scons i e)
        (ltTermAt (Term.var 0) (Term.rename Nat.succ raw)) := by
      apply (ltTermAt_nat (scons i e)
        (Term.var 0) (Term.rename Nat.succ raw)).mpr
      simpa [Term.eval_rename, Term.eval, scons] using hi
    have hstep := h i hlt
    have hspec := (ordinalCodeStepWitnessTermAt_exact
      (scons i e)
      (Term.rename Nat.succ sequenceCode)
      (Term.rename Nat.succ sequenceStep)
      (Term.var 0)).mp hstep
    simpa [Term.eval_rename, Term.eval, scons] using hspec
  · intro h i hlt
    have hiRaw := (ltTermAt_nat (scons i e)
      (Term.var 0) (Term.rename Nat.succ raw)).mp hlt
    have hi : i < Term.eval natModel e raw := by
      simpa [Term.eval_rename, Term.eval, scons] using hiRaw
    have hspec := h i hi
    apply (ordinalCodeStepWitnessTermAt_exact
      (scons i e)
      (Term.rename Nat.succ sequenceCode)
      (Term.rename Nat.succ sequenceStep)
      (Term.var 0)).mpr
    simpa [Term.eval_rename, Term.eval, scons] using hspec

theorem ordinalCodeGraphTermAt_trace_exact
    (e : Nat → Nat) (raw coded : Term) :
    Sat natModel e (ordinalCodeGraphTermAt raw coded) ↔
      ∃ sequenceCode sequenceStep,
        OrdinalCodeBetaTrace
          (Term.eval natModel e raw)
          (Term.eval natModel e coded)
          sequenceCode sequenceStep := by
  constructor
  · intro h
    rcases h with
      ⟨sequenceCode, sequenceStep, hzero, hend, hsteps⟩
    refine ⟨sequenceCode, sequenceStep, ?_, ?_, ?_⟩
    · have hraw := (betaTermTermAt_nat_entry
          (scons sequenceStep (scons sequenceCode e))
          Term.zero (Term.var 1) (Term.var 0) Term.zero).mp hzero
      simpa [Term.eval, natModel, scons] using hraw
    · have hraw := (betaTermTermAt_nat_entry
          (scons sequenceStep (scons sequenceCode e))
          (Term.rename (fun n ↦ n+2) coded)
          (Term.var 1) (Term.var 0)
          (Term.rename (fun n ↦ n+2) raw)).mp hend
      simpa [Term.eval_rename, Term.eval, scons] using hraw
    · have hraw := (ordinalCodeStepsTermAt_exact
          (scons sequenceStep (scons sequenceCode e))
          (Term.var 1) (Term.var 0)
          (Term.rename (fun n ↦ n+2) raw)).mp hsteps
      simpa [Term.eval_rename, Term.eval, scons] using hraw
  · intro h
    rcases h with
      ⟨sequenceCode, sequenceStep, hzero, hend, hsteps⟩
    refine ⟨sequenceCode, sequenceStep, ?_, ?_, ?_⟩
    · apply (betaTermTermAt_nat_entry
        (scons sequenceStep (scons sequenceCode e))
        Term.zero (Term.var 1) (Term.var 0) Term.zero).mpr
      simpa [Term.eval, natModel, scons] using hzero
    · apply (betaTermTermAt_nat_entry
        (scons sequenceStep (scons sequenceCode e))
        (Term.rename (fun n ↦ n+2) coded)
        (Term.var 1) (Term.var 0)
        (Term.rename (fun n ↦ n+2) raw)).mpr
      simpa [Term.eval_rename, Term.eval, scons] using hend
    · apply (ordinalCodeStepsTermAt_exact
        (scons sequenceStep (scons sequenceCode e))
        (Term.var 1) (Term.var 0)
        (Term.rename (fun n ↦ n+2) raw)).mpr
      simpa [Term.eval_rename, Term.eval, scons] using hsteps

theorem ordinalCodeGraphTermAt_exact
    (e : Nat → Nat) (raw coded : Term) :
    Sat natModel e (ordinalCodeGraphTermAt raw coded) ↔
      Term.eval natModel e coded =
        AckermannHF.ordinalCode (Term.eval natModel e raw) := by
  constructor
  · intro h
    rcases (ordinalCodeGraphTermAt_trace_exact e raw coded).mp h with
      ⟨sequenceCode, sequenceStep, htrace⟩
    exact OrdinalCodeBetaTrace_value htrace
  · intro h
    rcases OrdinalCodeBetaTrace_exists (Term.eval natModel e raw) with
      ⟨sequenceCode, sequenceStep, htrace⟩
    apply (ordinalCodeGraphTermAt_trace_exact e raw coded).mpr
    refine ⟨sequenceCode, sequenceStep, ?_⟩
    simpa [h] using htrace

theorem ordinalCodeGraphAt_exact
    (e : Nat → Nat) (raw coded : Nat) :
    Sat natModel e (ordinalCodeGraphAt raw coded) ↔
      e coded = AckermannHF.ordinalCode (e raw) := by
  simpa [ordinalCodeGraphAt, Term.eval] using
    (ordinalCodeGraphTermAt_exact e (Term.var raw) (Term.var coded))

/-- The coded-ordinal domain appearing in the PA-side composite. -/
def codedOrdinalDomain : Formula :=
  translateHFFormula AckermannHF.PAInHF.domainForm

theorem codedOrdinalDomain_exact (e : Nat → Nat) :
    Sat natModel e codedOrdinalDomain ↔
      ∃ raw, AckermannHF.ordinalCode raw = e 0 :=
  (translateHFFormula_exact AckermannHF.PAInHF.domainForm e).trans
    (AckermannHF.PAInHF.domain_exact e)

/-- Closed totality sentence for the internal ordinal-code graph. -/
def ordinalCodeGraphTotal : Formula :=
  all (ex (ordinalCodeGraphAt 1 0))

/-- Closed range characterization: the graph hits exactly the relativized
coded-ordinal domain. -/
def ordinalCodeGraphRange : Formula :=
  all
    (iffForm codedOrdinalDomain
      (ex (ordinalCodeGraphAt 0 1)))

theorem standard_sat_ordinalCodeGraphTotal (e : Nat → Nat) :
    Sat natModel e ordinalCodeGraphTotal := by
  intro raw
  refine ⟨AckermannHF.ordinalCode raw, ?_⟩
  apply (ordinalCodeGraphAt_exact
    (scons (AckermannHF.ordinalCode raw) (scons raw e)) 1 0).mpr
  simp [scons]

theorem standard_sat_ordinalCodeGraphRange (e : Nat → Nat) :
    Sat natModel e ordinalCodeGraphRange := by
  intro coded
  rw [Sat_iffForm]
  constructor
  · intro hdomain
    rcases (codedOrdinalDomain_exact (scons coded e)).mp hdomain with
      ⟨raw, hraw⟩
    refine ⟨raw, ?_⟩
    apply (ordinalCodeGraphAt_exact
      (scons raw (scons coded e)) 0 1).mpr
    simpa [Term.eval, scons] using hraw.symm
  · intro hgraph
    rcases hgraph with ⟨raw, hraw⟩
    have hcode := (ordinalCodeGraphAt_exact
      (scons raw (scons coded e)) 0 1).mp hraw
    apply (codedOrdinalDomain_exact (scons coded e)).mpr
    refine ⟨raw, ?_⟩
    simpa [Term.eval, scons] using hcode.symm

/-- HF slot map used for a translated term graph: slot `0` is the graph
output, and slot `n+1` contains the code paired with raw PA variable `n`. -/
def codedTermSlotMap (codedOut : Nat) (codedMap : Nat → Nat) : Nat → Nat
  | 0 => codedOut
  | n+1 => codedMap n

/-- Reverse-translate the finite-ordinal graph of a PA term while selecting
explicit PA slots for the coded inputs and output. -/
def compositeTermGraphAt
    (codedOut : Nat) (codedMap : Nat → Nat) (t : Term) : Formula :=
  hfFormulaAt (codedTermSlotMap codedOut codedMap)
    (AckermannHF.PAInHF.termGraphAt (fun n ↦ n+1) 0 t)

/-- Formula-level composite with an explicit map from intermediate HF slots
to the PA slots containing their ordinal codes. -/
def paCompositeAt (codedMap : Nat → Nat) (phi : Formula) : Formula :=
  hfFormulaAt codedMap
    (AckermannHF.PAInHF.formulaAt (fun n : Nat ↦ n) phi)

theorem paCompositeAt_id (phi : Formula) :
    paCompositeAt (fun n : Nat ↦ n) phi =
      translateHFFormula (AckermannHF.PAInHF.translateFormula phi) := rfl

/-- The translated coded-ordinal domain is unchanged by the slot-map lift
introduced for a surrounding PA quantifier. -/
theorem hfFormulaAt_domain_up_eq_codedOrdinalDomain
    (codedMap : Nat → Nat) :
    hfFormulaAt (hfUpVarMap codedMap)
        AckermannHF.PAInHF.domainForm =
      codedOrdinalDomain := by
  unfold codedOrdinalDomain translateHFFormula
  apply hfFormulaAt_ext_free
  intro n hn
  have hn0 := AckermannHF.PAInHF.domainForm_free hn
  subst n
  rfl

theorem PAInHF_formulaAt_up_id (phi : Formula) :
    AckermannHF.PAInHF.formulaAt
        (AckermannHF.PAInHF.upVarMap (fun n : Nat ↦ n)) phi =
      AckermannHF.PAInHF.formulaAt (fun n : Nat ↦ n) phi := by
  apply AckermannHF.PAInHF.formulaAt_map_ext
  intro n
  cases n <;> rfl

/-- Universal PA composites quantify over exactly the translated coded
ordinal domain. -/
theorem paCompositeAt_all_normalForm
    (codedMap : Nat → Nat) (phi : Formula) :
    paCompositeAt codedMap (all phi) =
      all (imp codedOrdinalDomain
        (paCompositeAt (hfUpVarMap codedMap) phi)) := by
  simp only [paCompositeAt, AckermannHF.PAInHF.formulaAt,
    hfFormulaAt]
  rw [hfFormulaAt_domain_up_eq_codedOrdinalDomain]
  rw [PAInHF_formulaAt_up_id]

/-- Existential PA composites quantify over exactly the translated coded
ordinal domain. -/
theorem paCompositeAt_ex_normalForm
    (codedMap : Nat → Nat) (phi : Formula) :
    paCompositeAt codedMap (ex phi) =
      ex (and codedOrdinalDomain
        (paCompositeAt (hfUpVarMap codedMap) phi)) := by
  simp only [paCompositeAt, AckermannHF.PAInHF.formulaAt,
    hfFormulaAt]
  rw [hfFormulaAt_domain_up_eq_codedOrdinalDomain]
  rw [PAInHF_formulaAt_up_id]

/-- Paired slot map used after opening a coded ordinal by the range theorem:
the raw witness is slot `0`, the coded value is slot `1`, and outer raw
variables have moved through both binders. -/
def rangeRawMap (rawMap : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => rawMap n + 2

def rangeCodedMap (codedMap : Nat → Nat) : Nat → Nat
  | 0 => 1
  | n+1 => codedMap n + 2

/-- Paired slot map used after totality chooses a code for a bound raw value:
the coded witness is slot `0`, the raw value is slot `1`, and outer variables
have moved through both binders. -/
def totalRawMap (rawMap : Nat → Nat) : Nat → Nat
  | 0 => 1
  | n+1 => rawMap n + 2

def totalCodedMap (codedMap : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => codedMap n + 2

theorem rename_paCompositeAt
    (r : Nat → Nat) (codedMap : Nat → Nat) (phi : Formula) :
    rename r (paCompositeAt codedMap phi) =
      paCompositeAt (fun n ↦ r (codedMap n)) phi := by
  simpa [paCompositeAt] using
    (rename_hfFormulaAt
      (AckermannHF.PAInHF.formulaAt (fun n : Nat ↦ n) phi)
      codedMap r)

theorem rename_succ_paCompositeAt_up
    (codedMap : Nat → Nat) (phi : Formula) :
    rename Nat.succ
        (paCompositeAt (hfUpVarMap codedMap) phi) =
      paCompositeAt (rangeCodedMap codedMap) phi := by
  rw [rename_paCompositeAt]
  apply congrArg (fun m ↦ paCompositeAt m phi)
  funext n
  cases n <;> rfl

theorem rename_succ_rawBody
    (rawMap : Nat → Nat) (phi : Formula) :
    rename Nat.succ
        (rename (AckermannHF.PAInHF.upVarMap rawMap) phi) =
      rename (totalRawMap rawMap) phi := by
  rw [rename_comp]
  apply rename_ext
  intro n
  cases n <;> rfl

theorem subst_instTerm_range_rawBody
    (rawMap : Nat → Nat) (phi : Formula) :
    subst (instTerm (Term.var 0))
        (rename (SetTheory.up Nat.succ)
          (rename (SetTheory.up Nat.succ)
            (rename (AckermannHF.PAInHF.upVarMap rawMap) phi))) =
      rename (rangeRawMap rawMap) phi := by
  rw [subst_instTerm_var_zero_rename_up_succ]
  rw [rename_comp]
  apply rename_ext
  intro n
  cases n <;> rfl

theorem subst_instTerm_total_codedBody
    (codedMap : Nat → Nat) (phi : Formula) :
    subst (instTerm (Term.var 0))
        (rename (SetTheory.up Nat.succ)
          (rename (SetTheory.up Nat.succ)
            (paCompositeAt (hfUpVarMap codedMap) phi))) =
      paCompositeAt (totalCodedMap codedMap) phi := by
  rw [subst_instTerm_var_zero_rename_up_succ]
  rw [rename_paCompositeAt]
  apply congrArg (fun m ↦ paCompositeAt m phi)
  funext n
  cases n <;> rfl

/-- Exact syntactic Code-graph frontier.

The first three fields are the graph's totality/range/injectivity kit.  The
last field is the sole term-language compatibility theorem needed to reduce
composite equality atoms to the Code relation. -/
structure OrdinalCodeGraphProofs where
  total : ∀ (G : List Formula) (raw : Term),
    BProv Ax_s G
      (ex (ordinalCodeGraphTermAt
        (Term.rename Nat.succ raw) (Term.var 0)))
  range : ∀ (G : List Formula) (coded : Term),
    BProv Ax_s G
      (iffForm
        (subst (instTerm coded) codedOrdinalDomain)
        (ex (ordinalCodeGraphTermAt
          (Term.var 0) (Term.rename Nat.succ coded))))
  injective : ∀ {G : List Formula} {raw₁ raw₂ coded : Term},
    BProv Ax_s G (ordinalCodeGraphTermAt raw₁ coded) →
    BProv Ax_s G (ordinalCodeGraphTermAt raw₂ coded) →
    BProv Ax_s G (eq raw₁ raw₂)
  term_graph : ∀ (G : List Formula) (t : Term)
      (rawMap codedMap : Nat → Nat) (codedOut : Nat),
    (∀ n, Term.Free n t →
      BProv Ax_s G (ordinalCodeGraphAt (rawMap n) (codedMap n))) →
    BProv Ax_s G
      (iffForm
        (compositeTermGraphAt codedOut codedMap t)
        (ordinalCodeGraphTermAt
          (Term.rename rawMap t) (Term.var codedOut)))

theorem codedOrdinalDomain_free
    {i : Nat} (h : Free i codedOrdinalDomain) : i = 0 := by
  rcases hfFormulaAt_free AckermannHF.PAInHF.domainForm h with
    ⟨n, hn, hi⟩
  have hn0 := AckermannHF.PAInHF.domainForm_free hn
  exact hi.trans hn0

theorem subst_instTerm_var_zero_codedOrdinalDomain :
    subst (instTerm (Term.var 0)) codedOrdinalDomain =
      codedOrdinalDomain := by
  rw [subst_instTerm_var]
  calc
    rename (SetTheory.inst 0) codedOrdinalDomain =
        rename (fun n : Nat ↦ n) codedOrdinalDomain := by
      apply rename_ext_free
      intro n hn
      have hn0 := codedOrdinalDomain_free hn
      subst n
      rfl
    _ = codedOrdinalDomain := rename_id codedOrdinalDomain

/-- Use the range equivalence to open an arbitrary coded ordinal as the Code
of a raw PA value. -/
theorem BProv_Ax_s_ordinalCodeGraph_range_of_domain
    (P : OrdinalCodeGraphProofs)
    {G : List Formula} {coded : Term}
    (hdomain : BProv Ax_s G
      (subst (instTerm coded) codedOrdinalDomain)) :
    BProv Ax_s G
      (ex (ordinalCodeGraphTermAt
        (Term.var 0) (Term.rename Nat.succ coded))) := by
  have hrange := P.range G coded
  have hforward : BProv Ax_s G
      (imp
        (subst (instTerm coded) codedOrdinalDomain)
        (ex (ordinalCodeGraphTermAt
          (Term.var 0) (Term.rename Nat.succ coded)))) := by
    simpa [iffForm] using BProv_andE1 hrange
  exact BProv_mp Ax_s G _ _ hforward hdomain

/-- Conditional structural formula-induction package.  Its `formula_exact`
field is the logical induction driven by `OrdinalCodeGraphProofs`; keeping it
separate makes the remaining de Bruijn/context plumbing explicit. -/
structure PACompositeStructuralProofs extends OrdinalCodeGraphProofs where
  formula_exact : ∀ (G : List Formula) (phi : Formula)
      (rawMap codedMap : Nat → Nat),
    (∀ n, Free n phi →
      BProv Ax_s G (ordinalCodeGraphAt (rawMap n) (codedMap n))) →
    BProv Ax_s G
      (iffForm (rename rawMap phi) (paCompositeAt codedMap phi))

/-- A completed paired-variable structural induction immediately closes the
PA composite identity on sentences. -/
theorem BProv_Ax_s_pa_roundTrip_of_structuralProofs
    (P : PACompositeStructuralProofs)
    (phi : Formula) (hphi : Sentence phi) :
    BProv Ax_s []
      (iffForm phi
        (translateHFFormula
          (AckermannHF.PAInHF.translateFormula phi))) := by
  have h := P.formula_exact [] phi
    (fun n : Nat ↦ n) (fun n : Nat ↦ n)
    (fun n hn ↦ False.elim (hphi n hn))
  simpa [paCompositeAt_id, rename_id] using h

/-- The β-trace recurrence is vacuous at raw input zero. -/
theorem BProv_Ax_s_ordinalCodeStepsTermAt_zero
    {G : List Formula} (sequenceCode sequenceStep : Term) :
    BProv Ax_s G
      (ordinalCodeStepsTermAt sequenceCode sequenceStep Term.zero) := by
  let antecedent : Formula := ltTermAt (Term.var 0) Term.zero
  let consequent : Formula :=
    ordinalCodeStepWitnessTermAt
      (Term.rename Nat.succ sequenceCode)
      (Term.rename Nat.succ sequenceStep)
      (Term.var 0)
  let body : Formula := imp antecedent consequent
  have hbody : BProv Ax_s
      (antecedent :: G.map (rename Nat.succ)) consequent := by
    let C : List Formula := antecedent :: G.map (rename Nat.succ)
    have hlt : BProv Ax_s C
        (ltTermAt (Term.var 0) Term.zero) := by
      simpa [C, antecedent] using
        (BProv_ass (B := Ax_s) (G := C) (by simp [C, antecedent]))
    have hle : BProv Ax_s C
        (leTermAt Term.zero (Term.var 0)) :=
      BProv_Ax_s_leTermAt_zero_left (Term.var 0)
    have hbot : BProv Ax_s C bot :=
      BProv_Ax_s_ltTermAt_leTermAt_bot hlt hle
    exact BProv_botE (B := Ax_s) (G := C)
      (a := consequent) hbot
  have himp : BProv Ax_s (G.map (rename Nat.succ)) body := by
    simpa [body] using BProv_impI hbody
  have hall : BProv Ax_s G (all body) :=
    BProv_allI_of_sentences (B := Ax_s)
      (fun f hf ↦ sentence_ax_s (f := f) hf) himp
  simpa [ordinalCodeStepsTermAt, body, antecedent, consequent,
    Term.rename] using hall

/-- Binder-free body used to package the two beta-sequence witnesses. -/
def ordinalCodeGraphBodyTermAt
    (sequenceCode sequenceStep raw coded : Term) : Formula :=
  and
    (betaTermTermAt Term.zero sequenceCode sequenceStep Term.zero)
    (and
      (betaTermTermAt coded sequenceCode sequenceStep raw)
      (ordinalCodeStepsTermAt sequenceCode sequenceStep raw))

theorem subst_betaTermTermAt
    (sigma : Nat → Term) (out code step index : Term) :
    subst sigma (betaTermTermAt out code step index) =
      betaTermTermAt
        (Term.subst sigma out)
        (Term.subst sigma code)
        (Term.subst sigma step)
        (Term.subst sigma index) := by
  simp [betaTermTermAt, betaModTermTerm, remTermTermAt,
    ltTermAt, subst, Term.subst, Term.upSubst,
    Term.subst_rename_succ_up]

theorem rename_betaTermTermAt
    (r : Nat → Nat) (out code step index : Term) :
    rename r (betaTermTermAt out code step index) =
      betaTermTermAt
        (Term.rename r out)
        (Term.rename r code)
        (Term.rename r step)
        (Term.rename r index) := by
  rw [← subst_var_rename, subst_betaTermTermAt]
  simp only [term_subst_var_rename]

theorem subst_ordinalCodeStepWitnessTermAt
    (sigma : Nat → Term) (sequenceCode sequenceStep index : Term) :
    subst sigma
        (ordinalCodeStepWitnessTermAt
          sequenceCode sequenceStep index) =
      ordinalCodeStepWitnessTermAt
        (Term.subst sigma sequenceCode)
        (Term.subst sigma sequenceStep)
        (Term.subst sigma index) := by
  have hshift2 (t : Term) :
      Term.subst (Term.upSubst (Term.upSubst sigma))
          (Term.rename (fun n ↦ n+2) t) =
        Term.rename (fun n ↦ n+2) (Term.subst sigma t) := by
    change Term.subst (iterUpSubst 2 sigma)
        (Term.rename (fun n ↦ n+2) t) =
      Term.rename (fun n ↦ n+2) (Term.subst sigma t)
    exact term_subst_iterUpSubst_rename_add 2 sigma t
  simp [ordinalCodeStepWitnessTermAt,
    subst_betaTermTermAt, subst_hfAdjoinGraphTermAt,
    subst, Term.subst, Term.upSubst, Term.rename, hshift2]

theorem subst_ordinalCodeStepsTermAt
    (sigma : Nat → Term) (sequenceCode sequenceStep raw : Term) :
    subst sigma
        (ordinalCodeStepsTermAt sequenceCode sequenceStep raw) =
      ordinalCodeStepsTermAt
        (Term.subst sigma sequenceCode)
        (Term.subst sigma sequenceStep)
        (Term.subst sigma raw) := by
  simp [ordinalCodeStepsTermAt,
    subst_ordinalCodeStepWitnessTermAt, subst_ltTermAt,
    subst, Term.subst, Term.upSubst,
    Term.subst_rename_succ_up]

theorem subst_ordinalCodeGraphTermAt
    (sigma : Nat → Term) (raw coded : Term) :
    subst sigma (ordinalCodeGraphTermAt raw coded) =
      ordinalCodeGraphTermAt
        (Term.subst sigma raw) (Term.subst sigma coded) := by
  have hshift2 (t : Term) :
      Term.subst (Term.upSubst (Term.upSubst sigma))
          (Term.rename (fun n ↦ n+2) t) =
        Term.rename (fun n ↦ n+2) (Term.subst sigma t) := by
    change Term.subst (iterUpSubst 2 sigma)
        (Term.rename (fun n ↦ n+2) t) =
      Term.rename (fun n ↦ n+2) (Term.subst sigma t)
    exact term_subst_iterUpSubst_rename_add 2 sigma t
  simp [ordinalCodeGraphTermAt,
    subst_betaTermTermAt,
    subst_ordinalCodeStepsTermAt,
    subst, Term.subst, Term.upSubst, Term.rename, hshift2]

theorem subst_ordinalCodeGraphBodyTermAt
    (sigma : Nat → Term)
    (sequenceCode sequenceStep raw coded : Term) :
    subst sigma
        (ordinalCodeGraphBodyTermAt
          sequenceCode sequenceStep raw coded) =
      ordinalCodeGraphBodyTermAt
        (Term.subst sigma sequenceCode)
        (Term.subst sigma sequenceStep)
        (Term.subst sigma raw)
        (Term.subst sigma coded) := by
  simp [ordinalCodeGraphBodyTermAt,
    subst_betaTermTermAt,
    subst_ordinalCodeStepsTermAt, subst, Term.subst]

theorem rename_ordinalCodeStepWitnessTermAt
    (r : Nat → Nat) (sequenceCode sequenceStep index : Term) :
    rename r
        (ordinalCodeStepWitnessTermAt
          sequenceCode sequenceStep index) =
      ordinalCodeStepWitnessTermAt
        (Term.rename r sequenceCode)
        (Term.rename r sequenceStep)
        (Term.rename r index) := by
  rw [← subst_var_rename,
    subst_ordinalCodeStepWitnessTermAt]
  simp only [term_subst_var_rename]

theorem rename_ordinalCodeStepsTermAt
    (r : Nat → Nat) (sequenceCode sequenceStep raw : Term) :
    rename r
        (ordinalCodeStepsTermAt sequenceCode sequenceStep raw) =
      ordinalCodeStepsTermAt
        (Term.rename r sequenceCode)
        (Term.rename r sequenceStep)
        (Term.rename r raw) := by
  rw [← subst_var_rename, subst_ordinalCodeStepsTermAt]
  simp only [term_subst_var_rename]

theorem rename_ordinalCodeGraphTermAt
    (r : Nat → Nat) (raw coded : Term) :
    rename r (ordinalCodeGraphTermAt raw coded) =
      ordinalCodeGraphTermAt
        (Term.rename r raw) (Term.rename r coded) := by
  rw [← subst_var_rename, subst_ordinalCodeGraphTermAt]
  simp only [term_subst_var_rename]

theorem rename_ordinalCodeGraphBodyTermAt
    (r : Nat → Nat)
    (sequenceCode sequenceStep raw coded : Term) :
    rename r
        (ordinalCodeGraphBodyTermAt
          sequenceCode sequenceStep raw coded) =
      ordinalCodeGraphBodyTermAt
        (Term.rename r sequenceCode)
        (Term.rename r sequenceStep)
        (Term.rename r raw)
        (Term.rename r coded) := by
  rw [← subst_var_rename,
    subst_ordinalCodeGraphBodyTermAt]
  simp only [term_subst_var_rename]

/-- Instantiating the inner graph binder supplies the sequence-step term. -/
theorem subst_instTerm_ordinalCodeGraphBody_inner
    (sequenceCode sequenceStep raw coded : Term) :
    subst (instTerm sequenceStep)
        (ordinalCodeGraphBodyTermAt
          (Term.rename Nat.succ sequenceCode)
          (Term.var 0)
          (Term.rename Nat.succ raw)
          (Term.rename Nat.succ coded)) =
      ordinalCodeGraphBodyTermAt
        sequenceCode sequenceStep raw coded := by
  rw [subst_ordinalCodeGraphBodyTermAt]
  simp [instTerm, Term.subst, term_subst_instTerm_rename_succ]

/-- Instantiating the outer graph binder supplies the sequence-code term while
leaving the inner sequence-step binder protected. -/
theorem subst_instTerm_ordinalCodeGraphBody_outer
    (sequenceCode raw coded : Term) :
    subst (instTerm sequenceCode)
        (ex (ordinalCodeGraphBodyTermAt
          (Term.var 1)
          (Term.var 0)
          (Term.rename (fun n ↦ n+2) raw)
          (Term.rename (fun n ↦ n+2) coded))) =
      ex (ordinalCodeGraphBodyTermAt
        (Term.rename Nat.succ sequenceCode)
        (Term.var 0)
        (Term.rename Nat.succ raw)
        (Term.rename Nat.succ coded)) := by
  simp only [subst, subst_ordinalCodeGraphBodyTermAt]
  simp [instTerm, Term.subst, Term.upSubst,
    term_subst_upSubst_instTerm_rename_two_succ]

/-- Package explicit beta-sequence code and step terms into the internal
ordinal-code graph's two existential binders. -/
theorem BProv_ordinalCodeGraphTermAt_of_body
    {B : Formula → Prop} {G : List Formula}
    {sequenceCode sequenceStep raw coded : Term}
    (hbody : BProv B G
      (ordinalCodeGraphBodyTermAt
        sequenceCode sequenceStep raw coded)) :
    BProv B G (ordinalCodeGraphTermAt raw coded) := by
  have hinnerInst : BProv B G
      (subst (instTerm sequenceStep)
        (ordinalCodeGraphBodyTermAt
          (Term.rename Nat.succ sequenceCode)
          (Term.var 0)
          (Term.rename Nat.succ raw)
          (Term.rename Nat.succ coded))) := by
    rw [subst_instTerm_ordinalCodeGraphBody_inner]
    exact hbody
  have hinner : BProv B G
      (ex (ordinalCodeGraphBodyTermAt
        (Term.rename Nat.succ sequenceCode)
        (Term.var 0)
        (Term.rename Nat.succ raw)
        (Term.rename Nat.succ coded))) :=
    BProv_exI (B := B) (G := G) hinnerInst
  have houterInst : BProv B G
      (subst (instTerm sequenceCode)
        (ex (ordinalCodeGraphBodyTermAt
          (Term.var 1)
          (Term.var 0)
          (Term.rename (fun n ↦ n+2) raw)
          (Term.rename (fun n ↦ n+2) coded)))) := by
    rw [subst_instTerm_ordinalCodeGraphBody_outer]
    exact hinner
  have hgraph : BProv B G
      (ex (ex (ordinalCodeGraphBodyTermAt
        (Term.var 1)
        (Term.var 0)
        (Term.rename (fun n ↦ n+2) raw)
        (Term.rename (fun n ↦ n+2) coded)))) :=
    BProv_exI (B := B) (G := G) houterInst
  simpa [ordinalCodeGraphTermAt,
    ordinalCodeGraphBodyTermAt] using hgraph

/-- A concrete Code witness lies in the translated coded-ordinal domain. -/
theorem BProv_Ax_s_codedOrdinalDomain_of_ordinalCodeGraph
    (P : OrdinalCodeGraphProofs)
    {G : List Formula} {raw coded : Term}
    (hgraph : BProv Ax_s G
      (ordinalCodeGraphTermAt raw coded)) :
    BProv Ax_s G
      (subst (instTerm coded) codedOrdinalDomain) := by
  have hinst : BProv Ax_s G
      (subst (instTerm raw)
        (ordinalCodeGraphTermAt
          (Term.var 0) (Term.rename Nat.succ coded))) := by
    simpa [subst_ordinalCodeGraphTermAt, instTerm, Term.subst,
      term_subst_instTerm_rename_succ] using hgraph
  have hex : BProv Ax_s G
      (ex (ordinalCodeGraphTermAt
        (Term.var 0) (Term.rename Nat.succ coded))) :=
    BProv_exI hinst
  have hrange := P.range G coded
  have hreverse : BProv Ax_s G
      (imp
        (ex (ordinalCodeGraphTermAt
          (Term.var 0) (Term.rename Nat.succ coded)))
        (subst (instTerm coded) codedOrdinalDomain)) := by
    simpa [iffForm] using BProv_andE2 hrange
  exact BProv_mp Ax_s G _ _ hreverse hex

/-- The explicit beta trace witnessing the Ackermann ordinal code of zero. -/
theorem BProv_Ax_s_ordinalCodeGraphTermAt_zero
    {G : List Formula} :
    BProv Ax_s G
      (ordinalCodeGraphTermAt Term.zero Term.zero) := by
  have hstepZero : BProv Ax_s G (eq Term.zero Term.zero) :=
    BProv_eqRefl (B := Ax_s) (G := G) Term.zero
  have hentry : BProv Ax_s G
      (betaTermTermAt Term.zero Term.zero Term.zero Term.zero) :=
    BProv_Ax_s_betaTermTermAt_zero_of_eq_step_zero hstepZero
  have hsteps : BProv Ax_s G
      (ordinalCodeStepsTermAt Term.zero Term.zero Term.zero) :=
    BProv_Ax_s_ordinalCodeStepsTermAt_zero Term.zero Term.zero
  exact BProv_ordinalCodeGraphTermAt_of_body
    (BProv_andI hentry (BProv_andI hentry hsteps))

/-- Base case in precisely the existential shape used by graph totality. -/
theorem BProv_Ax_s_ordinalCodeGraphTermAt_zero_exists
    {G : List Formula} :
    BProv Ax_s G
      (ex (ordinalCodeGraphTermAt
        (Term.rename Nat.succ Term.zero) (Term.var 0))) := by
  apply BProv_exI (t := Term.zero)
  simpa [subst_ordinalCodeGraphTermAt, instTerm, Term.subst,
    Term.rename] using
    (BProv_Ax_s_ordinalCodeGraphTermAt_zero (G := G))

theorem BProv_Ax_s_ordinalCodeStepWitnessTermAt_of_components
    {G : List Formula}
    {sequenceCode sequenceStep index current next : Term}
    (hcurrent : BProv Ax_s G
      (betaTermTermAt current sequenceCode sequenceStep index))
    (hnext : BProv Ax_s G
      (betaTermTermAt next sequenceCode sequenceStep
        (Term.succ index)))
    (hadjoin : BProv Ax_s G
      (hfAdjoinGraphTermAt next current current)) :
    BProv Ax_s G
      (ordinalCodeStepWitnessTermAt
        sequenceCode sequenceStep index) := by
  let body : Formula :=
    and
      (betaTermTermAt (Term.var 1)
        (Term.rename (fun n => n + 2) sequenceCode)
        (Term.rename (fun n => n + 2) sequenceStep)
        (Term.rename (fun n => n + 2) index))
      (and
        (betaTermTermAt (Term.var 0)
          (Term.rename (fun n => n + 2) sequenceCode)
          (Term.rename (fun n => n + 2) sequenceStep)
          (Term.succ (Term.rename (fun n => n + 2) index)))
        (hfAdjoinGraphTermAt
          (Term.var 0) (Term.var 1) (Term.var 1)))
  have hcomponents : BProv Ax_s G
      (and
        (betaTermTermAt current sequenceCode sequenceStep index)
        (and
          (betaTermTermAt next sequenceCode sequenceStep
            (Term.succ index))
          (hfAdjoinGraphTermAt next current current))) :=
    BProv_andI hcurrent (BProv_andI hnext hadjoin)
  apply BProv_exI (t := current)
  apply BProv_exI (t := next)
  simpa [ordinalCodeStepWitnessTermAt, body,
    subst_betaTermTermAt, subst_hfAdjoinGraphTermAt,
    subst, instTerm, Term.subst, Term.upSubst,
    Term.subst_rename_succ_up,
    term_subst_instTerm_rename_succ,
    term_subst_instTerm_rename_two_succ,
    term_subst_upSubst_instTerm_rename_two_succ,
    term_subst_up_up_instTerm_rename_three_succ,
    Term.rename_comp, Function.comp_def] using hcomponents

/-- Instantiate the bounded ordinal-code recurrence at an arbitrary term
known to lie below its raw bound. -/
theorem BProv_Ax_s_ordinalCodeStepsTermAt_step_of_ltTerm
    {G : List Formula}
    {sequenceCode sequenceStep raw index : Term}
    (hsteps : BProv Ax_s G
      (ordinalCodeStepsTermAt sequenceCode sequenceStep raw))
    (hlt : BProv Ax_s G (ltTermAt index raw)) :
    BProv Ax_s G
      (ordinalCodeStepWitnessTermAt
        sequenceCode sequenceStep index) := by
  have himpRaw := BProv_allE (B := Ax_s) (G := G)
    (t := index) hsteps
  have himp : BProv Ax_s G
      (imp (ltTermAt index raw)
        (ordinalCodeStepWitnessTermAt
          sequenceCode sequenceStep index)) := by
    simpa [ordinalCodeStepsTermAt,
      subst_ordinalCodeStepWitnessTermAt,
      subst_ltTermAt, subst, instTerm, Term.subst,
      Term.upSubst, Term.subst_rename_succ_up,
      term_subst_instTerm_rename_succ] using himpRaw
  exact BProv_mp Ax_s G _ _ himp hlt

/-- Prefix agreement transports an Ackermann-adjoin trace edge when both of
its adjacent indices lie below the agreement bound. -/
theorem BProv_Ax_s_ordinalCodeStepWitnessTermAt_of_prefixAgreement
    {G : List Formula}
    {oldCode newCode step bound index : Term}
    (hagreement : BProv Ax_s G
      (betaPrefixAgreementTermAt oldCode newCode step bound))
    (hltCurrent : BProv Ax_s G (ltTermAt index bound))
    (hltNext : BProv Ax_s G
      (ltTermAt (Term.succ index) bound))
    (hwitness : BProv Ax_s G
      (ordinalCodeStepWitnessTermAt oldCode step index)) :
    BProv Ax_s G
      (ordinalCodeStepWitnessTermAt newCode step index) := by
  let target : Formula :=
    ordinalCodeStepWitnessTermAt newCode step index
  let body : Formula :=
    and
      (betaTermTermAt (Term.var 1)
        (Term.rename (fun n => n + 2) oldCode)
        (Term.rename (fun n => n + 2) step)
        (Term.rename (fun n => n + 2) index))
      (and
        (betaTermTermAt (Term.var 0)
          (Term.rename (fun n => n + 2) oldCode)
          (Term.rename (fun n => n + 2) step)
          (Term.succ (Term.rename (fun n => n + 2) index)))
        (hfAdjoinGraphTermAt
          (Term.var 0) (Term.var 1) (Term.var 1)))
  have hwit : BProv Ax_s G (ex (ex body)) := by
    simpa [ordinalCodeStepWitnessTermAt, body] using hwitness
  have houter : BProv Ax_s
      (ex body :: G.map (rename Nat.succ))
      (rename Nat.succ target) := by
    let G1 : List Formula := ex body :: G.map (rename Nat.succ)
    have hexInner : BProv Ax_s G1 (ex body) :=
      BProv_ass (B := Ax_s) (G := G1) (by simp [G1])
    have hinner : BProv Ax_s
        (body :: G1.map (rename Nat.succ))
        (rename Nat.succ (rename Nat.succ target)) := by
      let C : List Formula := body :: G1.map (rename Nat.succ)
      let oldCode2 : Term := Term.rename (fun n => n + 2) oldCode
      let newCode2 : Term := Term.rename (fun n => n + 2) newCode
      let step2 : Term := Term.rename (fun n => n + 2) step
      let bound2 : Term := Term.rename (fun n => n + 2) bound
      let index2 : Term := Term.rename (fun n => n + 2) index
      have hbody : BProv Ax_s C body :=
        BProv_ass (B := Ax_s) (G := C) (by simp [C])
      have hcurrent : BProv Ax_s C
          (betaTermTermAt (Term.var 1) oldCode2 step2 index2) := by
        simpa [body, oldCode2, step2, index2] using BProv_andE1 hbody
      have htail : BProv Ax_s C
          (and
            (betaTermTermAt (Term.var 0) oldCode2 step2
              (Term.succ index2))
            (hfAdjoinGraphTermAt
              (Term.var 0) (Term.var 1) (Term.var 1))) := by
        simpa [body, oldCode2, step2, index2] using BProv_andE2 hbody
      have hnext : BProv Ax_s C
          (betaTermTermAt (Term.var 0) oldCode2 step2
            (Term.succ index2)) := BProv_andE1 htail
      have hadjoin : BProv Ax_s C
          (hfAdjoinGraphTermAt
            (Term.var 0) (Term.var 1) (Term.var 1)) := BProv_andE2 htail
      have hagreementRen1 : BProv Ax_s (G.map (rename Nat.succ))
          (rename Nat.succ
            (betaPrefixAgreementTermAt oldCode newCode step bound)) :=
        BProv_rename_of_sentences
          (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
          hagreement Nat.succ
      have hagreementRen2 : BProv Ax_s
          ((G.map (rename Nat.succ)).map (rename Nat.succ))
          (rename Nat.succ (rename Nat.succ
            (betaPrefixAgreementTermAt oldCode newCode step bound))) :=
        BProv_rename_of_sentences
          (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
          hagreementRen1 Nat.succ
      have hagreementC : BProv Ax_s C
          (betaPrefixAgreementTermAt
            oldCode2 newCode2 step2 bound2) := by
        have h1 := BProv_context_cons (B := Ax_s)
          (a := rename Nat.succ (ex body)) hagreementRen2
        have h2 := BProv_context_cons (B := Ax_s) (a := body) h1
        simpa [C, G1, oldCode2, newCode2, step2, bound2,
          betaPrefixAgreementTermAt, betaTermTermAt,
          remTermTermAt, ltTermAt, betaModTermTerm,
          rename, Term.rename, SetTheory.up, Term.rename_comp,
          Function.comp_def, Nat.add_assoc] using h2
      have hltCurrentRen1 : BProv Ax_s (G.map (rename Nat.succ))
          (rename Nat.succ (ltTermAt index bound)) :=
        BProv_rename_of_sentences
          (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
          hltCurrent Nat.succ
      have hltCurrentRen2 : BProv Ax_s
          ((G.map (rename Nat.succ)).map (rename Nat.succ))
          (rename Nat.succ (rename Nat.succ
            (ltTermAt index bound))) :=
        BProv_rename_of_sentences
          (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
          hltCurrentRen1 Nat.succ
      have hltCurrentC : BProv Ax_s C (ltTermAt index2 bound2) := by
        have h1 := BProv_context_cons (B := Ax_s)
          (a := rename Nat.succ (ex body)) hltCurrentRen2
        have h2 := BProv_context_cons (B := Ax_s) (a := body) h1
        simpa [C, G1, index2, bound2, ltTermAt,
          rename, Term.rename, SetTheory.up, Term.rename_comp,
          Function.comp_def, Nat.add_assoc] using h2
      have hltNextRen1 : BProv Ax_s (G.map (rename Nat.succ))
          (rename Nat.succ (ltTermAt (Term.succ index) bound)) :=
        BProv_rename_of_sentences
          (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
          hltNext Nat.succ
      have hltNextRen2 : BProv Ax_s
          ((G.map (rename Nat.succ)).map (rename Nat.succ))
          (rename Nat.succ (rename Nat.succ
            (ltTermAt (Term.succ index) bound))) :=
        BProv_rename_of_sentences
          (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
          hltNextRen1 Nat.succ
      have hltNextC : BProv Ax_s C
          (ltTermAt (Term.succ index2) bound2) := by
        have h1 := BProv_context_cons (B := Ax_s)
          (a := rename Nat.succ (ex body)) hltNextRen2
        have h2 := BProv_context_cons (B := Ax_s) (a := body) h1
        simpa [C, G1, index2, bound2, ltTermAt,
          rename, Term.rename, SetTheory.up, Term.rename_comp,
          Function.comp_def, Nat.add_assoc] using h2
      have hcurrentNew : BProv Ax_s C
          (betaTermTermAt (Term.var 1) newCode2 step2 index2) :=
        BProv_Ax_s_betaPrefixAgreementTermAt_entry_of_ltTerm
          hagreementC hltCurrentC hcurrent
      have hnextNew : BProv Ax_s C
          (betaTermTermAt (Term.var 0) newCode2 step2
            (Term.succ index2)) :=
        BProv_Ax_s_betaPrefixAgreementTermAt_entry_of_ltTerm
          hagreementC hltNextC hnext
      have hnew : BProv Ax_s C
          (ordinalCodeStepWitnessTermAt newCode2 step2 index2) :=
        BProv_Ax_s_ordinalCodeStepWitnessTermAt_of_components
          hcurrentNew hnextNew hadjoin
      simpa [target, C, G1, newCode2, step2, index2,
        rename_ordinalCodeStepWitnessTermAt,
        rename, Term.rename, SetTheory.up, Term.rename_comp,
        Function.comp_def, Nat.add_assoc] using hnew
    exact BProv_exE_of_sentences
      (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
      hexInner (by simpa [G1, rename] using hinner)
  exact BProv_exE_of_sentences
    (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
    hwit (by simpa [target, body, rename] using houter)

theorem subst_betaPrefixAgreementTermAt
    (sigma : Nat → Term) (oldCode newCode step bound : Term) :
    subst sigma
        (betaPrefixAgreementTermAt oldCode newCode step bound) =
      betaPrefixAgreementTermAt
        (Term.subst sigma oldCode) (Term.subst sigma newCode)
        (Term.subst sigma step) (Term.subst sigma bound) := by
  have hshift2 (t : Term) :
      Term.subst (Term.upSubst (Term.upSubst sigma))
          (Term.rename (fun n => n + 2) t) =
        Term.rename (fun n => n + 2) (Term.subst sigma t) := by
    change Term.subst (iterUpSubst 2 sigma)
        (Term.rename (fun n => n + 2) t) =
      Term.rename (fun n => n + 2) (Term.subst sigma t)
    exact term_subst_iterUpSubst_rename_add 2 sigma t
  simp [betaPrefixAgreementTermAt, subst_betaTermTermAt,
    subst_ltTermAt, subst, Term.subst, Term.upSubst,
    Term.subst_rename_succ_up, hshift2, Term.rename]

theorem rename_betaPrefixAgreementTermAt
    (r : Nat → Nat) (oldCode newCode step bound : Term) :
    rename r
        (betaPrefixAgreementTermAt oldCode newCode step bound) =
      betaPrefixAgreementTermAt
        (Term.rename r oldCode) (Term.rename r newCode)
        (Term.rename r step) (Term.rename r bound) := by
  rw [← subst_var_rename,
    subst_betaPrefixAgreementTermAt]
  simp only [term_subst_var_rename]

theorem subst_betaCodeExtensionTermAt
    (sigma : Nat → Term) (oldCode step target newOut newCode : Term) :
    subst sigma
        (betaCodeExtensionTermAt oldCode step target newOut newCode) =
      betaCodeExtensionTermAt
        (Term.subst sigma oldCode) (Term.subst sigma step)
        (Term.subst sigma target) (Term.subst sigma newOut)
        (Term.subst sigma newCode) := by
  simp [betaCodeExtensionTermAt,
    subst_betaPrefixAgreementTermAt,
    subst_betaTermTermAt, subst]

theorem rename_betaCodeExtensionTermAt
    (r : Nat → Nat) (oldCode step target newOut newCode : Term) :
    rename r
        (betaCodeExtensionTermAt oldCode step target newOut newCode) =
      betaCodeExtensionTermAt
        (Term.rename r oldCode) (Term.rename r step)
        (Term.rename r target) (Term.rename r newOut)
        (Term.rename r newCode) := by
  rw [← subst_var_rename,
    subst_betaCodeExtensionTermAt]
  simp only [term_subst_var_rename]

/-- A one-entry beta-code extension transports the old recurrence and adds
the new final Ackermann-adjoin edge.  This is the local successor invariant
used by the strengthened PA induction. -/
theorem BProv_Ax_s_ordinalCodeStepsTermAt_succ_of_extension
    {G : List Formula}
    {oldSequenceCode newSequenceCode sequenceStep raw oldCoded newCoded : Term}
    (hsteps : BProv Ax_s G
      (ordinalCodeStepsTermAt oldSequenceCode sequenceStep raw))
    (hendpoint : BProv Ax_s G
      (betaTermTermAt oldCoded oldSequenceCode sequenceStep raw))
    (hextension : BProv Ax_s G
      (betaCodeExtensionTermAt oldSequenceCode sequenceStep
        (Term.succ raw) newCoded newSequenceCode))
    (hadjoin : BProv Ax_s G
      (hfAdjoinGraphTermAt newCoded oldCoded oldCoded)) :
    BProv Ax_s G
      (ordinalCodeStepsTermAt
        newSequenceCode sequenceStep (Term.succ raw)) := by
  let antecedent : Formula :=
    ltTermAt (Term.var 0)
      (Term.succ (Term.rename Nat.succ raw))
  let consequent : Formula :=
    ordinalCodeStepWitnessTermAt
      (Term.rename Nat.succ newSequenceCode)
      (Term.rename Nat.succ sequenceStep)
      (Term.var 0)
  let body : Formula := imp antecedent consequent
  have hbody : BProv Ax_s
      (antecedent :: G.map (rename Nat.succ)) consequent := by
    let C : List Formula := antecedent :: G.map (rename Nat.succ)
    let oldSequenceCode1 : Term := Term.rename Nat.succ oldSequenceCode
    let newSequenceCode1 : Term := Term.rename Nat.succ newSequenceCode
    let sequenceStep1 : Term := Term.rename Nat.succ sequenceStep
    let raw1 : Term := Term.rename Nat.succ raw
    let oldCoded1 : Term := Term.rename Nat.succ oldCoded
    let newCoded1 : Term := Term.rename Nat.succ newCoded
    have hltSucc : BProv Ax_s C
        (ltTermAt (Term.var 0) (Term.succ raw1)) := by
      simpa [C, antecedent, raw1] using
        (BProv_ass (B := Ax_s) (G := C) (by simp [C, antecedent]))
    have hcases : BProv Ax_s C
        (or (ltTermAt (Term.var 0) raw1)
          (eq (Term.var 0) raw1)) :=
      BProv_Ax_s_ltTermAt_succ_right_cases hltSucc
    have hstepsRen : BProv Ax_s (G.map (rename Nat.succ))
        (rename Nat.succ
          (ordinalCodeStepsTermAt oldSequenceCode sequenceStep raw)) :=
      BProv_rename_of_sentences
        (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
        hsteps Nat.succ
    have hstepsC : BProv Ax_s C
        (ordinalCodeStepsTermAt
          oldSequenceCode1 sequenceStep1 raw1) := by
      have hraw := BProv_context_cons (B := Ax_s)
        (a := antecedent) hstepsRen
      simpa [C, oldSequenceCode1, sequenceStep1, raw1,
        rename_ordinalCodeStepsTermAt] using hraw
    have hendpointRen : BProv Ax_s (G.map (rename Nat.succ))
        (rename Nat.succ
          (betaTermTermAt oldCoded oldSequenceCode sequenceStep raw)) :=
      BProv_rename_of_sentences
        (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
        hendpoint Nat.succ
    have hendpointC : BProv Ax_s C
        (betaTermTermAt oldCoded1 oldSequenceCode1 sequenceStep1 raw1) := by
      have hraw := BProv_context_cons (B := Ax_s)
        (a := antecedent) hendpointRen
      simpa [C, oldCoded1, oldSequenceCode1, sequenceStep1, raw1,
        rename_betaTermTermAt] using hraw
    have hextensionRen : BProv Ax_s (G.map (rename Nat.succ))
        (rename Nat.succ
          (betaCodeExtensionTermAt oldSequenceCode sequenceStep
            (Term.succ raw) newCoded newSequenceCode)) :=
      BProv_rename_of_sentences
        (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
        hextension Nat.succ
    have hextensionC : BProv Ax_s C
        (betaCodeExtensionTermAt oldSequenceCode1 sequenceStep1
          (Term.succ raw1) newCoded1 newSequenceCode1) := by
      have hraw := BProv_context_cons (B := Ax_s)
        (a := antecedent) hextensionRen
      simpa [C, oldSequenceCode1, sequenceStep1, raw1,
        newCoded1, newSequenceCode1,
        rename_betaCodeExtensionTermAt,
        Term.rename] using hraw
    have hagreementC : BProv Ax_s C
        (betaPrefixAgreementTermAt oldSequenceCode1 newSequenceCode1
          sequenceStep1 (Term.succ raw1)) :=
      BProv_Ax_s_betaPrefixAgreementTermAt_of_betaCodeExtensionTermAt
        hextensionC
    have hadjoinRen : BProv Ax_s (G.map (rename Nat.succ))
        (rename Nat.succ
          (hfAdjoinGraphTermAt newCoded oldCoded oldCoded)) :=
      BProv_rename_of_sentences
        (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
        hadjoin Nat.succ
    have hadjoinC : BProv Ax_s C
        (hfAdjoinGraphTermAt newCoded1 oldCoded1 oldCoded1) := by
      have hraw := BProv_context_cons (B := Ax_s)
        (a := antecedent) hadjoinRen
      simpa [C, newCoded1, oldCoded1,
        rename_hfAdjoinGraphTermAt_succ] using hraw
    have hbelow : BProv Ax_s
        (ltTermAt (Term.var 0) raw1 :: C) consequent := by
      let D : List Formula := ltTermAt (Term.var 0) raw1 :: C
      have hlt : BProv Ax_s D (ltTermAt (Term.var 0) raw1) :=
        BProv_ass (B := Ax_s) (G := D) (by simp [D])
      have holdWitness : BProv Ax_s D
          (ordinalCodeStepWitnessTermAt
            oldSequenceCode1 sequenceStep1 (Term.var 0)) :=
        BProv_Ax_s_ordinalCodeStepsTermAt_step_of_ltTerm
          (BProv_context_cons (B := Ax_s) hstepsC) hlt
      have hagreementD := BProv_context_cons (B := Ax_s)
        (a := ltTermAt (Term.var 0) raw1) hagreementC
      have hltCurrent : BProv Ax_s D
          (ltTermAt (Term.var 0) (Term.succ raw1)) :=
        BProv_context_cons (B := Ax_s)
          (a := ltTermAt (Term.var 0) raw1) hltSucc
      have hltNext : BProv Ax_s D
          (ltTermAt (Term.succ (Term.var 0)) (Term.succ raw1)) :=
        BProv_Ax_s_ltTermAt_succ_succ hlt
      have hnewWitness : BProv Ax_s D
          (ordinalCodeStepWitnessTermAt
            newSequenceCode1 sequenceStep1 (Term.var 0)) :=
        BProv_Ax_s_ordinalCodeStepWitnessTermAt_of_prefixAgreement
          hagreementD hltCurrent hltNext holdWitness
      simpa [D, C, consequent, newSequenceCode1, sequenceStep1] using
        hnewWitness
    have hequal : BProv Ax_s
        (eq (Term.var 0) raw1 :: C) consequent := by
      let D : List Formula := eq (Term.var 0) raw1 :: C
      have heq : BProv Ax_s D (eq (Term.var 0) raw1) :=
        BProv_ass (B := Ax_s) (G := D) (by simp [D])
      have hagreementD := BProv_context_cons (B := Ax_s)
        (a := eq (Term.var 0) raw1) hagreementC
      have hendpointD := BProv_context_cons (B := Ax_s)
        (a := eq (Term.var 0) raw1) hendpointC
      have holdAtRaw : BProv Ax_s D
          (betaTermTermAt oldCoded1 newSequenceCode1 sequenceStep1 raw1) :=
        BProv_Ax_s_betaPrefixAgreementTermAt_entry_of_ltTerm
          hagreementD (BProv_Ax_s_ltTermAt_self_succ raw1) hendpointD
      have holdAtIndex : BProv Ax_s D
          (betaTermTermAt oldCoded1 newSequenceCode1 sequenceStep1
            (Term.var 0)) :=
        BProv_Ax_s_betaTermTermAt_of_eq_index
          (BProv_eqSym heq) holdAtRaw
      have hnewAtSuccRaw : BProv Ax_s D
          (betaTermTermAt newCoded1 newSequenceCode1 sequenceStep1
            (Term.succ raw1)) :=
        BProv_Ax_s_betaTermTermAt_of_betaCodeExtensionTermAt
          (BProv_context_cons (B := Ax_s)
            (a := eq (Term.var 0) raw1) hextensionC)
      have hnewAtSuccIndex : BProv Ax_s D
          (betaTermTermAt newCoded1 newSequenceCode1 sequenceStep1
            (Term.succ (Term.var 0))) :=
        BProv_Ax_s_betaTermTermAt_of_eq_index
          (BProv_eq_congr_succ (BProv_eqSym heq)) hnewAtSuccRaw
      have hnewWitness : BProv Ax_s D
          (ordinalCodeStepWitnessTermAt
            newSequenceCode1 sequenceStep1 (Term.var 0)) :=
        BProv_Ax_s_ordinalCodeStepWitnessTermAt_of_components
          holdAtIndex hnewAtSuccIndex
          (BProv_context_cons (B := Ax_s)
            (a := eq (Term.var 0) raw1) hadjoinC)
      simpa [D, C, consequent, newSequenceCode1, sequenceStep1] using
        hnewWitness
    exact BProv_orE hcases hbelow hequal
  have himp : BProv Ax_s (G.map (rename Nat.succ)) body := by
    simpa [body] using BProv_impI hbody
  have hall : BProv Ax_s G (all body) :=
    BProv_allI_of_sentences (B := Ax_s)
      (fun f hf => sentence_ax_s (f := f) hf) himp
  simpa [ordinalCodeStepsTermAt, body, antecedent, consequent,
    Term.rename] using hall

/-- Complete local successor transformer for an explicit ordinal-code trace.
The step is intentionally unchanged; the strengthened induction chooses it
large enough before invoking this theorem. -/
theorem BProv_Ax_s_ordinalCodeGraphBodyTermAt_succ_of_extension
    {G : List Formula}
    {oldSequenceCode newSequenceCode sequenceStep raw oldCoded newCoded : Term}
    (hbody : BProv Ax_s G
      (ordinalCodeGraphBodyTermAt
        oldSequenceCode sequenceStep raw oldCoded))
    (hextension : BProv Ax_s G
      (betaCodeExtensionTermAt oldSequenceCode sequenceStep
        (Term.succ raw) newCoded newSequenceCode))
    (hadjoin : BProv Ax_s G
      (hfAdjoinGraphTermAt newCoded oldCoded oldCoded)) :
    BProv Ax_s G
      (ordinalCodeGraphBodyTermAt
        newSequenceCode sequenceStep (Term.succ raw) newCoded) := by
  have hhead : BProv Ax_s G
      (betaTermTermAt Term.zero oldSequenceCode sequenceStep Term.zero) := by
    simpa [ordinalCodeGraphBodyTermAt] using BProv_andE1 hbody
  have htail : BProv Ax_s G
      (and
        (betaTermTermAt oldCoded oldSequenceCode sequenceStep raw)
        (ordinalCodeStepsTermAt oldSequenceCode sequenceStep raw)) := by
    simpa [ordinalCodeGraphBodyTermAt] using BProv_andE2 hbody
  have hendpoint : BProv Ax_s G
      (betaTermTermAt oldCoded oldSequenceCode sequenceStep raw) :=
    BProv_andE1 htail
  have hsteps : BProv Ax_s G
      (ordinalCodeStepsTermAt oldSequenceCode sequenceStep raw) :=
    BProv_andE2 htail
  have hheadNew : BProv Ax_s G
      (betaTermTermAt Term.zero newSequenceCode sequenceStep Term.zero) :=
    BProv_Ax_s_betaTermTermAt_zero_of_succ_extension
      hhead hextension
  have hendpointNew : BProv Ax_s G
      (betaTermTermAt newCoded newSequenceCode sequenceStep
        (Term.succ raw)) :=
    BProv_Ax_s_betaTermTermAt_of_betaCodeExtensionTermAt hextension
  have hstepsNew : BProv Ax_s G
      (ordinalCodeStepsTermAt
        newSequenceCode sequenceStep (Term.succ raw)) :=
    BProv_Ax_s_ordinalCodeStepsTermAt_succ_of_extension
      hsteps hendpoint hextension hadjoin
  simpa [ordinalCodeGraphBodyTermAt] using
    BProv_andI hheadNew (BProv_andI hendpointNew hstepsNew)

/-- A successor-stage capacity `oldCapacity + newCoded` is sufficient to
re-use the induction hypothesis at the predecessor bound. -/
theorem BProv_Ax_s_betaCodingStepTermAt_old_of_sum_capacity
    {G : List Formula} {raw oldCapacity newCoded step : Term}
    (hcoding : BProv Ax_s G
      (betaCodingStepTermAt (Term.succ raw)
        (Term.add oldCapacity newCoded) step)) :
    BProv Ax_s G
      (betaCodingStepTermAt raw oldCapacity step) := by
  have hcommonSucc : BProv Ax_s G
      (commonMultipleThroughTermAt (Term.succ raw) step) := by
    simpa [betaCodingStepTermAt] using BProv_andE1 hcoding
  have hcommon : BProv Ax_s G
      (commonMultipleThroughTermAt raw step) :=
    BProv_Ax_s_commonMultipleThroughTermAt_of_le hcommonSucc
      (BProv_Ax_s_leTermAt_self_succ raw)
  have hlargeSum : BProv Ax_s G
      (leTermAt (Term.succ (Term.add oldCapacity newCoded)) step) := by
    simpa [betaCodingStepTermAt] using BProv_andE2 hcoding
  have holdLeSum : BProv Ax_s G
      (leTermAt oldCapacity (Term.add oldCapacity newCoded)) :=
    BProv_Ax_s_leTermAt_of_eq_add_right_terms
      (BProv_eqRefl (B := Ax_s) (G := G)
        (Term.add oldCapacity newCoded))
  have hsuccOldLeSum : BProv Ax_s G
      (leTermAt (Term.succ oldCapacity)
        (Term.succ (Term.add oldCapacity newCoded))) :=
    BProv_Ax_s_leTermAt_succ_succ holdLeSum
  have hlargeOld : BProv Ax_s G
      (leTermAt (Term.succ oldCapacity) step) :=
    BProv_Ax_s_leTermAt_trans hsuccOldLeSum hlargeSum
  simpa [betaCodingStepTermAt] using BProv_andI hcommon hlargeOld

/-- The same summed capacity supplies the strict modulus bound needed to
append `newCoded` at index `S raw`. -/
theorem BProv_Ax_s_betaCodeExtensionExistsTermAt_of_sum_capacity
    {G : List Formula}
    {oldSequenceCode raw oldCapacity newCoded step : Term}
    (hcoding : BProv Ax_s G
      (betaCodingStepTermAt (Term.succ raw)
        (Term.add oldCapacity newCoded) step)) :
    BProv Ax_s G
      (betaCodeExtensionExistsTermAt oldSequenceCode step
        (Term.succ raw) newCoded) := by
  have hcommon : BProv Ax_s G
      (commonMultipleThroughTermAt (Term.succ raw) step) := by
    simpa [betaCodingStepTermAt] using BProv_andE1 hcoding
  have hlargeSum : BProv Ax_s G
      (leTermAt (Term.succ (Term.add oldCapacity newCoded)) step) := by
    simpa [betaCodingStepTermAt] using BProv_andE2 hcoding
  have hcomm : BProv Ax_s G
      (eq (Term.add oldCapacity newCoded)
        (Term.add newCoded oldCapacity)) :=
    BProv_Ax_s_add_comm_terms oldCapacity newCoded
  have hnewLeSum : BProv Ax_s G
      (leTermAt newCoded (Term.add oldCapacity newCoded)) :=
    BProv_Ax_s_leTermAt_of_eq_add_right_terms hcomm
  have hsuccNewLeSum : BProv Ax_s G
      (leTermAt (Term.succ newCoded)
        (Term.succ (Term.add oldCapacity newCoded))) :=
    BProv_Ax_s_leTermAt_succ_succ hnewLeSum
  have hlargeNew : BProv Ax_s G
      (leTermAt (Term.succ newCoded) step) :=
    BProv_Ax_s_leTermAt_trans hsuccNewLeSum hlargeSum
  have hstepMod : BProv Ax_s G
      (leTermAt step
        (betaModTermTerm step (Term.succ raw))) :=
    BProv_Ax_s_leTermAt_step_betaModTermTerm step (Term.succ raw)
  have hnewLtMod : BProv Ax_s G
      (ltTermAt newCoded
        (betaModTermTerm step (Term.succ raw))) :=
    BProv_Ax_s_ltTermAt_of_succ_leTermAt
      (BProv_Ax_s_leTermAt_trans hlargeNew hstepMod)
  exact BProv_Ax_s_betaCodeExtensionExistsTermAt_of_common
    hcommon hnewLtMod

/-- Existence of a sequence-code witness for a fixed step and endpoint. -/
def ordinalCodeGraphBodyExistsTermAt
    (step raw coded : Term) : Formula :=
  ex (ordinalCodeGraphBodyTermAt
    (Term.var 0)
    (Term.rename Nat.succ step)
    (Term.rename Nat.succ raw)
    (Term.rename Nat.succ coded))

theorem subst_ordinalCodeGraphBodyExistsTermAt
    (sigma : Nat → Term) (step raw coded : Term) :
    subst sigma
        (ordinalCodeGraphBodyExistsTermAt step raw coded) =
      ordinalCodeGraphBodyExistsTermAt
        (Term.subst sigma step)
        (Term.subst sigma raw)
        (Term.subst sigma coded) := by
  simp [ordinalCodeGraphBodyExistsTermAt,
    subst_ordinalCodeGraphBodyTermAt,
    subst, Term.subst, Term.upSubst,
    Term.subst_rename_succ_up]

theorem rename_ordinalCodeGraphBodyExistsTermAt
    (r : Nat → Nat) (step raw coded : Term) :
    rename r
        (ordinalCodeGraphBodyExistsTermAt step raw coded) =
      ordinalCodeGraphBodyExistsTermAt
        (Term.rename r step)
        (Term.rename r raw)
        (Term.rename r coded) := by
  rw [← subst_var_rename,
    subst_ordinalCodeGraphBodyExistsTermAt]
  simp only [term_subst_var_rename]

theorem BProv_ordinalCodeGraphBodyExistsTermAt_of_term
    {B : Formula → Prop} {G : List Formula}
    {sequenceCode step raw coded : Term}
    (hbody : BProv B G
      (ordinalCodeGraphBodyTermAt sequenceCode step raw coded)) :
    BProv B G
      (ordinalCodeGraphBodyExistsTermAt step raw coded) := by
  apply BProv_exI (t := sequenceCode)
  simpa [ordinalCodeGraphBodyExistsTermAt,
    subst_ordinalCodeGraphBodyTermAt,
    instTerm, Term.subst,
    term_subst_instTerm_rename_succ] using hbody

theorem BProv_Ax_s_ordinalCodeGraphBodyExistsTermAt_elim_opened
    {G : List Formula} {step raw coded : Term} {target : Formula}
    (hopened : BProv Ax_s
      (ordinalCodeGraphBodyTermAt
          (Term.var 0)
          (Term.rename Nat.succ step)
          (Term.rename Nat.succ raw)
          (Term.rename Nat.succ coded) ::
        G.map (rename Nat.succ))
      (rename Nat.succ target))
    (hex : BProv Ax_s G
      (ordinalCodeGraphBodyExistsTermAt step raw coded)) :
    BProv Ax_s G target :=
  BProv_exE_of_sentences
    (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
    hex (by simpa [ordinalCodeGraphBodyExistsTermAt] using hopened)

/-- For a chosen PA coding step, existence of a sequence code realizing the
ordinal graph body.  The separate `capacity` parameter is a deliberately
arithmetic majorant; it avoids requiring an internal proof that Ackermann
adjunction is monotone in its old code. -/
def ordinalCodeTraceCapacityTermAt
    (raw coded capacity : Term) : Formula :=
  all (imp
    (betaCodingStepTermAt
      (Term.rename Nat.succ raw)
      (Term.rename Nat.succ capacity)
      (Term.var 0))
    (ordinalCodeGraphBodyExistsTermAt
      (Term.var 0)
      (Term.rename Nat.succ raw)
      (Term.rename Nat.succ coded)))

/-- Zero has the explicit sequence code zero at every sufficiently large
chosen step, not merely at the special step zero. -/
theorem BProv_Ax_s_ordinalCodeGraphBodyTermAt_zero_at_step
    {G : List Formula} {step : Term}
    (hlarge : BProv Ax_s G
      (leTermAt (Term.succ Term.zero) step)) :
    BProv Ax_s G
      (ordinalCodeGraphBodyTermAt
        Term.zero step Term.zero Term.zero) := by
  have hentry : BProv Ax_s G
      (betaTermTermAt Term.zero Term.zero step Term.zero) :=
    BProv_Ax_s_betaTermTermAt_self_zero_of_succ_le_step hlarge
  have hsteps : BProv Ax_s G
      (ordinalCodeStepsTermAt Term.zero step Term.zero) :=
    BProv_Ax_s_ordinalCodeStepsTermAt_zero Term.zero step
  simpa [ordinalCodeGraphBodyTermAt] using
    BProv_andI hentry (BProv_andI hentry hsteps)

/-- Base case of the majorant-parametric induction invariant. -/
theorem BProv_Ax_s_ordinalCodeTraceCapacityTermAt_zero
    {G : List Formula} :
    BProv Ax_s G
      (ordinalCodeTraceCapacityTermAt
        Term.zero Term.zero Term.zero) := by
  let antecedent : Formula :=
    betaCodingStepTermAt Term.zero Term.zero (Term.var 0)
  let consequent : Formula :=
    ordinalCodeGraphBodyExistsTermAt
      (Term.var 0) Term.zero Term.zero
  let body : Formula := imp antecedent consequent
  have hbody : BProv Ax_s
      (antecedent :: G.map (rename Nat.succ)) consequent := by
    let C : List Formula := antecedent :: G.map (rename Nat.succ)
    have hcoding : BProv Ax_s C
        (betaCodingStepTermAt Term.zero Term.zero (Term.var 0)) :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C, antecedent])
    have hlarge : BProv Ax_s C
        (leTermAt (Term.succ Term.zero) (Term.var 0)) := by
      simpa [betaCodingStepTermAt] using BProv_andE2 hcoding
    have hzero : BProv Ax_s C
        (ordinalCodeGraphBodyTermAt
          Term.zero (Term.var 0) Term.zero Term.zero) :=
      BProv_Ax_s_ordinalCodeGraphBodyTermAt_zero_at_step hlarge
    apply BProv_exI (t := Term.zero)
    simpa [ordinalCodeGraphBodyExistsTermAt,
      subst_ordinalCodeGraphBodyTermAt,
      instTerm, Term.subst,
      term_subst_instTerm_rename_succ] using hzero
  have himp : BProv Ax_s (G.map (rename Nat.succ)) body := by
    simpa [body] using BProv_impI hbody
  have hall : BProv Ax_s G (all body) :=
    BProv_allI_of_sentences (B := Ax_s)
      (fun f hf => sentence_ax_s (f := f) hf) himp
  simpa [ordinalCodeTraceCapacityTermAt,
    body, antecedent, consequent, Term.rename] using hall

theorem BProv_Ax_s_ordinalCodeGraphBodyExistsTermAt_succ_of_sum_capacity
    {G : List Formula}
    {step raw oldCoded newCoded oldCapacity : Term}
    (holdTrace : BProv Ax_s G
      (ordinalCodeGraphBodyExistsTermAt
        step raw oldCoded))
    (hcoding : BProv Ax_s G
      (betaCodingStepTermAt (Term.succ raw)
        (Term.add oldCapacity newCoded) step))
    (hadjoin : BProv Ax_s G
      (hfAdjoinGraphTermAt newCoded oldCoded oldCoded)) :
    BProv Ax_s G
      (ordinalCodeGraphBodyExistsTermAt
        step (Term.succ raw) newCoded) := by
  let goal : Formula :=
    ordinalCodeGraphBodyExistsTermAt
      step (Term.succ raw) newCoded
  refine BProv_Ax_s_ordinalCodeGraphBodyExistsTermAt_elim_opened
    (G := G) (step := step) (raw := raw) (coded := oldCoded)
    (target := goal) ?_ holdTrace
  let oldBody : Formula :=
    ordinalCodeGraphBodyTermAt
      (Term.var 0)
      (Term.rename Nat.succ step)
      (Term.rename Nat.succ raw)
      (Term.rename Nat.succ oldCoded)
  let D : List Formula := oldBody :: G.map (rename Nat.succ)
  let step1 : Term := Term.rename Nat.succ step
  let raw1 : Term := Term.rename Nat.succ raw
  let oldCoded1 : Term := Term.rename Nat.succ oldCoded
  let newCoded1 : Term := Term.rename Nat.succ newCoded
  let oldCapacity1 : Term := Term.rename Nat.succ oldCapacity
  have holdBody : BProv Ax_s D
      (ordinalCodeGraphBodyTermAt
        (Term.var 0) step1 raw1 oldCoded1) := by
    simpa [D, oldBody, step1, raw1, oldCoded1] using
      (BProv_ass (B := Ax_s) (G := D) (by simp [D, oldBody]))
  have hcodingRen : BProv Ax_s (G.map (rename Nat.succ))
      (rename Nat.succ
        (betaCodingStepTermAt (Term.succ raw)
          (Term.add oldCapacity newCoded) step)) :=
    BProv_rename_of_sentences
      (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
      hcoding Nat.succ
  have hcodingD : BProv Ax_s D
      (betaCodingStepTermAt (Term.succ raw1)
        (Term.add oldCapacity1 newCoded1) step1) := by
    have hraw := BProv_context_cons (B := Ax_s)
      (a := oldBody) hcodingRen
    simpa [D, step1, raw1, oldCapacity1, newCoded1,
      betaCodingStepTermAt, commonMultipleThroughTermAt,
      dvdTermTermAt, ltTermAt, leTermAt,
      rename, Term.rename, SetTheory.up, Term.rename_comp,
      Function.comp_def, Nat.add_assoc] using hraw
  have hadjoinRen : BProv Ax_s (G.map (rename Nat.succ))
      (rename Nat.succ
        (hfAdjoinGraphTermAt newCoded oldCoded oldCoded)) :=
    BProv_rename_of_sentences
      (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
      hadjoin Nat.succ
  have hadjoinD : BProv Ax_s D
      (hfAdjoinGraphTermAt newCoded1 oldCoded1 oldCoded1) := by
    have hraw := BProv_context_cons (B := Ax_s)
      (a := oldBody) hadjoinRen
    simpa [D, newCoded1, oldCoded1,
      rename_hfAdjoinGraphTermAt_succ] using hraw
  have hextExists : BProv Ax_s D
      (betaCodeExtensionExistsTermAt
        (Term.var 0) step1 (Term.succ raw1) newCoded1) :=
    BProv_Ax_s_betaCodeExtensionExistsTermAt_of_sum_capacity
      hcodingD
  refine BProv_Ax_s_betaCodeExtensionExistsTermAt_elim_opened
    (G := D) (oldCode := Term.var 0) (step := step1)
    (target := Term.succ raw1) (newOut := newCoded1)
    (goal := rename Nat.succ goal) ?_ hextExists
  let extensionBody : Formula :=
    betaCodeExtensionExistsTermAtBody
      (Term.var 0) step1 (Term.succ raw1) newCoded1
  let E : List Formula := extensionBody :: D.map (rename Nat.succ)
  let step2 : Term := Term.rename (fun n => n + 2) step
  let raw2 : Term := Term.rename (fun n => n + 2) raw
  let oldCoded2 : Term := Term.rename (fun n => n + 2) oldCoded
  let newCoded2 : Term := Term.rename (fun n => n + 2) newCoded
  have hextension : BProv Ax_s E
      (betaCodeExtensionTermAt
        (Term.var 1) step2 (Term.succ raw2) newCoded2
        (Term.var 0)) := by
    have hraw : BProv Ax_s E extensionBody :=
      BProv_ass (B := Ax_s) (G := E) (by simp [E])
    simpa [extensionBody, betaCodeExtensionExistsTermAtBody,
      step1, raw1, newCoded1, step2, raw2, newCoded2,
      Term.rename, Term.rename_comp, Function.comp_def,
      Nat.add_assoc] using hraw
  have holdBodyE : BProv Ax_s E
      (ordinalCodeGraphBodyTermAt
        (Term.var 1) step2 raw2 oldCoded2) := by
    have hraw : BProv Ax_s E (rename Nat.succ oldBody) :=
      BProv_ass (B := Ax_s) (G := E) (by simp [E, D])
    simpa [oldBody, step1, raw1, oldCoded1,
      step2, raw2, oldCoded2,
      rename_ordinalCodeGraphBodyTermAt,
      Term.rename, Term.rename_comp, Function.comp_def,
      Nat.add_assoc] using hraw
  have hadjoinDRen : BProv Ax_s (D.map (rename Nat.succ))
      (rename Nat.succ
        (hfAdjoinGraphTermAt newCoded1 oldCoded1 oldCoded1)) :=
    BProv_rename_of_sentences
      (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
      hadjoinD Nat.succ
  have hadjoinE : BProv Ax_s E
      (hfAdjoinGraphTermAt newCoded2 oldCoded2 oldCoded2) := by
    have hraw := BProv_context_cons (B := Ax_s)
      (a := extensionBody) hadjoinDRen
    simpa [E, newCoded1, oldCoded1, newCoded2, oldCoded2,
      rename_hfAdjoinGraphTermAt_succ,
      Term.rename, Term.rename_comp, Function.comp_def,
      Nat.add_assoc] using hraw
  have hnewBody : BProv Ax_s E
      (ordinalCodeGraphBodyTermAt
        (Term.var 0) step2 (Term.succ raw2) newCoded2) :=
    BProv_Ax_s_ordinalCodeGraphBodyTermAt_succ_of_extension
      holdBodyE hextension hadjoinE
  have hnewExists : BProv Ax_s E
      (ordinalCodeGraphBodyExistsTermAt
        step2 (Term.succ raw2) newCoded2) :=
    BProv_ordinalCodeGraphBodyExistsTermAt_of_term hnewBody
  simpa [goal, E, D, extensionBody,
    betaCodeExtensionExistsTermAtBody,
    rename_ordinalCodeGraphBodyExistsTermAt,
    Term.rename, Term.rename_comp, Function.comp_def,
    Nat.add_assoc] using hnewExists

theorem rename_betaCodingStepTermAt
    (r : Nat → Nat) (bound sourceCode step : Term) :
    rename r (betaCodingStepTermAt bound sourceCode step) =
      betaCodingStepTermAt
        (Term.rename r bound) (Term.rename r sourceCode)
        (Term.rename r step) := by
  simp [betaCodingStepTermAt, commonMultipleThroughTermAt,
    dvdTermTermAt, ltTermAt, leTermAt,
    rename, Term.rename, SetTheory.up, Term.rename_comp]

theorem rename_ordinalCodeTraceCapacityTermAt
    (r : Nat → Nat) (raw coded capacity : Term) :
    rename r
        (ordinalCodeTraceCapacityTermAt raw coded capacity) =
      ordinalCodeTraceCapacityTermAt
        (Term.rename r raw) (Term.rename r coded)
        (Term.rename r capacity) := by
  simp [ordinalCodeTraceCapacityTermAt,
    rename_betaCodingStepTermAt,
    rename_ordinalCodeGraphBodyExistsTermAt,
    rename, Term.rename, SetTheory.up, Term.rename_comp]

/-- Instantiate the capacity-parametric trace invariant at one certified
coding step. -/
theorem BProv_Ax_s_ordinalCodeTraceCapacityTermAt_trace_of_coding
    {G : List Formula} {raw coded capacity step : Term}
    (hcapacity : BProv Ax_s G
      (ordinalCodeTraceCapacityTermAt raw coded capacity))
    (hcoding : BProv Ax_s G
      (betaCodingStepTermAt raw capacity step)) :
    BProv Ax_s G
      (ordinalCodeGraphBodyExistsTermAt step raw coded) := by
  have hshift2 (t : Term) :
      Term.subst (Term.upSubst (Term.upSubst (instTerm step)))
          (Term.rename (fun n => n + 2) t) =
        Term.rename (fun n => n + 2)
          (Term.subst (instTerm step) t) := by
    change Term.subst (iterUpSubst 2 (instTerm step))
        (Term.rename (fun n => n + 2) t) =
      Term.rename (fun n => n + 2)
        (Term.subst (instTerm step) t)
    exact term_subst_iterUpSubst_rename_add 2 (instTerm step) t
  have himpRaw := BProv_allE (B := Ax_s) (G := G)
    (t := step) hcapacity
  have himp : BProv Ax_s G
      (imp
        (betaCodingStepTermAt raw capacity step)
        (ordinalCodeGraphBodyExistsTermAt step raw coded)) := by
    simpa [ordinalCodeTraceCapacityTermAt,
      subst_ordinalCodeGraphBodyExistsTermAt,
      betaCodingStepTermAt, commonMultipleThroughTermAt,
      dvdTermTermAt, ltTermAt, leTermAt,
      subst, instTerm, Term.subst, Term.upSubst,
      Term.subst_rename_succ_up,
      term_subst_instTerm_rename_succ,
      term_subst_instTerm_rename_two_succ,
      term_subst_upSubst_instTerm_rename_two_succ,
      term_subst_up_up_instTerm_rename_three_succ,
      Term.rename_comp, Function.comp_def, hshift2] using himpRaw
  exact BProv_mp Ax_s G _ _ himp hcoding

/-- The capacity-parametric trace invariant advances across one explicit
Ackermann-adjoin edge.  The successor capacity is the arithmetic sum of the
old majorant and the new endpoint. -/
theorem BProv_Ax_s_ordinalCodeTraceCapacityTermAt_succ
    {G : List Formula}
    {raw oldCoded newCoded oldCapacity : Term}
    (holdCapacity : BProv Ax_s G
      (ordinalCodeTraceCapacityTermAt
        raw oldCoded oldCapacity))
    (hadjoin : BProv Ax_s G
      (hfAdjoinGraphTermAt newCoded oldCoded oldCoded)) :
    BProv Ax_s G
      (ordinalCodeTraceCapacityTermAt
        (Term.succ raw) newCoded
        (Term.add oldCapacity newCoded)) := by
  let antecedent : Formula :=
    betaCodingStepTermAt
      (Term.succ (Term.rename Nat.succ raw))
      (Term.add
        (Term.rename Nat.succ oldCapacity)
        (Term.rename Nat.succ newCoded))
      (Term.var 0)
  let consequent : Formula :=
    ordinalCodeGraphBodyExistsTermAt
      (Term.var 0)
      (Term.succ (Term.rename Nat.succ raw))
      (Term.rename Nat.succ newCoded)
  let body : Formula := imp antecedent consequent
  have hbody : BProv Ax_s
      (antecedent :: G.map (rename Nat.succ)) consequent := by
    let C : List Formula := antecedent :: G.map (rename Nat.succ)
    let raw1 : Term := Term.rename Nat.succ raw
    let oldCoded1 : Term := Term.rename Nat.succ oldCoded
    let newCoded1 : Term := Term.rename Nat.succ newCoded
    let oldCapacity1 : Term := Term.rename Nat.succ oldCapacity
    have hcoding : BProv Ax_s C
        (betaCodingStepTermAt
          (Term.succ raw1)
          (Term.add oldCapacity1 newCoded1)
          (Term.var 0)) := by
      simpa [C, antecedent, raw1, oldCapacity1, newCoded1] using
        (BProv_ass (B := Ax_s) (G := C) (by simp [C, antecedent]))
    have holdCapacityRen : BProv Ax_s (G.map (rename Nat.succ))
        (rename Nat.succ
          (ordinalCodeTraceCapacityTermAt
            raw oldCoded oldCapacity)) :=
      BProv_rename_of_sentences
        (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
        holdCapacity Nat.succ
    have holdCapacityC : BProv Ax_s C
        (ordinalCodeTraceCapacityTermAt
          raw1 oldCoded1 oldCapacity1) := by
      have hraw := BProv_context_cons (B := Ax_s)
        (a := antecedent) holdCapacityRen
      simpa [C, raw1, oldCoded1, oldCapacity1,
        rename_ordinalCodeTraceCapacityTermAt] using hraw
    have hadjoinRen : BProv Ax_s (G.map (rename Nat.succ))
        (rename Nat.succ
          (hfAdjoinGraphTermAt newCoded oldCoded oldCoded)) :=
      BProv_rename_of_sentences
        (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
        hadjoin Nat.succ
    have hadjoinC : BProv Ax_s C
        (hfAdjoinGraphTermAt newCoded1 oldCoded1 oldCoded1) := by
      have hraw := BProv_context_cons (B := Ax_s)
        (a := antecedent) hadjoinRen
      simpa [C, newCoded1, oldCoded1,
        rename_hfAdjoinGraphTermAt_succ] using hraw
    have holdCoding : BProv Ax_s C
        (betaCodingStepTermAt raw1 oldCapacity1 (Term.var 0)) :=
      BProv_Ax_s_betaCodingStepTermAt_old_of_sum_capacity
        hcoding
    have holdTrace : BProv Ax_s C
        (ordinalCodeGraphBodyExistsTermAt
          (Term.var 0) raw1 oldCoded1) :=
      BProv_Ax_s_ordinalCodeTraceCapacityTermAt_trace_of_coding
        holdCapacityC holdCoding
    have hnewTrace : BProv Ax_s C
        (ordinalCodeGraphBodyExistsTermAt
          (Term.var 0) (Term.succ raw1) newCoded1) :=
      BProv_Ax_s_ordinalCodeGraphBodyExistsTermAt_succ_of_sum_capacity
        holdTrace hcoding hadjoinC
    simpa [C, consequent, raw1, newCoded1] using hnewTrace
  have himp : BProv Ax_s (G.map (rename Nat.succ)) body := by
    simpa [body] using BProv_impI hbody
  have hall : BProv Ax_s G (all body) :=
    BProv_allI_of_sentences (B := Ax_s)
      (fun f hf => sentence_ax_s (f := f) hf) himp
  simpa [ordinalCodeTraceCapacityTermAt,
    body, antecedent, consequent, Term.rename] using hall

/-! ### Atomic equality through ordinal codes -/

/-- Binder-free equality comparison through a common ordinal-code witness. -/
def codeEqualityBodyTermAt
    (leftCode rightCode leftRaw rightRaw : Term) : Formula :=
  and
    (ordinalCodeGraphTermAt leftRaw leftCode)
    (and
      (ordinalCodeGraphTermAt rightRaw rightCode)
      (eq leftCode rightCode))

/-- Relational equality obtained by evaluating both raw terms into coded
finite ordinals and comparing those codes. -/
def codeEqualityTermAt (leftRaw rightRaw : Term) : Formula :=
  ex (ex
    (codeEqualityBodyTermAt
      (Term.var 1) (Term.var 0)
      (Term.rename (fun n ↦ n+2) leftRaw)
      (Term.rename (fun n ↦ n+2) rightRaw)))

theorem subst_codeEqualityBodyTermAt
    (sigma : Nat → Term)
    (leftCode rightCode leftRaw rightRaw : Term) :
    subst sigma
        (codeEqualityBodyTermAt
          leftCode rightCode leftRaw rightRaw) =
      codeEqualityBodyTermAt
        (Term.subst sigma leftCode)
        (Term.subst sigma rightCode)
        (Term.subst sigma leftRaw)
        (Term.subst sigma rightRaw) := by
  simp [codeEqualityBodyTermAt,
    subst_ordinalCodeGraphTermAt, subst]

theorem subst_codeEqualityTermAt
    (sigma : Nat → Term) (leftRaw rightRaw : Term) :
    subst sigma (codeEqualityTermAt leftRaw rightRaw) =
      codeEqualityTermAt
        (Term.subst sigma leftRaw)
        (Term.subst sigma rightRaw) := by
  have hshift2 (t : Term) :
      Term.subst (Term.upSubst (Term.upSubst sigma))
          (Term.rename (fun n ↦ n+2) t) =
        Term.rename (fun n ↦ n+2) (Term.subst sigma t) := by
    change Term.subst (iterUpSubst 2 sigma)
        (Term.rename (fun n ↦ n+2) t) =
      Term.rename (fun n ↦ n+2) (Term.subst sigma t)
    exact term_subst_iterUpSubst_rename_add 2 sigma t
  simp [codeEqualityTermAt,
    subst_codeEqualityBodyTermAt,
    subst, Term.subst, Term.upSubst, Term.rename, hshift2]

theorem rename_codeEqualityTermAt
    (r : Nat → Nat) (leftRaw rightRaw : Term) :
    rename r (codeEqualityTermAt leftRaw rightRaw) =
      codeEqualityTermAt
        (Term.rename r leftRaw) (Term.rename r rightRaw) := by
  rw [← subst_var_rename, subst_codeEqualityTermAt]
  simp only [term_subst_var_rename]

theorem subst_instTerm_codeEqualityBody_inner
    (leftCode rightCode leftRaw rightRaw : Term) :
    subst (instTerm rightCode)
        (codeEqualityBodyTermAt
          (Term.rename Nat.succ leftCode)
          (Term.var 0)
          (Term.rename Nat.succ leftRaw)
          (Term.rename Nat.succ rightRaw)) =
      codeEqualityBodyTermAt
        leftCode rightCode leftRaw rightRaw := by
  rw [subst_codeEqualityBodyTermAt]
  simp [instTerm, Term.subst, term_subst_instTerm_rename_succ]

theorem subst_instTerm_codeEqualityBody_outer
    (leftCode leftRaw rightRaw : Term) :
    subst (instTerm leftCode)
        (ex (codeEqualityBodyTermAt
          (Term.var 1) (Term.var 0)
          (Term.rename (fun n ↦ n+2) leftRaw)
          (Term.rename (fun n ↦ n+2) rightRaw))) =
      ex (codeEqualityBodyTermAt
        (Term.rename Nat.succ leftCode) (Term.var 0)
        (Term.rename Nat.succ leftRaw)
        (Term.rename Nat.succ rightRaw)) := by
  simp only [subst, subst_codeEqualityBodyTermAt]
  simp [instTerm, Term.subst, Term.upSubst,
    term_subst_upSubst_instTerm_rename_two_succ]

/-- Package two explicit code witnesses and their equality into relational
equality. -/
theorem BProv_codeEqualityTermAt_of_components
    {B : Formula → Prop} {G : List Formula}
    {leftCode rightCode leftRaw rightRaw : Term}
    (hleft : BProv B G
      (ordinalCodeGraphTermAt leftRaw leftCode))
    (hright : BProv B G
      (ordinalCodeGraphTermAt rightRaw rightCode))
    (heq : BProv B G (eq leftCode rightCode)) :
    BProv B G (codeEqualityTermAt leftRaw rightRaw) := by
  have hbody : BProv B G
      (codeEqualityBodyTermAt
        leftCode rightCode leftRaw rightRaw) := by
    simpa [codeEqualityBodyTermAt] using
      BProv_andI hleft (BProv_andI hright heq)
  have hinnerInst : BProv B G
      (subst (instTerm rightCode)
        (codeEqualityBodyTermAt
          (Term.rename Nat.succ leftCode)
          (Term.var 0)
          (Term.rename Nat.succ leftRaw)
          (Term.rename Nat.succ rightRaw))) := by
    rw [subst_instTerm_codeEqualityBody_inner]
    exact hbody
  have hinner : BProv B G
      (ex (codeEqualityBodyTermAt
        (Term.rename Nat.succ leftCode) (Term.var 0)
        (Term.rename Nat.succ leftRaw)
        (Term.rename Nat.succ rightRaw))) :=
    BProv_exI hinnerInst
  have houterInst : BProv B G
      (subst (instTerm leftCode)
        (ex (codeEqualityBodyTermAt
          (Term.var 1) (Term.var 0)
          (Term.rename (fun n ↦ n+2) leftRaw)
          (Term.rename (fun n ↦ n+2) rightRaw)))) := by
    rw [subst_instTerm_codeEqualityBody_outer]
    exact hinner
  simpa [codeEqualityTermAt] using
    (BProv_exI houterInst)

/-- Equality transport in the raw argument of the ordinal-code graph. -/
theorem BProv_ordinalCodeGraphTermAt_congr_raw
    {B : Formula → Prop} {G : List Formula}
    {leftRaw rightRaw coded : Term}
    (heq : BProv B G (eq leftRaw rightRaw))
    (hleft : BProv B G
      (ordinalCodeGraphTermAt leftRaw coded)) :
    BProv B G (ordinalCodeGraphTermAt rightRaw coded) := by
  let context : Formula :=
    ordinalCodeGraphTermAt
      (Term.var 0) (Term.rename Nat.succ coded)
  have hleftInst : BProv B G
      (subst (instTerm leftRaw) context) := by
    simpa [context, subst_ordinalCodeGraphTermAt,
      instTerm, Term.subst,
      term_subst_instTerm_rename_succ] using hleft
  have hrightInst := BProv_eqElim (B := B) (G := G)
    (a := context) heq hleftInst
  simpa [context, subst_ordinalCodeGraphTermAt,
    instTerm, Term.subst,
    term_subst_instTerm_rename_succ] using hrightInst

/-- Equality transport in the coded argument of the ordinal-code graph. -/
theorem BProv_ordinalCodeGraphTermAt_congr_coded
    {B : Formula → Prop} {G : List Formula}
    {raw leftCode rightCode : Term}
    (heq : BProv B G (eq leftCode rightCode))
    (hleft : BProv B G
      (ordinalCodeGraphTermAt raw leftCode)) :
    BProv B G (ordinalCodeGraphTermAt raw rightCode) := by
  let context : Formula :=
    ordinalCodeGraphTermAt
      (Term.rename Nat.succ raw) (Term.var 0)
  have hleftInst : BProv B G
      (subst (instTerm leftCode) context) := by
    simpa [context, subst_ordinalCodeGraphTermAt,
      instTerm, Term.subst,
      term_subst_instTerm_rename_succ] using hleft
  have hrightInst := BProv_eqElim (B := B) (G := G)
    (a := context) heq hleftInst
  simpa [context, subst_ordinalCodeGraphTermAt,
    instTerm, Term.subst,
    term_subst_instTerm_rename_succ] using hrightInst

/-- Totality of the ordinal-code graph turns equality of raw terms into
relational equality of their codes. -/
theorem BProv_codeEqualityTermAt_of_eq
    (P : OrdinalCodeGraphProofs)
    {G : List Formula} {leftRaw rightRaw : Term}
    (heq : BProv Ax_s G (eq leftRaw rightRaw)) :
    BProv Ax_s G
      (codeEqualityTermAt leftRaw rightRaw) := by
  let graphBody : Formula :=
    ordinalCodeGraphTermAt
      (Term.rename Nat.succ leftRaw) (Term.var 0)
  have htotal : BProv Ax_s G (ex graphBody) := by
    simpa [graphBody] using P.total G leftRaw
  have hbody : BProv Ax_s
      (graphBody :: G.map (rename Nat.succ))
      (rename Nat.succ
        (codeEqualityTermAt leftRaw rightRaw)) := by
    let C : List Formula := graphBody :: G.map (rename Nat.succ)
    have hleft : BProv Ax_s C
        (ordinalCodeGraphTermAt
          (Term.rename Nat.succ leftRaw) (Term.var 0)) := by
      exact BProv_ass (B := Ax_s) (G := C) (by simp [C, graphBody])
    have heqShift : BProv Ax_s C
        (eq (Term.rename Nat.succ leftRaw)
          (Term.rename Nat.succ rightRaw)) := by
      simpa [C, rename, Term.rename] using
        (BProv_rename_succ_context_cons_of_sentences
          (B := Ax_s) (fun f hf ↦ sentence_ax_s (f := f) hf)
          (a := graphBody) heq)
    have hright : BProv Ax_s C
        (ordinalCodeGraphTermAt
          (Term.rename Nat.succ rightRaw) (Term.var 0)) :=
      BProv_ordinalCodeGraphTermAt_congr_raw heqShift hleft
    have hcodes : BProv Ax_s C
        (codeEqualityTermAt
          (Term.rename Nat.succ leftRaw)
          (Term.rename Nat.succ rightRaw)) :=
      BProv_codeEqualityTermAt_of_components
        hleft hright (BProv_eqRefl (Term.var 0))
    simpa [C, rename_codeEqualityTermAt] using hcodes
  exact BProv_exE_of_sentences (B := Ax_s)
    (fun f hf ↦ sentence_ax_s (f := f) hf)
    (a := graphBody)
    (c := codeEqualityTermAt leftRaw rightRaw)
    htotal hbody

/-- Injectivity of the ordinal-code graph recovers equality of raw terms from
relational equality of their codes. -/
theorem BProv_eq_of_codeEqualityTermAt
    (P : OrdinalCodeGraphProofs)
    {G : List Formula} {leftRaw rightRaw : Term}
    (hcodes : BProv Ax_s G
      (codeEqualityTermAt leftRaw rightRaw)) :
    BProv Ax_s G (eq leftRaw rightRaw) := by
  let body : Formula :=
    codeEqualityBodyTermAt
      (Term.var 1) (Term.var 0)
      (Term.rename (fun n ↦ n+2) leftRaw)
      (Term.rename (fun n ↦ n+2) rightRaw)
  let inner : Formula := ex body
  have houter : BProv Ax_s G (ex inner) := by
    simpa [codeEqualityTermAt, inner, body] using hcodes
  have houterBody : BProv Ax_s
      (inner :: G.map (rename Nat.succ))
      (rename Nat.succ (eq leftRaw rightRaw)) := by
    let G₁ : List Formula := inner :: G.map (rename Nat.succ)
    have hinner : BProv Ax_s G₁ (ex body) :=
      BProv_ass (B := Ax_s) (G := G₁) (by simp [G₁, inner])
    have hinnerBody : BProv Ax_s
        (body :: G₁.map (rename Nat.succ))
        (rename Nat.succ (rename Nat.succ
          (eq leftRaw rightRaw))) := by
      let C : List Formula := body :: G₁.map (rename Nat.succ)
      have hpacked : BProv Ax_s C body :=
        BProv_ass (B := Ax_s) (G := C) (by simp [C])
      have hleft : BProv Ax_s C
          (ordinalCodeGraphTermAt
            (Term.rename (fun n ↦ n+2) leftRaw)
            (Term.var 1)) := by
        simpa [body, codeEqualityBodyTermAt] using
          BProv_andE1 hpacked
      have hrightAndEq : BProv Ax_s C
          (and
            (ordinalCodeGraphTermAt
              (Term.rename (fun n ↦ n+2) rightRaw)
              (Term.var 0))
            (eq (Term.var 1) (Term.var 0))) := by
        simpa [body, codeEqualityBodyTermAt] using
          BProv_andE2 hpacked
      have hright : BProv Ax_s C
          (ordinalCodeGraphTermAt
            (Term.rename (fun n ↦ n+2) rightRaw)
            (Term.var 0)) :=
        BProv_andE1 hrightAndEq
      have heqCode : BProv Ax_s C
          (eq (Term.var 1) (Term.var 0)) :=
        BProv_andE2 hrightAndEq
      have hleftAtRightCode : BProv Ax_s C
          (ordinalCodeGraphTermAt
            (Term.rename (fun n ↦ n+2) leftRaw)
            (Term.var 0)) :=
        BProv_ordinalCodeGraphTermAt_congr_coded
          heqCode hleft
      have hraw : BProv Ax_s C
          (eq
            (Term.rename (fun n ↦ n+2) leftRaw)
            (Term.rename (fun n ↦ n+2) rightRaw)) :=
        P.injective hleftAtRightCode hright
      simpa [C, rename, Term.rename, Term.rename_comp,
        Function.comp_def] using hraw
    exact BProv_exE_of_sentences (B := Ax_s)
      (fun f hf ↦ sentence_ax_s (f := f) hf)
      (a := body) (c := rename Nat.succ (eq leftRaw rightRaw))
      hinner hinnerBody
  exact BProv_exE_of_sentences (B := Ax_s)
    (fun f hf ↦ sentence_ax_s (f := f) hf)
    (a := inner) (c := eq leftRaw rightRaw)
    houter houterBody

/-- Raw equality is equivalent in PA to equality through existentially chosen
ordinal codes.  The forward direction uses graph totality; the reverse direction
uses graph injectivity. -/
theorem BProv_eq_iff_codeEqualityTermAt
    (P : OrdinalCodeGraphProofs)
    (G : List Formula) (leftRaw rightRaw : Term) :
    BProv Ax_s G
      (iffForm
        (eq leftRaw rightRaw)
        (codeEqualityTermAt leftRaw rightRaw)) := by
  have hforward : BProv Ax_s G
      (imp
        (eq leftRaw rightRaw)
        (codeEqualityTermAt leftRaw rightRaw)) := by
    apply BProv_impI
    exact BProv_codeEqualityTermAt_of_eq P
      (BProv_ass (B := Ax_s)
        (G := eq leftRaw rightRaw :: G) (by simp))
  have hreverse : BProv Ax_s G
      (imp
        (codeEqualityTermAt leftRaw rightRaw)
        (eq leftRaw rightRaw)) := by
    apply BProv_impI
    exact BProv_eq_of_codeEqualityTermAt P
      (BProv_ass (B := Ax_s)
        (G := codeEqualityTermAt leftRaw rightRaw :: G)
        (by simp))
  simpa [iffForm] using BProv_andI hforward hreverse

/-! ### Equivalence calculus for the structural round trip -/

theorem BProv_iffForm_refl
    {B : Formula → Prop} {G : List Formula} (a : Formula) :
    BProv B G (iffForm a a) := by
  have haa : BProv B G (imp a a) :=
    BProv_impI (BProv_ass (B := B) (G := a :: G) (by simp))
  simpa [iffForm] using BProv_andI haa haa

theorem BProv_iffForm_symm
    {B : Formula → Prop} {G : List Formula} {a b : Formula}
    (h : BProv B G (iffForm a b)) :
    BProv B G (iffForm b a) := by
  have hab : BProv B G (imp a b) := by
    simpa [iffForm] using BProv_andE1 h
  have hba : BProv B G (imp b a) := by
    simpa [iffForm] using BProv_andE2 h
  simpa [iffForm] using BProv_andI hba hab

theorem BProv_iffForm_trans
    {B : Formula → Prop} {G : List Formula} {a b c : Formula}
    (hab : BProv B G (iffForm a b))
    (hbc : BProv B G (iffForm b c)) :
    BProv B G (iffForm a c) := by
  have habForward : BProv B G (imp a b) := by
    simpa [iffForm] using BProv_andE1 hab
  have habReverse : BProv B G (imp b a) := by
    simpa [iffForm] using BProv_andE2 hab
  have hbcForward : BProv B G (imp b c) := by
    simpa [iffForm] using BProv_andE1 hbc
  have hbcReverse : BProv B G (imp c b) := by
    simpa [iffForm] using BProv_andE2 hbc
  have hac : BProv B G (imp a c) := by
    apply BProv_impI
    have ha : BProv B (a :: G) a :=
      BProv_ass (B := B) (G := a :: G) (by simp)
    have hb : BProv B (a :: G) b :=
      BProv_mp B (a :: G) a b
        (BProv_context_cons habForward) ha
    exact BProv_mp B (a :: G) b c
      (BProv_context_cons hbcForward) hb
  have hca : BProv B G (imp c a) := by
    apply BProv_impI
    have hc : BProv B (c :: G) c :=
      BProv_ass (B := B) (G := c :: G) (by simp)
    have hb : BProv B (c :: G) b :=
      BProv_mp B (c :: G) c b
        (BProv_context_cons hbcReverse) hc
    exact BProv_mp B (c :: G) b a
      (BProv_context_cons habReverse) hb
  simpa [iffForm] using BProv_andI hac hca

theorem BProv_iffForm_imp_congr
    {B : Formula → Prop} {G : List Formula}
    {a a' b b' : Formula}
    (ha : BProv B G (iffForm a a'))
    (hb : BProv B G (iffForm b b')) :
    BProv B G (iffForm (imp a b) (imp a' b')) := by
  have haa' : BProv B G (imp a a') := by
    simpa [iffForm] using BProv_andE1 ha
  have ha'a : BProv B G (imp a' a) := by
    simpa [iffForm] using BProv_andE2 ha
  have hbb' : BProv B G (imp b b') := by
    simpa [iffForm] using BProv_andE1 hb
  have hb'b : BProv B G (imp b' b) := by
    simpa [iffForm] using BProv_andE2 hb
  have hforward : BProv B G (imp (imp a b) (imp a' b')) := by
    apply BProv_impI
    apply BProv_impI
    let C : List Formula := a' :: imp a b :: G
    have ha'C : BProv B C a' :=
      BProv_ass (B := B) (G := C) (by simp [C])
    have haC : BProv B C a :=
      BProv_mp B C a' a
        (BProv_context_cons (BProv_context_cons ha'a)) ha'C
    have habC : BProv B C (imp a b) :=
      BProv_ass (B := B) (G := C) (by simp [C])
    have hbC : BProv B C b := BProv_mp B C a b habC haC
    exact BProv_mp B C b b'
      (BProv_context_cons (BProv_context_cons hbb')) hbC
  have hreverse : BProv B G (imp (imp a' b') (imp a b)) := by
    apply BProv_impI
    apply BProv_impI
    let C : List Formula := a :: imp a' b' :: G
    have haC : BProv B C a :=
      BProv_ass (B := B) (G := C) (by simp [C])
    have ha'C : BProv B C a' :=
      BProv_mp B C a a'
        (BProv_context_cons (BProv_context_cons haa')) haC
    have ha'b'C : BProv B C (imp a' b') :=
      BProv_ass (B := B) (G := C) (by simp [C])
    have hb'C : BProv B C b' := BProv_mp B C a' b' ha'b'C ha'C
    exact BProv_mp B C b' b
      (BProv_context_cons (BProv_context_cons hb'b)) hb'C
  simpa [iffForm] using BProv_andI hforward hreverse

theorem BProv_iffForm_and_congr
    {B : Formula → Prop} {G : List Formula}
    {a a' b b' : Formula}
    (ha : BProv B G (iffForm a a'))
    (hb : BProv B G (iffForm b b')) :
    BProv B G (iffForm (and a b) (and a' b')) := by
  have haa' : BProv B G (imp a a') := by
    simpa [iffForm] using BProv_andE1 ha
  have ha'a : BProv B G (imp a' a) := by
    simpa [iffForm] using BProv_andE2 ha
  have hbb' : BProv B G (imp b b') := by
    simpa [iffForm] using BProv_andE1 hb
  have hb'b : BProv B G (imp b' b) := by
    simpa [iffForm] using BProv_andE2 hb
  have hforward : BProv B G (imp (and a b) (and a' b')) := by
    apply BProv_impI
    let C : List Formula := and a b :: G
    have hp : BProv B C (and a b) :=
      BProv_ass (B := B) (G := C) (by simp [C])
    have haC : BProv B C a := BProv_andE1 hp
    have hbC : BProv B C b := BProv_andE2 hp
    have ha'C : BProv B C a' :=
      BProv_mp B C a a' (BProv_context_cons haa') haC
    have hb'C : BProv B C b' :=
      BProv_mp B C b b' (BProv_context_cons hbb') hbC
    exact BProv_andI ha'C hb'C
  have hreverse : BProv B G (imp (and a' b') (and a b)) := by
    apply BProv_impI
    let C : List Formula := and a' b' :: G
    have hp : BProv B C (and a' b') :=
      BProv_ass (B := B) (G := C) (by simp [C])
    have ha'C : BProv B C a' := BProv_andE1 hp
    have hb'C : BProv B C b' := BProv_andE2 hp
    have haC : BProv B C a :=
      BProv_mp B C a' a (BProv_context_cons ha'a) ha'C
    have hbC : BProv B C b :=
      BProv_mp B C b' b (BProv_context_cons hb'b) hb'C
    exact BProv_andI haC hbC
  simpa [iffForm] using BProv_andI hforward hreverse

theorem BProv_iffForm_or_congr
    {B : Formula → Prop} {G : List Formula}
    {a a' b b' : Formula}
    (ha : BProv B G (iffForm a a'))
    (hb : BProv B G (iffForm b b')) :
    BProv B G (iffForm (or a b) (or a' b')) := by
  have haa' : BProv B G (imp a a') := by
    simpa [iffForm] using BProv_andE1 ha
  have ha'a : BProv B G (imp a' a) := by
    simpa [iffForm] using BProv_andE2 ha
  have hbb' : BProv B G (imp b b') := by
    simpa [iffForm] using BProv_andE1 hb
  have hb'b : BProv B G (imp b' b) := by
    simpa [iffForm] using BProv_andE2 hb
  have hforward : BProv B G (imp (or a b) (or a' b')) := by
    apply BProv_impI
    let C : List Formula := or a b :: G
    have hor : BProv B C (or a b) :=
      BProv_ass (B := B) (G := C) (by simp [C])
    have hleft : BProv B (a :: C) (or a' b') := by
      have haC : BProv B (a :: C) a :=
        BProv_ass (B := B) (G := a :: C) (by simp)
      exact BProv_orI1
        (BProv_mp B (a :: C) a a'
          (BProv_context_cons
            (BProv_context_cons haa')) haC)
    have hright : BProv B (b :: C) (or a' b') := by
      have hbC : BProv B (b :: C) b :=
        BProv_ass (B := B) (G := b :: C) (by simp)
      exact BProv_orI2
        (BProv_mp B (b :: C) b b'
          (BProv_context_cons
            (BProv_context_cons hbb')) hbC)
    exact BProv_orE hor hleft hright
  have hreverse : BProv B G (imp (or a' b') (or a b)) := by
    apply BProv_impI
    let C : List Formula := or a' b' :: G
    have hor : BProv B C (or a' b') :=
      BProv_ass (B := B) (G := C) (by simp [C])
    have hleft : BProv B (a' :: C) (or a b) := by
      have ha'C : BProv B (a' :: C) a' :=
        BProv_ass (B := B) (G := a' :: C) (by simp)
      exact BProv_orI1
        (BProv_mp B (a' :: C) a' a
          (BProv_context_cons
            (BProv_context_cons ha'a)) ha'C)
    have hright : BProv B (b' :: C) (or a b) := by
      have hb'C : BProv B (b' :: C) b' :=
        BProv_ass (B := B) (G := b' :: C) (by simp)
      exact BProv_orI2
        (BProv_mp B (b' :: C) b' b
          (BProv_context_cons
            (BProv_context_cons hb'b)) hb'C)
    exact BProv_orE hor hleft hright
  simpa [iffForm] using BProv_andI hforward hreverse

theorem BProv_iffForm_ex_congr_of_sentences
    {B : Formula → Prop} (hB : Sentences B)
    {G : List Formula} {a b : Formula}
    (h : BProv B (G.map (rename Nat.succ)) (iffForm a b)) :
    BProv B G (iffForm (ex a) (ex b)) := by
  have hab : BProv B (G.map (rename Nat.succ)) (imp a b) := by
    simpa [iffForm] using BProv_andE1 h
  have hba : BProv B (G.map (rename Nat.succ)) (imp b a) := by
    simpa [iffForm] using BProv_andE2 h
  have hforward : BProv B G (imp (ex a) (ex b)) := by
    apply BProv_impI
    let C : List Formula := ex a :: G
    have hexa : BProv B C (ex a) :=
      BProv_ass (B := B) (G := C) (by simp [C])
    refine BProv_exE_of_sentences hB hexa ?_
    let D : List Formula := a :: C.map (rename Nat.succ)
    have ha : BProv B D a :=
      BProv_ass (B := B) (G := D) (by simp [D])
    have habD : BProv B D (imp a b) := by
      have hctx := BProv_context_cons (B := B) (a := a)
        (BProv_context_cons (B := B)
          (a := rename Nat.succ (ex a)) hab)
      simpa [D, C] using hctx
    have hb : BProv B D b := BProv_mp B D a b habD ha
    have hinst : BProv B D
        (subst (instTerm (Term.var 0))
          (rename (SetTheory.up Nat.succ) b)) := by
      simpa [subst_instTerm_var_zero_rename_up_succ] using hb
    have hex : BProv B D
        (ex (rename (SetTheory.up Nat.succ) b)) :=
      BProv_exI hinst
    simpa [D, C, rename] using hex
  have hreverse : BProv B G (imp (ex b) (ex a)) := by
    apply BProv_impI
    let C : List Formula := ex b :: G
    have hexb : BProv B C (ex b) :=
      BProv_ass (B := B) (G := C) (by simp [C])
    refine BProv_exE_of_sentences hB hexb ?_
    let D : List Formula := b :: C.map (rename Nat.succ)
    have hb : BProv B D b :=
      BProv_ass (B := B) (G := D) (by simp [D])
    have hbaD : BProv B D (imp b a) := by
      have hctx := BProv_context_cons (B := B) (a := b)
        (BProv_context_cons (B := B)
          (a := rename Nat.succ (ex b)) hba)
      simpa [D, C] using hctx
    have ha : BProv B D a := BProv_mp B D b a hbaD hb
    have hinst : BProv B D
        (subst (instTerm (Term.var 0))
          (rename (SetTheory.up Nat.succ) a)) := by
      simpa [subst_instTerm_var_zero_rename_up_succ] using ha
    have hex : BProv B D
        (ex (rename (SetTheory.up Nat.succ) a)) :=
      BProv_exI hinst
    simpa [D, C, rename] using hex
  simpa [iffForm] using BProv_andI hforward hreverse

theorem BProv_iffForm_all_congr_of_sentences
    {B : Formula → Prop} (hB : Sentences B)
    {G : List Formula} {a b : Formula}
    (h : BProv B (G.map (rename Nat.succ)) (iffForm a b)) :
    BProv B G (iffForm (all a) (all b)) := by
  have hab : BProv B (G.map (rename Nat.succ)) (imp a b) := by
    simpa [iffForm] using BProv_andE1 h
  have hba : BProv B (G.map (rename Nat.succ)) (imp b a) := by
    simpa [iffForm] using BProv_andE2 h
  have hforward : BProv B G (imp (all a) (all b)) := by
    apply BProv_impI
    let C : List Formula := all a :: G
    apply BProv_allI_of_sentences hB
    let D : List Formula := C.map (rename Nat.succ)
    have halla : BProv B C (all a) :=
      BProv_ass (B := B) (G := C) (by simp [C])
    have hallaRen : BProv B D (rename Nat.succ (all a)) := by
      simpa [D] using BProv_rename_of_sentences hB halla Nat.succ
    have hainst := BProv_allE (B := B) (G := D)
      (t := Term.var 0) hallaRen
    have ha : BProv B D a := by
      simpa [rename, subst_instTerm_var_zero_rename_up_succ] using hainst
    have habD : BProv B D (imp a b) := by
      have hctx := BProv_context_cons (B := B)
        (a := rename Nat.succ (all a)) hab
      simpa [D, C] using hctx
    exact BProv_mp B D a b habD ha
  have hreverse : BProv B G (imp (all b) (all a)) := by
    apply BProv_impI
    let C : List Formula := all b :: G
    apply BProv_allI_of_sentences hB
    let D : List Formula := C.map (rename Nat.succ)
    have hallb : BProv B C (all b) :=
      BProv_ass (B := B) (G := C) (by simp [C])
    have hallbRen : BProv B D (rename Nat.succ (all b)) := by
      simpa [D] using BProv_rename_of_sentences hB hallb Nat.succ
    have hbinst := BProv_allE (B := B) (G := D)
      (t := Term.var 0) hallbRen
    have hb : BProv B D b := by
      simpa [rename, subst_instTerm_var_zero_rename_up_succ] using hbinst
    have hbaD : BProv B D (imp b a) := by
      have hctx := BProv_context_cons (B := B)
        (a := rename Nat.succ (all b)) hba
      simpa [D, C] using hctx
    exact BProv_mp B D b a hbaD hb
  simpa [iffForm] using BProv_andI hforward hreverse

/-! ### Composite equality atoms -/

/-- Normal form of a reverse-translated equality atom after opening its two
term-value witnesses. -/
def paCompositeEqBodyAt
    (codedMap : Nat → Nat) (left right : Term) : Formula :=
  and
    (compositeTermGraphAt 1 (fun n ↦ codedMap n + 2) left)
    (and
      (compositeTermGraphAt 0 (fun n ↦ codedMap n + 2) right)
      (eq (Term.var 1) (Term.var 0)))

theorem hfFormulaAt_termGraph_left_eq_composite
    (codedMap : Nat → Nat) (t : Term) :
    hfFormulaAt (hfUpVarMap (hfUpVarMap codedMap))
        (AckermannHF.PAInHF.termGraphAt (fun n ↦ n+2) 1 t) =
      compositeTermGraphAt 1 (fun n ↦ codedMap n + 2) t := by
  let graph : Form :=
    AckermannHF.PAInHF.termGraphAt (fun n ↦ n+1) 0 t
  have hgraph : SetTheory.rename Nat.succ graph =
      AckermannHF.PAInHF.termGraphAt (fun n ↦ n+2) 1 t := by
    simpa [graph] using
      (AckermannHF.PAInHF.termGraphAt_rename t
        (ρ := fun n ↦ n+1) (out := 0) (r := Nat.succ))
  rw [← hgraph]
  rw [hfFormulaAt_source_rename]
  apply hfFormulaAt_ext
  intro n
  cases n <;> rfl

theorem hfFormulaAt_termGraph_right_eq_composite
    (codedMap : Nat → Nat) (t : Term) :
    hfFormulaAt (hfUpVarMap (hfUpVarMap codedMap))
        (AckermannHF.PAInHF.termGraphAt (fun n ↦ n+2) 0 t) =
      compositeTermGraphAt 0 (fun n ↦ codedMap n + 2) t := by
  let graph : Form :=
    AckermannHF.PAInHF.termGraphAt (fun n ↦ n+1) 0 t
  have hgraph : SetTheory.rename (SetTheory.up Nat.succ) graph =
      AckermannHF.PAInHF.termGraphAt (fun n ↦ n+2) 0 t := by
    simpa [graph, SetTheory.up] using
      (AckermannHF.PAInHF.termGraphAt_rename t
        (ρ := fun n ↦ n+1) (out := 0)
        (r := SetTheory.up Nat.succ))
  rw [← hgraph]
  rw [hfFormulaAt_source_rename]
  apply hfFormulaAt_ext
  intro n
  cases n <;> rfl

theorem paCompositeAt_eq_normalForm
    (codedMap : Nat → Nat) (left right : Term) :
    paCompositeAt codedMap (eq left right) =
      ex (ex (paCompositeEqBodyAt codedMap left right)) := by
  simp [paCompositeAt, paCompositeEqBodyAt,
    AckermannHF.PAInHF.formulaAt, hfFormulaAt,
    hfUpVarMap,
    hfFormulaAt_termGraph_left_eq_composite,
    hfFormulaAt_termGraph_right_eq_composite]

theorem BProv_paCompositeAt_eq_iff_codeEqualityTermAt_of_termGraphs
    {G : List Formula} {left right rawLeft rawRight : Term}
    {codedMap : Nat → Nat}
    (hleft : BProv Ax_s
      ((G.map (rename Nat.succ)).map (rename Nat.succ))
      (iffForm
        (compositeTermGraphAt 1 (fun n ↦ codedMap n + 2) left)
        (ordinalCodeGraphTermAt
          (Term.rename (fun n ↦ n+2) rawLeft) (Term.var 1))))
    (hright : BProv Ax_s
      ((G.map (rename Nat.succ)).map (rename Nat.succ))
      (iffForm
        (compositeTermGraphAt 0 (fun n ↦ codedMap n + 2) right)
        (ordinalCodeGraphTermAt
          (Term.rename (fun n ↦ n+2) rawRight) (Term.var 0)))) :
    BProv Ax_s G
      (iffForm
        (paCompositeAt codedMap (eq left right))
        (codeEqualityTermAt rawLeft rawRight)) := by
  let G₂ : List Formula :=
    (G.map (rename Nat.succ)).map (rename Nat.succ)
  have heq : BProv Ax_s G₂
      (iffForm
        (eq (Term.var 1) (Term.var 0))
        (eq (Term.var 1) (Term.var 0))) :=
    BProv_iffForm_refl (eq (Term.var 1) (Term.var 0))
  have hbody : BProv Ax_s G₂
      (iffForm
        (paCompositeEqBodyAt codedMap left right)
        (codeEqualityBodyTermAt
          (Term.var 1) (Term.var 0)
          (Term.rename (fun n ↦ n+2) rawLeft)
          (Term.rename (fun n ↦ n+2) rawRight))) := by
    have hp := BProv_iffForm_and_congr hright heq
    have h := BProv_iffForm_and_congr hleft hp
    simpa [G₂, paCompositeEqBodyAt,
      codeEqualityBodyTermAt] using h
  have hinner : BProv Ax_s (G.map (rename Nat.succ))
      (iffForm
        (ex (paCompositeEqBodyAt codedMap left right))
        (ex (codeEqualityBodyTermAt
          (Term.var 1) (Term.var 0)
          (Term.rename (fun n ↦ n+2) rawLeft)
          (Term.rename (fun n ↦ n+2) rawRight)))) := by
    apply BProv_iffForm_ex_congr_of_sentences
      (B := Ax_s) (G := G.map (rename Nat.succ))
      (fun f hf ↦ sentence_ax_s (f := f) hf)
    simpa [G₂] using hbody
  have houter := BProv_iffForm_ex_congr_of_sentences
    (B := Ax_s) (G := G)
    (fun f hf ↦ sentence_ax_s (f := f) hf) hinner
  simpa [paCompositeAt_eq_normalForm,
    codeEqualityTermAt] using houter

/-- The equality-atom case of paired raw/coded structural induction. -/
theorem BProv_Ax_s_paCompositeAt_eq_exact
    (P : OrdinalCodeGraphProofs)
    (G : List Formula) (left right : Term)
    (rawMap codedMap : Nat → Nat)
    (hcode : ∀ n, Free n (eq left right) →
      BProv Ax_s G
        (ordinalCodeGraphAt (rawMap n) (codedMap n))) :
    BProv Ax_s G
      (iffForm
        (rename rawMap (eq left right))
        (paCompositeAt codedMap (eq left right))) := by
  let G₂ : List Formula :=
    (G.map (rename Nat.succ)).map (rename Nat.succ)
  let rawMap₂ : Nat → Nat := fun n ↦ rawMap n + 2
  let codedMap₂ : Nat → Nat := fun n ↦ codedMap n + 2
  have hcode₂ : ∀ n, Free n (eq left right) →
      BProv Ax_s G₂
        (ordinalCodeGraphAt (rawMap₂ n) (codedMap₂ n)) := by
    intro n hn
    have h₀ := hcode n hn
    have h₁ := BProv_rename_of_sentences
      (B := Ax_s) (fun f hf ↦ sentence_ax_s (f := f) hf)
      h₀ Nat.succ
    have h₂ := BProv_rename_of_sentences
      (B := Ax_s) (fun f hf ↦ sentence_ax_s (f := f) hf)
      h₁ Nat.succ
    simpa [G₂, rawMap₂, codedMap₂, ordinalCodeGraphAt,
      rename_ordinalCodeGraphTermAt, Term.rename] using h₂
  have hleftRaw : ∀ n, Term.Free n left →
      BProv Ax_s G₂
        (ordinalCodeGraphAt (rawMap₂ n) (codedMap₂ n)) :=
    fun n hn ↦ hcode₂ n (Or.inl hn)
  have hrightRaw : ∀ n, Term.Free n right →
      BProv Ax_s G₂
        (ordinalCodeGraphAt (rawMap₂ n) (codedMap₂ n)) :=
    fun n hn ↦ hcode₂ n (Or.inr hn)
  have hleft₀ := P.term_graph G₂ left rawMap₂ codedMap₂ 1 hleftRaw
  have hright₀ := P.term_graph G₂ right rawMap₂ codedMap₂ 0 hrightRaw
  have hleft : BProv Ax_s G₂
      (iffForm
        (compositeTermGraphAt 1 (fun n ↦ codedMap n + 2) left)
        (ordinalCodeGraphTermAt
          (Term.rename (fun n ↦ n+2) (Term.rename rawMap left))
          (Term.var 1))) := by
    simpa [rawMap₂, codedMap₂, Term.rename_comp,
      Function.comp_def, Nat.add_assoc] using hleft₀
  have hright : BProv Ax_s G₂
      (iffForm
        (compositeTermGraphAt 0 (fun n ↦ codedMap n + 2) right)
        (ordinalCodeGraphTermAt
          (Term.rename (fun n ↦ n+2) (Term.rename rawMap right))
          (Term.var 0))) := by
    simpa [rawMap₂, codedMap₂, Term.rename_comp,
      Function.comp_def, Nat.add_assoc] using hright₀
  have hcomposite :=
    BProv_paCompositeAt_eq_iff_codeEqualityTermAt_of_termGraphs
      (G := G) (left := left) (right := right)
      (rawLeft := Term.rename rawMap left)
      (rawRight := Term.rename rawMap right)
      (codedMap := codedMap) hleft hright
  have hraw := BProv_eq_iff_codeEqualityTermAt P G
    (Term.rename rawMap left) (Term.rename rawMap right)
  have h := BProv_iffForm_trans hraw
    (BProv_iffForm_symm hcomposite)
  simpa [rename] using h

/-- The fragment of PA formulas whose syntax contains no quantifier. -/
def QuantifierFree : Formula → Prop
  | eq _ _ => True
  | bot => True
  | imp a b => QuantifierFree a ∧ QuantifierFree b
  | and a b => QuantifierFree a ∧ QuantifierFree b
  | or a b => QuantifierFree a ∧ QuantifierFree b
  | all _ => False
  | ex _ => False

/-- Once equality atoms are related through the ordinal-code graph, the
entire quantifier-free fragment follows by structural proof composition. -/
theorem BProv_Ax_s_paCompositeAt_iff_of_quantifierFree
    (equality_exact :
      ∀ (G : List Formula) (left right : Term)
          (rawMap codedMap : Nat → Nat),
        (∀ n, Free n (eq left right) →
          BProv Ax_s G
            (ordinalCodeGraphAt (rawMap n) (codedMap n))) →
        BProv Ax_s G
          (iffForm
            (rename rawMap (eq left right))
            (paCompositeAt codedMap (eq left right)))) :
    ∀ (phi : Formula), QuantifierFree phi →
      ∀ (G : List Formula) (rawMap codedMap : Nat → Nat),
        (∀ n, Free n phi →
          BProv Ax_s G
            (ordinalCodeGraphAt (rawMap n) (codedMap n))) →
        BProv Ax_s G
          (iffForm (rename rawMap phi) (paCompositeAt codedMap phi)) := by
  intro phi hqf
  induction phi with
  | eq left right =>
      intro G rawMap codedMap hcode
      exact equality_exact G left right rawMap codedMap hcode
  | bot =>
      intro G rawMap codedMap hcode
      simpa [rename, paCompositeAt,
        AckermannHF.PAInHF.formulaAt, hfFormulaAt] using
        (BProv_iffForm_refl (B := Ax_s) (G := G) bot)
  | imp a b iha ihb =>
      intro G rawMap codedMap hcode
      have hqa : QuantifierFree a := hqf.1
      have hqb : QuantifierFree b := hqf.2
      have ha := iha hqa G rawMap codedMap
        (fun n hn ↦ hcode n (Or.inl hn))
      have hb := ihb hqb G rawMap codedMap
        (fun n hn ↦ hcode n (Or.inr hn))
      simpa [rename, paCompositeAt,
        AckermannHF.PAInHF.formulaAt, hfFormulaAt] using
        BProv_iffForm_imp_congr ha hb
  | and a b iha ihb =>
      intro G rawMap codedMap hcode
      have hqa : QuantifierFree a := hqf.1
      have hqb : QuantifierFree b := hqf.2
      have ha := iha hqa G rawMap codedMap
        (fun n hn ↦ hcode n (Or.inl hn))
      have hb := ihb hqb G rawMap codedMap
        (fun n hn ↦ hcode n (Or.inr hn))
      simpa [rename, paCompositeAt,
        AckermannHF.PAInHF.formulaAt, hfFormulaAt] using
        BProv_iffForm_and_congr ha hb
  | or a b iha ihb =>
      intro G rawMap codedMap hcode
      have hqa : QuantifierFree a := hqf.1
      have hqb : QuantifierFree b := hqf.2
      have ha := iha hqa G rawMap codedMap
        (fun n hn ↦ hcode n (Or.inl hn))
      have hb := ihb hqb G rawMap codedMap
        (fun n hn ↦ hcode n (Or.inr hn))
      simpa [rename, paCompositeAt,
        AckermannHF.PAInHF.formulaAt, hfFormulaAt] using
        BProv_iffForm_or_congr ha hb
  | all a ih =>
      exact False.elim hqf
  | ex a ih =>
      exact False.elim hqf


end Formula
end PA

namespace AckermannHF

/-- Conditional deductive-bi-interpretability shell with the PA round trip
factored through the internal ordinal-Code graph package. -/
def PAHFFinDeductiveBiInterpretationCertificate_of_codeStructuralProofs
    (P : PA.Formula.PACompositeStructuralProofs)
    (hhf_roundTrip :
      ∀ (phi : Form), Sentence phi →
        BProv HFFinAx_s []
          (fIff phi
            (PAInHF.translateFormula
              (PA.Formula.translateHFFormula phi)))) :
    PAHFFinDeductiveBiInterpretationCertificate :=
  PAHFFinDeductiveBiInterpretationCertificate_of_remaining
    (fun phi hphi ↦
      PA.Formula.BProv_Ax_s_pa_roundTrip_of_structuralProofs
        P phi hphi)
    hhf_roundTrip

end AckermannHF
end SetTheory
