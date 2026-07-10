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
