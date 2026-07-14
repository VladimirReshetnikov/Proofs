import CombinatoryLogic.SKIChurchConfluence
import CombinatoryLogic.SKIReductionPrimrec

/-!
# Exact partial-recursive observation of SKI terms

Finite SKI reduction has primitive-recursive certificates.  We enumerate a
natural number together with a trace certificate and accept it precisely when
the source, probed with two `K` arguments, reduces to the canonical redex-free
spine `churchK n`.  Confluence makes all accepted outputs equal, so the first
accepted certificate computes exactly the partial Church observation relation.
-/

namespace CombinatoryLogic.SKI.Term

open Coding ReductionCoding

/-- Code of the term obtained by probing a decoded source with two `K`s. -/
def probeCode (source : Code) : Code :=
  Coding.app (Coding.app source Coding.k) Coding.k

@[simp] theorem decode_probeCode (source : Code) :
    Coding.decode (probeCode source) = Coding.decode source ⬝ k ⬝ k := by
  simp [probeCode]

theorem primrec_probeCode : Primrec probeCode :=
  Coding.primrec_app.comp
    (Coding.primrec_app.comp Primrec.id (Primrec.const Coding.k))
    (Primrec.const Coding.k)

/-- Raw syntax code of the canonical redex-free numeral probe. -/
def churchKCode : Nat → Code
  | 0 => Coding.k
  | n + 1 => Coding.app Coding.k (churchKCode n)

@[simp] theorem churchKCode_eq_encode : ∀ n,
    churchKCode n = Coding.encode (churchK n)
  | 0 => rfl
  | n + 1 => by simp [churchKCode, churchK, churchKCode_eq_encode n]

@[simp] theorem decode_churchKCode (n : Nat) :
    Coding.decode (churchKCode n) = churchK n := by
  rw [churchKCode_eq_encode, Coding.decode_encode]

theorem primrec_churchKCode : Primrec churchKCode := by
  have step : Primrec₂ (fun (_ : Nat) (previous : Code) =>
      Coding.app Coding.k previous) :=
    Coding.primrec_app.comp₂ (Primrec₂.const Coding.k) Primrec₂.right
  apply (Primrec.nat_rec₁ Coding.k step).of_eq
  intro n
  induction n with
  | zero => rfl
  | succ n inductionHypothesis => simp [churchKCode, inductionHypothesis]

/-- The denumerable witness decoded from a raw search index. -/
def observationWitness (index : Nat) : Nat × TraceCertificate :=
  Denumerable.ofNat (Nat × TraceCertificate) index

theorem primrec_observationWitness : Primrec observationWitness := by
  exact Primrec.ofNat (Nat × TraceCertificate)

/-- A total certificate checker used by unbounded partial-recursive search. -/
def observationCandidate (source index : Nat) : Option Nat :=
  let witness := observationWitness index
  if TraceValid (probeCode source) (churchKCode witness.1) witness.2
  then some witness.1
  else none

theorem primrec₂_observationCandidate : Primrec₂ observationCandidate := by
  apply Primrec₂.mk
  have witness : Primrec (fun input : Nat × Nat => observationWitness input.2) :=
    primrec_observationWitness.comp Primrec.snd
  have output : Primrec (fun input : Nat × Nat => (observationWitness input.2).1) :=
    Primrec.fst.comp witness
  have trace : Primrec (fun input : Nat × Nat => (observationWitness input.2).2) :=
    Primrec.snd.comp witness
  have source : Primrec (fun input : Nat × Nat => probeCode input.1) :=
    primrec_probeCode.comp Primrec.fst
  have target : Primrec (fun input : Nat × Nat =>
      churchKCode (observationWitness input.2).1) :=
    primrec_churchKCode.comp output
  have endpoints : Primrec (fun input : Nat × Nat =>
      (probeCode input.1, churchKCode (observationWitness input.2).1)) :=
    Primrec.pair source target
  have valid : PrimrecPred (fun input : Nat × Nat =>
      TraceValid (probeCode input.1)
        (churchKCode (observationWitness input.2).1)
        (observationWitness input.2).2) :=
    ReductionCoding.primrecRel_traceValid.comp endpoints trace
  exact (Primrec.ite valid (Primrec.option_some.comp output) (Primrec.const none)).of_eq
    (fun input => by simp only [observationCandidate])

/-- Partial output obtained by searching for a finite Church-observation trace. -/
def observeCode (source : Code) : Part Nat :=
  Nat.rfindOpt (observationCandidate source)

/-- Exact SKI observation is a partial-recursive function of the source code. -/
theorem partrec_observeCode : Partrec observeCode :=
  Partrec.rfindOpt primrec₂_observationCandidate.to_comp

/-- Every result returned by certificate search is a genuine Church observation. -/
theorem observesChurch_of_mem_observeCode {source : Code} {n : Nat}
    (membership : n ∈ observeCode source) : ObservesChurch n (Coding.decode source) := by
  obtain ⟨index, candidate⟩ := Nat.rfindOpt_spec membership
  change n ∈ (if TraceValid (probeCode source)
      (churchKCode (observationWitness index).1) (observationWitness index).2
    then some (observationWitness index).1 else none) at candidate
  split at candidate
  next valid =>
    have outputEquality : (observationWitness index).1 = n := by
      simpa using candidate
    have reduction := ReductionCoding.trace_sound valid
    rw [outputEquality] at reduction
    simpa only [ObservesChurch, decode_probeCode, decode_churchKCode] using reduction
  next => simp at candidate

/-- Every genuine Church observation is eventually found by certificate search. -/
theorem mem_observeCode_of_observesChurch {source : Code} {n : Nat}
    (observation : ObservesChurch n (Coding.decode source)) : n ∈ observeCode source := by
  obtain ⟨trace, valid⟩ := ReductionCoding.trace_complete observation
  have validCode : TraceValid (probeCode source) (churchKCode n) trace := by
    simpa [probeCode] using valid
  let witness : Nat × TraceCertificate := (n, trace)
  let index : Nat := Encodable.encode witness
  have witnessDecoded : observationWitness index = witness := by
    simp [observationWitness, index, witness]
  have candidate : n ∈ observationCandidate source index := by
    change n ∈ (if TraceValid (probeCode source)
        (churchKCode (observationWitness index).1) (observationWitness index).2
      then some (observationWitness index).1 else none)
    rw [witnessDecoded]
    change n ∈ (if TraceValid (probeCode source) (churchKCode n) trace then some n else none)
    rw [if_pos validCode]
    simp
  have domain : (observeCode source).Dom :=
    Nat.rfindOpt_dom.2 ⟨index, n, candidate⟩
  have foundObservation :
      ObservesChurch ((observeCode source).get domain) (Coding.decode source) :=
    observesChurch_of_mem_observeCode (Part.get_mem domain)
  have outputEquality : (observeCode source).get domain = n :=
    observesChurch_unique foundObservation observation
  exact outputEquality ▸ Part.get_mem domain

/-- Graph theorem for the exact partial-recursive SKI observer. -/
theorem mem_observeCode_iff {source : Code} {n : Nat} :
    n ∈ observeCode source ↔ ObservesChurch n (Coding.decode source) :=
  ⟨observesChurch_of_mem_observeCode, mem_observeCode_of_observesChurch⟩

/-! ## Partial-recursive semantics of a fixed SKI program -/

/-- Raw code of the canonical arithmetic Church representative. -/
def toChurchCode : Nat → Code
  | 0 => Coding.encode Zero
  | n + 1 => Coding.app (Coding.encode Succ) (toChurchCode n)

@[simp] theorem toChurchCode_eq_encode : ∀ n,
    toChurchCode n = Coding.encode (toChurch n)
  | 0 => rfl
  | n + 1 => by simp [toChurchCode, toChurch, toChurchCode_eq_encode n]

@[simp] theorem decode_toChurchCode (n : Nat) :
    Coding.decode (toChurchCode n) = toChurch n := by
  rw [toChurchCode_eq_encode, Coding.decode_encode]

theorem primrec_toChurchCode : Primrec toChurchCode := by
  have step : Primrec₂ (fun (_ : Nat) (previous : Code) =>
      Coding.app (Coding.encode Succ) previous) :=
    Coding.primrec_app.comp₂ (Primrec₂.const (Coding.encode Succ)) Primrec₂.right
  apply (Primrec.nat_rec₁ (Coding.encode Zero) step).of_eq
  intro n
  induction n with
  | zero => rfl
  | succ n inductionHypothesis => simp [toChurchCode, inductionHypothesis]

/-- Code of a fixed SKI program applied to its canonical Church input. -/
def appliedCode (program : Term) (input : Nat) : Code :=
  Coding.app (Coding.encode program) (toChurchCode input)

@[simp] theorem decode_appliedCode (program : Term) (input : Nat) :
    Coding.decode (appliedCode program input) = program ⬝ toChurch input := by
  simp [appliedCode]

theorem primrec_appliedCode (program : Term) : Primrec (appliedCode program) :=
  Coding.primrec_app.comp (Primrec.const (Coding.encode program)) primrec_toChurchCode

/-- Exact partial observation semantics of a unary SKI program. -/
def observationSemantics (program : Term) (input : Nat) : Part Nat :=
  observeCode (appliedCode program input)

/-- Every unary SKI program denotes a partial-recursive natural-number function. -/
theorem partrec_observationSemantics (program : Term) :
    Partrec (observationSemantics program) :=
  partrec_observeCode.comp (primrec_appliedCode program).to_comp

/-- The partial-recursive semantics has exactly the program's Church observations. -/
theorem mem_observationSemantics_iff {program : Term} {input output : Nat} :
    output ∈ observationSemantics program input ↔
      ObservesChurch output (program ⬝ toChurch input) := by
  simpa [observationSemantics] using
    (mem_observeCode_iff (source := appliedCode program input) (n := output))

/-- Exact, divergence-sensitive realization of a unary partial function. -/
def ExactlyComputes (program : Term) (function : Nat →. Nat) : Prop :=
  ∀ input output, output ∈ function input ↔
    ObservesChurch output (program ⬝ toChurch input)

/-- A partial function is exactly SKI-computable when one closed program
realizes its complete graph, including undefined inputs. -/
def ExactlyComputable (function : Nat →. Nat) : Prop :=
  ∃ program, ExactlyComputes program function

theorem observationSemantics_exactlyComputes (program : Term) :
    ExactlyComputes program (observationSemantics program) := by
  intro input output
  exact mem_observationSemantics_iff

/-- Reverse Turing-completeness inclusion: exact SKI computability implies
partial recursiveness. -/
theorem partrec_of_exactlyComputable {function : Nat →. Nat}
    (computable : ExactlyComputable function) : Partrec function := by
  obtain ⟨program, correctness⟩ := computable
  exact (partrec_observationSemantics program).of_eq fun input =>
    Part.ext fun output =>
      mem_observationSemantics_iff.trans (correctness input output).symm

end CombinatoryLogic.SKI.Term
