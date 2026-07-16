import CombinatoryLogic.PartrecToSKI
import CombinatoryLogic.SKIObservationPartrec
import Mathlib.Computability.RE

/-!
# Exact compilation of partial-recursive functions to SKI

This module strengthens the defined-case compiler in `PartrecToSKI` to an
exact compiler.  Instead of imposing an evaluation strategy on every compiler
clause, it specializes one fixed SKI realizer for Mathlib's universal
partial-recursive evaluator and then applies Kleene's second recursion theorem
to remove all spurious observations.  A fair partial-recursive race compares
the desired result with the program's own exact observation, shifted by one;
confluence makes the shifted self-observation branch impossible.
-/

namespace CombinatoryLogic.SKI.Term

open Nat.Partrec
open Polynomial
open Denumerable

/-- Forming an SKI application is computable under the bijective syntax
coding from `SKICoding`. -/
theorem computable₂_app : _root_.Computable₂ ((· ⬝ ·) : Term → Term → Term) := by
  apply _root_.Computable₂.mk
  rw [← _root_.Computable.encode_iff]
  change _root_.Computable fun terms : Term × Term =>
    Coding.app (Coding.encode terms.1) (Coding.encode terms.2)
  exact Coding.primrec_app.to_comp.comp
    (_root_.Computable.encode.comp _root_.Computable.fst)
    (_root_.Computable.encode.comp _root_.Computable.snd)

/-- The canonical Church representative is an effective syntax translation. -/
theorem computable_toChurch : _root_.Computable toChurch := by
  rw [← _root_.Computable.encode_iff]
  change _root_.Computable fun input => Coding.encode (toChurch input)
  exact primrec_toChurchCode.to_comp.of_eq toChurchCode_eq_encode

/-! ## A fixed universal realizer and effective specialization -/

/-- Mathlib's universal partial-recursive evaluator, with its code and input
packed into one natural number. -/
def universalEval (input : Nat) : Part Nat :=
  Code.eval (ofNat Code input.unpair.1) input.unpair.2

theorem partrec_universalEval : Partrec universalEval := by
  exact Code.eval_part.comp
    ((_root_.Computable.ofNat Code).comp
      (_root_.Computable.fst.comp _root_.Computable.unpair))
    (_root_.Computable.snd.comp _root_.Computable.unpair)

theorem natPartrec_universalEval : Nat.Partrec universalEval :=
  Partrec.nat_iff.mp partrec_universalEval

/-- Specialize a unary universal realizer to a fixed partial-recursive code. -/
def specializeTerm (universal : Term) (code : Code) : Term :=
  B ⬝ universal ⬝ (NatPair ⬝ toChurch (Encodable.encode code))

theorem computable_specializeTerm (universal : Term) :
    _root_.Computable (specializeTerm universal) := by
  exact computable₂_app.comp
    (_root_.Computable.const (B ⬝ universal))
    (computable₂_app.comp
      (_root_.Computable.const NatPair)
      (computable_toChurch.comp _root_.Computable.encode))

/-- Specialization preserves the defined-case guarantee of the universal
realizer. -/
theorem specializeTerm_computes {universal : Term}
    (computesUniversal : Computes universal universalEval) (code : Code) :
    Computes (specializeTerm universal code) code.eval := by
  intro input churchInput isChurchInput output outputMembership
  have isChurchCode :
      IsChurch (Encodable.encode code) (toChurch (Encodable.encode code)) :=
    toChurch_correct _
  have isChurchPair := natPair_correct (Encodable.encode code) input
    (toChurch (Encodable.encode code)) churchInput isChurchCode isChurchInput
  have universalMembership :
      output ∈ universalEval (Nat.pair (Encodable.encode code) input) := by
    simpa [universalEval] using outputMembership
  exact isChurch_trans output
    (B_def universal (NatPair ⬝ toChurch (Encodable.encode code)) churchInput)
    (computesUniversal _ _ isChurchPair output universalMembership)

/-! ## Exact observation of the effectively specialized program -/

/-- Exact observation semantics of the specialized universal realizer. -/
def specializedObservation (universal : Term) (input : Code × Nat) : Part Nat :=
  observationSemantics (specializeTerm universal input.1) input.2

theorem partrec_specializedObservation (universal : Term) :
    Partrec (specializedObservation universal) := by
  apply partrec_observeCode.comp
  exact Coding.primrec_app.to_comp.comp
    (_root_.Computable.encode.comp
      ((computable_specializeTerm universal).comp _root_.Computable.fst))
    (primrec_toChurchCode.to_comp.comp _root_.Computable.snd)

theorem mem_specializedObservation_iff {universal : Term} {code : Code}
    {input output : Nat} :
    output ∈ specializedObservation universal (code, input) ↔
      ObservesChurch output (specializeTerm universal code ⬝ toChurch input) := by
  exact mem_observationSemantics_iff

/-! ## Self-correcting exact compilation -/

/-- Every partial-recursive unary function has an SKI program whose Church
observations are exactly its graph.  The shifted self-observation branch of
the fair race cannot win: if it returned `m + 1`, defined-case correctness
would make the program observe `m + 1`, while that branch's premise already
makes the same program observe `m`; confluence forces `m + 1 = m`. -/
theorem exactlyComputable_of_partrec {function : Nat →. Nat}
    (functionPartrec : Partrec function) : ExactlyComputable function := by
  obtain ⟨universal, computesUniversal⟩ :=
    natPartrec_skiComputable universalEval natPartrec_universalEval
  let desired : Code × Nat →. Nat := fun input => function input.2
  have desiredPartrec : Partrec desired := by
    exact functionPartrec.comp _root_.Computable.snd
  let correction : Code × Nat →. Nat := fun input =>
    (specializedObservation universal input).map Nat.succ
  have correctionPartrec : Partrec correction := by
    simpa only [correction] using
      (partrec_specializedObservation universal).map
        (_root_.Computable.succ.comp _root_.Computable.snd).to₂
  obtain ⟨race, racePartrec, raceSpecification⟩ :=
    Partrec.merge' desiredPartrec correctionPartrec
  have racePartrec₂ : Partrec₂ (fun code input => race (code, input)) := by
    simpa only using racePartrec.to₂
  obtain ⟨self, selfFixed⟩ := Code.fixed_point₂ racePartrec₂
  let program := specializeTerm universal self
  have computesSelf : Computes program self.eval := by
    simpa only [program] using specializeTerm_computes computesUniversal self
  have raceObservation {input output : Nat}
      (membership : output ∈ race (self, input)) :
      ObservesChurch output (program ⬝ toChurch input) := by
    apply observesChurch_of_isChurch
    apply computesSelf input (toChurch input) (toChurch_correct input) output
    simpa only [selfFixed] using membership
  have correctionImpossible {input output : Nat}
      (raceMembership : output ∈ race (self, input))
      (correctionMembership : output ∈ correction (self, input)) : False := by
    have outputObservation := raceObservation raceMembership
    change output ∈ (specializedObservation universal (self, input)).map Nat.succ at correctionMembership
    obtain ⟨observed, observedMembership, outputEquality⟩ :=
      (Part.mem_map_iff _).mp correctionMembership
    have observedObservation : ObservesChurch observed (program ⬝ toChurch input) := by
      simpa only [program] using
        (mem_specializedObservation_iff.mp observedMembership)
    have sameOutput := observesChurch_unique outputObservation observedObservation
    omega
  refine ⟨program, fun input output => ?_⟩
  constructor
  · intro desiredMembership
    have desiredDomain : (desired (self, input)).Dom := by
      exact desiredMembership.fst
    have raceDomain : (race (self, input)).Dom :=
      (raceSpecification (self, input)).2.2 (Or.inl desiredDomain)
    let raced := (race (self, input)).get raceDomain
    have raceMembership : raced ∈ race (self, input) := Part.get_mem raceDomain
    rcases (raceSpecification (self, input)).1 raced raceMembership with
      racedDesired | racedCorrection
    · change raced ∈ function input at racedDesired
      have outputEquality : raced = output := Part.mem_unique racedDesired desiredMembership
      simpa only [outputEquality] using raceObservation raceMembership
    · exact (correctionImpossible raceMembership racedCorrection).elim
  · intro outputObservation
    have semanticMembership :
        output ∈ specializedObservation universal (self, input) :=
      mem_specializedObservation_iff.mpr (by
        simpa only [program] using outputObservation)
    have correctionMembership : output + 1 ∈ correction (self, input) := by
      change output + 1 ∈ (specializedObservation universal (self, input)).map Nat.succ
      exact (Part.mem_map_iff _).mpr ⟨output, semanticMembership, rfl⟩
    have correctionDomain : (correction (self, input)).Dom :=
      correctionMembership.fst
    have raceDomain : (race (self, input)).Dom :=
      (raceSpecification (self, input)).2.2 (Or.inr correctionDomain)
    let raced := (race (self, input)).get raceDomain
    have raceMembership : raced ∈ race (self, input) := Part.get_mem raceDomain
    have racedObservation := raceObservation raceMembership
    have outputEquality : raced = output :=
      observesChurch_unique racedObservation outputObservation
    rcases (raceSpecification (self, input)).1 raced raceMembership with
      racedDesired | racedCorrection
    · change raced ∈ function input at racedDesired
      simpa only [outputEquality] using racedDesired
    · exact (correctionImpossible raceMembership racedCorrection).elim

/-- Exact SKI computability and partial recursiveness coincide. -/
theorem partrec_iff_exactlyComputable {function : Nat →. Nat} :
    Partrec function ↔ ExactlyComputable function :=
  ⟨exactlyComputable_of_partrec, partrec_of_exactlyComputable⟩

end CombinatoryLogic.SKI.Term
