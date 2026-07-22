(**
  The finite formula-shift orbit needed by the three existential eliminations.

  The restricted-proof assumption has three nested existential binders.  Its
  initial singleton context therefore grows, after the successive pointwise
  de Bruijn shifts, as follows:

      [A0]
      [shift A0]

      [A1; shift A0]
      [shift A1; shift^2 A0]

      [A2; shift A1; shift^2 A0]
      [shift A2; shift^2 A1; shift^3 A0].

  This file makes those six formula-operation edges explicit and proves that
  they are sufficient to construct the three genuine [RawContextShift]
  witnesses.  Consequently, no context traversal remains hidden in the
  later field-refutation compiler: the only syntactic obligation is the
  finite formula-shift orbit itself.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedFormulaOperations
  RawCodedContextShift RawCodedRestrictedPAConsistencyOpenCompiler
  RawCodedRestrictedPAConsistencyOpenDescent
  RawCodedRestrictedPAConsistencyTripleExDescent.

Module PABoundedRawCodedRestrictedPAConsistencyShiftOrbit.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedRestrictedPAConsistencyOpenCompiler.
Import PABoundedRawCodedRestrictedPAConsistencyOpenDescent.
Import PABoundedRawCodedRestrictedPAConsistencyTripleExDescent.

(** Six edges are necessary because formulas already present in the context
    are shifted again at every later existential elimination. *)
Definition RawRestrictedPAFormulaShiftOrbit (M : RawPAModel)
    (numeralCode
      shiftedAssumption1 shiftedAssumption2 shiftedAssumption3
      shiftedAfterWitness1 shiftedAfterWitness2
      shiftedAfterProof1 : M) : Prop :=
  RawCodedFormulaShift M
    (raw_zero M) (rawNumeralValue M 1)
    (rawRestrictedPAProofAssumptionCode M numeralCode)
    shiftedAssumption1 /\
  RawCodedFormulaShift M
    (raw_zero M) (rawNumeralValue M 1)
    shiftedAssumption1 shiftedAssumption2 /\
  RawCodedFormulaShift M
    (raw_zero M) (rawNumeralValue M 1)
    shiftedAssumption2 shiftedAssumption3 /\
  RawCodedFormulaShift M
    (raw_zero M) (rawNumeralValue M 1)
    (rawRestrictedPAProofAfterWitnessCode M numeralCode)
    shiftedAfterWitness1 /\
  RawCodedFormulaShift M
    (raw_zero M) (rawNumeralValue M 1)
    shiftedAfterWitness1 shiftedAfterWitness2 /\
  RawCodedFormulaShift M
    (raw_zero M) (rawNumeralValue M 1)
    (rawRestrictedPAProofAfterProofCode M numeralCode)
    shiftedAfterProof1.

Arguments RawRestrictedPAFormulaShiftOrbit
  M numeralCode
    shiftedAssumption1 shiftedAssumption2 shiftedAssumption3
    shiftedAfterWitness1 shiftedAfterWitness2 shiftedAfterProof1
  : clear implicits.

(** The canonical list codes for the three shifted contexts. *)
Definition rawRestrictedPAShiftedRootContextCode (M : RawPAModel)
    (shiftedAssumption1 : M) : M :=
  rawListNode M shiftedAssumption1 (raw_zero M).

Definition rawRestrictedPAShiftedWitnessContextCode (M : RawPAModel)
    (shiftedAfterWitness1 shiftedAssumption2 : M) : M :=
  rawListNode M shiftedAfterWitness1
    (rawListNode M shiftedAssumption2 (raw_zero M)).

Definition rawRestrictedPAShiftedProofContextCode (M : RawPAModel)
    (shiftedAfterProof1 shiftedAfterWitness2 shiftedAssumption3 : M) : M :=
  rawListNode M shiftedAfterProof1
    (rawListNode M shiftedAfterWitness2
      (rawListNode M shiftedAssumption3 (raw_zero M))).

Arguments rawRestrictedPAShiftedRootContextCode
  M shiftedAssumption1 : clear implicits.
Arguments rawRestrictedPAShiftedWitnessContextCode
  M shiftedAfterWitness1 shiftedAssumption2 : clear implicits.
Arguments rawRestrictedPAShiftedProofContextCode
  M shiftedAfterProof1 shiftedAfterWitness2 shiftedAssumption3
  : clear implicits.

(** Construct the exact three context shifts by repeated canonical cons.
    This theorem is deliberately independent of any functionality result for
    formula shifting: every target formula is retained as explicit data. *)
Theorem raw_restrictedPAExistentialDescentContexts_of_formulaShiftOrbit :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    numeralCode
    shiftedAssumption1 shiftedAssumption2 shiftedAssumption3
    shiftedAfterWitness1 shiftedAfterWitness2 shiftedAfterProof1,
  RawRestrictedPAFormulaShiftOrbit M numeralCode
    shiftedAssumption1 shiftedAssumption2 shiftedAssumption3
    shiftedAfterWitness1 shiftedAfterWitness2 shiftedAfterProof1 ->
  RawRestrictedPAExistentialDescentContexts M numeralCode
    (rawRestrictedPAShiftedRootContextCode M shiftedAssumption1)
    (rawRestrictedPAShiftedWitnessContextCode M
      shiftedAfterWitness1 shiftedAssumption2)
    (rawRestrictedPAShiftedProofContextCode M
      shiftedAfterProof1 shiftedAfterWitness2 shiftedAssumption3).
Proof.
  intros M hPA numeralCode
    shiftedAssumption1 shiftedAssumption2 shiftedAssumption3
    shiftedAfterWitness1 shiftedAfterWitness2 shiftedAfterProof1
    [hAssumption1 [hAssumption2 [hAssumption3
      [hAfterWitness1 [hAfterWitness2 hAfterProof1]]]]].
  unfold RawRestrictedPAExistentialDescentContexts,
    rawRestrictedPAOpenRootContextCode,
    rawRestrictedPAAfterWitnessContextCode,
    rawRestrictedPAAfterProofContextCode,
    rawRestrictedPAShiftedRootContextCode,
    rawRestrictedPAShiftedWitnessContextCode,
    rawRestrictedPAShiftedProofContextCode.
  split.
  - apply (raw_contextShift_cons M hPA).
    + apply raw_contextShift_empty. exact hPA.
    + exact hAssumption1.
  - split.
    + apply (raw_contextShift_cons M hPA).
      * apply (raw_contextShift_cons M hPA).
        -- apply raw_contextShift_empty. exact hPA.
        -- exact hAssumption2.
      * exact hAfterWitness1.
    + apply (raw_contextShift_cons M hPA).
      * apply (raw_contextShift_cons M hPA).
        -- apply (raw_contextShift_cons M hPA).
           ++ apply raw_contextShift_empty. exact hPA.
           ++ exact hAssumption3.
        -- exact hAfterWitness2.
      * exact hAfterProof1.
Qed.

(** Existential packaging in the shape consumed by the old descent theorem.
    This is the public bridge used by later compiler stages. *)
Corollary raw_restrictedPAExistentialDescentContexts_exists_of_formulaShiftOrbit :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    numeralCode
    shiftedAssumption1 shiftedAssumption2 shiftedAssumption3
    shiftedAfterWitness1 shiftedAfterWitness2 shiftedAfterProof1,
  RawRestrictedPAFormulaShiftOrbit M numeralCode
    shiftedAssumption1 shiftedAssumption2 shiftedAssumption3
    shiftedAfterWitness1 shiftedAfterWitness2 shiftedAfterProof1 ->
  exists shiftedRootContext shiftedWitnessContext shiftedProofContext : M,
    RawRestrictedPAExistentialDescentContexts M numeralCode
      shiftedRootContext shiftedWitnessContext shiftedProofContext.
Proof.
  intros M hPA numeralCode
    shiftedAssumption1 shiftedAssumption2 shiftedAssumption3
    shiftedAfterWitness1 shiftedAfterWitness2 shiftedAfterProof1 horbit.
  exists (rawRestrictedPAShiftedRootContextCode M shiftedAssumption1),
    (rawRestrictedPAShiftedWitnessContextCode M
      shiftedAfterWitness1 shiftedAssumption2),
    (rawRestrictedPAShiftedProofContextCode M
      shiftedAfterProof1 shiftedAfterWitness2 shiftedAssumption3).
  exact
    (raw_restrictedPAExistentialDescentContexts_of_formulaShiftOrbit
      M hPA numeralCode
      shiftedAssumption1 shiftedAssumption2 shiftedAssumption3
      shiftedAfterWitness1 shiftedAfterWitness2 shiftedAfterProof1 horbit).
Qed.

End PABoundedRawCodedRestrictedPAConsistencyShiftOrbit.
