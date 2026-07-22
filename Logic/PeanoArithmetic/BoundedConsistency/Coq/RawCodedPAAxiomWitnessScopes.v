(** Opaque scope interfaces for complete PA-axiom witnesses. *)

From Stdlib Require Import Arith Lia.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From BoundedPAConsistency Require Import
  RawCodedPAAxiomWitness
  RawCodedScopedFormulaDiagonalSubstitution
  RawCodedStandardFormulaScopeCombinators
  RawCodedBasicFormulaScopes
  RawCodedFormulaOperationScopes
  RawCodedPAAxiomWitnessBoundScopes.

Module PABoundedRawCodedPAAxiomWitnessScopes.

Import PA.
Import PAListRepresentability.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedScopedFormulaDiagonalSubstitution.
Import PABoundedRawCodedStandardFormulaScopeCombinators.
Import PABoundedRawCodedBasicFormulaScopes.
Import PABoundedRawCodedFormulaOperationScopes.
Import PABoundedRawCodedPAAxiomWitnessBoundScopes.

Lemma standardFormulaScoped_axiomWitnessAnd10 : forall scope
    a b c d f g h i j k,
  StandardFormulaScoped scope a ->
  StandardFormulaScoped scope b ->
  StandardFormulaScoped scope c ->
  StandardFormulaScoped scope d ->
  StandardFormulaScoped scope f ->
  StandardFormulaScoped scope g ->
  StandardFormulaScoped scope h ->
  StandardFormulaScoped scope i ->
  StandardFormulaScoped scope j ->
  StandardFormulaScoped scope k ->
  StandardFormulaScoped scope (axiomWitnessAnd10 a b c d f g h i j k).
Proof.
  intros scope a b c d f g h i j k
    ha hb hc hd hf hg hh hi hj hk.
  unfold axiomWitnessAnd10.
  apply standardFormulaScoped_and; [exact ha |].
  apply standardFormulaScoped_and; [exact hb |].
  apply standardFormulaScoped_and; [exact hc |].
  apply standardFormulaScoped_and; [exact hd |].
  apply standardFormulaScoped_and; [exact hf |].
  apply standardFormulaScoped_and; [exact hg |].
  apply standardFormulaScoped_and; [exact hh |].
  apply standardFormulaScoped_and; [exact hi |].
  apply standardFormulaScoped_and; assumption.
Qed.

Lemma standardFormulaScoped_codedPAAxiomInductionTermAt : forall scope
    source axiom,
  StandardTermScoped scope source ->
  StandardTermScoped scope axiom ->
  StandardFormulaScoped scope
    (codedPAAxiomInductionTermAt source axiom).
Proof.
  intros scope source axiom hsource haxiom.
  unfold codedPAAxiomInductionTermAt, axiomWitnessEx9.
  repeat apply standardFormulaScoped_ex.
  apply standardFormulaScoped_axiomWitnessAnd10.
  - apply standardFormulaScoped_codedFormulaShiftTermAt.
    + apply standardTermScoped_numeral.
    + apply standardTermScoped_numeral.
    + exact (standardTermScoped_lift scope 9 source hsource).
    + apply standardTermScoped_var; lia.
  - apply standardFormulaScoped_codedFormulaSingleSubstitutionTermAt.
    + apply standardTermScoped_numeral.
    + apply standardTermScoped_var; lia.
    + apply standardTermScoped_var; lia.
  - apply standardFormulaScoped_codedFormulaSingleSubstitutionTermAt.
    + apply standardTermScoped_numeral.
    + exact (standardTermScoped_lift scope 9 source hsource).
    + apply standardTermScoped_var; lia.
  - apply standardFormulaScoped_formulaAllCodeTermAt.
    + apply standardTermScoped_var; lia.
    + exact (standardTermScoped_lift scope 9 source hsource).
  - apply standardFormulaScoped_formulaImpCodeTermAt.
    + apply standardTermScoped_var; lia.
    + exact (standardTermScoped_lift scope 9 source hsource).
    + apply standardTermScoped_var; lia.
  - apply standardFormulaScoped_formulaAllCodeTermAt;
      apply standardTermScoped_var; lia.
  - apply standardFormulaScoped_formulaAndCodeTermAt;
      apply standardTermScoped_var; lia.
  - apply standardFormulaScoped_formulaImpCodeTermAt;
      apply standardTermScoped_var; lia.
  - apply standardFormulaScoped_codedFormulaBoundTermAt;
      apply standardTermScoped_var; lia.
  - apply standardFormulaScoped_codedUniversalClosureTermAt.
    + apply standardTermScoped_var; lia.
    + apply standardTermScoped_var; lia.
    + exact (standardTermScoped_lift scope 9 axiom haxiom).
Qed.

Lemma standardFormulaScoped_codedPAAxiomFiniteWitnessTermAt : forall scope
    tag axiomFormula witness axiom,
  StandardTermScoped scope witness ->
  StandardTermScoped scope axiom ->
  StandardFormulaScoped scope
    (codedPAAxiomFiniteWitnessTermAt
      tag axiomFormula witness axiom).
Proof.
  intros scope tag axiomFormula witness axiom hwitness haxiom.
  unfold codedPAAxiomFiniteWitnessTermAt.
  apply standardFormulaScoped_and.
  - apply standardFormulaScoped_codeList1TermAt.
    + exact hwitness.
    + apply standardTermScoped_numeral.
  - apply standardFormulaScoped_eq.
    + exact haxiom.
    + apply standardTermScoped_numeral.
Qed.

Lemma standardFormulaScoped_codedPAAxiomWitnessTermAt : forall scope
    witness axiom,
  StandardTermScoped scope witness ->
  StandardTermScoped scope axiom ->
  StandardFormulaScoped scope (codedPAAxiomWitnessTermAt witness axiom).
Proof.
  intros scope witness axiom hwitness haxiom.
  unfold codedPAAxiomWitnessTermAt.
  apply standardFormulaScoped_or.
  - apply standardFormulaScoped_codedPAAxiomFiniteWitnessTermAt;
      assumption.
  - apply standardFormulaScoped_or.
    + apply standardFormulaScoped_codedPAAxiomFiniteWitnessTermAt;
        assumption.
    + apply standardFormulaScoped_or.
      * apply standardFormulaScoped_codedPAAxiomFiniteWitnessTermAt;
          assumption.
      * apply standardFormulaScoped_or.
        -- apply standardFormulaScoped_codedPAAxiomFiniteWitnessTermAt;
             assumption.
        -- apply standardFormulaScoped_or.
           ++ apply standardFormulaScoped_codedPAAxiomFiniteWitnessTermAt;
                assumption.
           ++ apply standardFormulaScoped_or.
              ** apply standardFormulaScoped_codedPAAxiomFiniteWitnessTermAt;
                   assumption.
              ** apply standardFormulaScoped_ex.
                 apply standardFormulaScoped_and.
                 --- apply standardFormulaScoped_codeList2TermAt.
                     +++ exact (standardTermScoped_lift
                          scope 1 witness hwitness).
                     +++ apply standardTermScoped_numeral.
                     +++ apply standardTermScoped_var; lia.
                 --- apply standardFormulaScoped_codedPAAxiomInductionTermAt.
                     +++ apply standardTermScoped_var; lia.
                     +++ exact (standardTermScoped_lift
                          scope 1 axiom haxiom).
Qed.

End PABoundedRawCodedPAAxiomWitnessScopes.
