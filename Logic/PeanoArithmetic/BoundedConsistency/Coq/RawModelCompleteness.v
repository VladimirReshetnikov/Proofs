(**
  Raw-model completeness for first-order Peano arithmetic.

  The ordinary [PA.Model] record is intentionally not used here: it carries
  induction for every meta-theoretic predicate on its carrier, whereas a
  nonstandard model of first-order PA validates only the definable induction
  instances present in [PA.Formula.Ax_s].  The premise below therefore ranges
  over [RawPAModel] structures which satisfy exactly those object-language
  axioms.

  The proof transports an arbitrary PA sentence to finite set theory, applies
  generic first-order completeness there, and transports the resulting proof
  back along the concrete PA/HFFin deductive bi-interpretation.  This makes a
  useful final step for later bounded-consistency arguments: once a particular
  sentence has been proved valid in every raw PA model, no second completeness
  development is needed.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol Calculus Completeness.
From PAHF Require Import PAHF
  PAHFRawSemantics PAHFRawSemanticsGraph
  PAHFTermGraphFunctional PAHFProofTranslationSemantic
  PAHFProofCalculus PAHFConcreteAssembly.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.

Import ListNotations.
Import PAHierarchyReduction PACanonicalSelectorPA.
Import PA PA.Term PA.Formula.

Module PABoundedRawModelCompleteness.

(** Every PA sentence valid in all raw models of the genuine PA axiom schema
    has a bounded proof from that schema.  Here "bounded" is the library's
    finite-axiom wrapper [BProv]: each concrete derivation uses only a finite
    list of instances selected from [Ax_s]. *)
Theorem PA_BProv_of_raw_valid : forall phi,
  PA.Formula.Sentence phi ->
  (forall (M : RawPAModel), RawPASatisfies M ->
    forall e : nat -> M, raw_formula_sat M e phi) ->
  PA.Formula.BProv PA.Formula.Ax_s [] phi.
Proof.
  intros phi hSentence hRawValid.

  (** Interpret PA in finite set theory.  A model of [HFFinAx_s] supplies a
      finite-adjunction structure; its ordinal-like elements form a raw PA
      model satisfying every sealed PA axiom, including each definable
      induction instance. *)
  assert (hTranslated :
      Completeness.BProv HFFinAx_s [] (translateFormula phi)).
  {
    apply Completeness.completeness_inf.
    - exact Sentences_HFFin.
    - exact (translateFormula_sentence_of_PA_sentence phi hSentence).
    - intros V mem env hHFFin.
      pose (M :=
        firstOrderFiniteAdjunctionModel_of_HFFinAx_s V mem env hHFFin).
      pose (ordEnv := fun _ : nat => fofamOrdinalZero M).

      change (Fol.Sat V (foam_mem V M) env
        (formulaAt (fun n => n) phi)).
      assert (hVars : forall n, PA.Formula.Free n phi ->
          env ((fun k => k) n) = proj1_sig (ordEnv n)).
      {
        intros n hn.
        exfalso.
        exact (hSentence n hn).
      }
      apply (proj2 (formulaAt_iff_fofamPAFormulaSat
        V M (FOFAMTermGraphFunctionalLaw_finite_model V M)
        phi (fun n => n) env ordEnv hVars)).
      apply (proj1 (raw_formula_sat_fofam V M ordEnv phi)).
      apply (hRawValid (fofamRawPAModel M)).
      exact (fofam_raw_pa_satisfies V M).
  }

  (** Translate the finite-set proof back to PA.  The first lift replaces
      translated HFFin axioms by their concrete PA derivations. *)
  assert (hComposite :
      PA.Formula.BProv PA.Formula.Ax_s []
        (PA.Formula.translateHFFormula (translateFormula phi))).
  {
    apply (PA.Formula.BProv_lift_translatedHFFinAx_to_PA
      (PA.Formula.BProv_Ax_s_of_translatedHFFinAx_of_proofs
        concreteTranslatedHFFinAxiomProofs)).
    apply PA.Formula.BProv_translateHFFormula_of_BProv_HFFin.
    exact hTranslated.
  }

  (** The concrete round-trip theorem identifies the composite translation
      with the original sentence.  Its reverse implication followed by
      modus ponens finishes the proof. *)
  pose proof (concretePARoundTripProof phi hSentence) as hRoundTrip.
  pose proof (BProv_PA_iffForm_reverse
    PA.Formula.Ax_s [] phi
    (PA.Formula.translateHFFormula (translateFormula phi))
    hRoundTrip) as hBack.
  exact (PA.Formula.BProv_mp PA.Formula.Ax_s []
    (PA.Formula.translateHFFormula (translateFormula phi)) phi
    hBack hComposite).
Qed.

End PABoundedRawModelCompleteness.
