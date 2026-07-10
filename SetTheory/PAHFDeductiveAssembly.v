(* ===================================================================== *)
(*  PAHFDeductiveAssembly.v                                             *)
(*                                                                       *)
(*  Minimal assembly layer for the deductive PA/HFFin                    *)
(*  bi-interpretation.  The mathematical proof modules can target the    *)
(*  four explicit hypotheses below; no intermediate package hierarchy is *)
(*  required.                                                            *)
(* ===================================================================== *)

From Stdlib Require Import List.
From SetTheory Require Import Fol Calculus Completeness PAHF PAHFInterpretations
  PAHFTranslatedHFFin.

Import ListNotations.

(* The reverse structural translation already targets the theory whose
   axioms are translated HFFin axioms.  A concrete proof record discharges
   exactly those axioms into PA proper. *)
Definition hfInPAFiniteInterpretation_of_proofs
    (P : PA.Formula.TranslatedHFFinAxiomProofs) :
  TheoryInterpretation form PA.formula
    Sentence PA.Formula.Sentence
    HFFinAx_s PA.Formula.Ax_s
    BProv PA.Formula.BProv.
Proof.
  refine {| ti_translate := PA.Formula.translateHFFormula |}.
  - intros phi hphi.
    apply PA.Formula.translateHFFormula_sentence_of_HF_sentence.
    exact hphi.
  - intros phi hphi.
    apply (PA.Formula.BProv_Ax_s_of_translatedHFFinAx_of_proofs P).
    apply PA.Formula.translatedHFFinAx_intro.
    exact hphi.
  - intros phi _ hprov.
    apply (PA.Formula.BProv_lift_translatedHFFinAx_to_PA
      (PA.Formula.BProv_Ax_s_of_translatedHFFinAx_of_proofs P)).
    apply PA.Formula.BProv_translateHFFormula_of_BProv_HFFin.
    exact hprov.
Defined.

Definition PARoundTripProof : Prop :=
  forall phi,
    PA.Formula.Sentence phi ->
    PA.Formula.BProv PA.Formula.Ax_s []
      (PA.Formula.iffForm phi
        (PA.Formula.translateHFFormula (translateFormula phi))).

Definition HFRoundTripProof : Prop :=
  forall phi,
    Sentence phi ->
    BProv HFFinAx_s []
      (fIff phi
        (translateFormula (PA.Formula.translateHFFormula phi))).

(* Directly inhabit the existing four-field certificate.  This replaces the
   larger sequence of historical "remaining proofs" and structural-package
   constructors used while the Lean proof was being developed. *)
Definition paHFFinDeductiveBiInterpretation_of_proofs
    (T : HFFinPAProofTranslation)
    (P : PA.Formula.TranslatedHFFinAxiomProofs)
    (hPA : PARoundTripProof)
    (hHF : HFRoundTripProof) :
  PAHFFinDeductiveBiInterpretationCertificate.
Proof.
  refine
    {| dbic_pa_in_hf := paInHFFinTheoryInterpretation_of_translation T;
       dbic_hf_in_pa := hfInPAFiniteInterpretation_of_proofs P;
       dbic_pa_round_trip := hPA;
       dbic_hf_round_trip := hHF |}.
Defined.
