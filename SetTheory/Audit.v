(* ===================================================================== *)
(*  Audit.v                                                              *)
(*                                                                       *)
(*  Coq analogue of the Lean Audit.lean file: type-check the headline    *)
(*  results and print the assumptions of the main semantic/deductive      *)
(*  checkpoints.  This file is intentionally an audit script rather than *)
(*  a proof development.                                                 *)
(* ===================================================================== *)

From SetTheory Require Import Fol Calculus Completeness Zf Equivalence PAHF.
From SetTheory Require Import BusyBeaver BusyBeaverMathlib.
From SetTheory Require Import Forward Reverse.

(* Full deductive equivalence between the Closure axiomatization and ZF. *)
Check T_iff_ZF.
Print Assumptions T_iff_ZF.
Check T_iff_ZF_via_theory_equiv.
Print Assumptions T_iff_ZF_via_theory_equiv.

Check ZF_implies_T.
Check T_implies_ZF.
Check T_ZF_same_models.
Print Assumptions T_ZF_same_models.

(* Generic calculus and completeness layer. *)
Check completeness.
Check prov_iff_valid.
Check completeness_inf.
Check theory_equiv.
Check BProv_ax.
Check BProv_of_Prov.
Check BProv_lift.
Check BProv_eqElim.
Check BProv_eqSym.
Check BProv_eqTrans.
Check BProv_theory_mono.
Check completeness_inf_context.
Print Assumptions prov_iff_valid.

Check soundness.
Check ClosureFO_of_ZF.
Print Assumptions ClosureFO_of_ZF.

(* PA/HF translation and finite-HF bridge. *)
Check PA.Formula.Ax_s.
Check PA.Formula.sat_axiom_s.
Check PA.Formula.BProv_lift.
Check PA.Formula.BProv_eqElim.
Check PA.Formula.BProv_context_cons.
Check PA.Formula.BProv_impI.
Check PA.Formula.BProv_impI_after_prefix.
Check PA.Formula.BProv_andI.
Check PA.Formula.BProv_botE.
Check PA.Formula.BProv_andE1.
Check PA.Formula.BProv_andE2.
Check PA.Formula.BProv_orI1.
Check PA.Formula.BProv_orI2.
Check PA.Formula.BProv_orE.
Check PA.Formula.BProv_allE.
Check PA.Formula.BProv_exI.
Check PA.Formula.soundness_BProv.
Check PA.Formula.translated_HF_axiom_sat_nat.
Check PA.Formula.translated_HFFin_axiom_sat_nat.
Check PA.Formula.standard_sat_translatedHFAx.
Check PA.Formula.standard_sat_translatedHFFinAx.

Check HFAx_s.
Check HFFinAx_s.
Check Sentences_HF.
Check Sentences_HFFin.
Check HF_finite_induction_form.
Check HF_finite_induction_form_spec.
Check prefix_below.
Check mem_prefix_below_iff.
Check prefix_below_self_eq.
Check sat_HF_finite_induction_standard.
Check standard_sat_HF.
Check standard_sat_HFFin.

Check firstOrderFiniteAdjunctionModel_of_HFFinAx_s.
Check formulaAt_induction_valid_finite_model.
Check translated_induction_sat_of_HFFinAx_s.
Check BProv_HFFin_translated_induction.
Check BProv_HFFin_translated_PA_axiom.
Check BProv_HFFin_of_translatedPAAx.
Check BProv_HFFin_of_BProv_translatedPAAx.
Check standard_sat_translatedPAAx.

Check ShallowBiInterpretation.
Check TheoryInterpretation.
Check TheoryInterpretation_comp.
Check setTheoryIdentityInterpretationOfAxiomProofs.
Check translatedPATheoryInHFFinInterpretation.
Check paInHFFinOfTranslatedPATheoryInterpretation.
Check paIdentityInterpretationOfAxiomProofs.
Check DeductiveBiInterpretationCertificate.
Check PAHFDeductiveBiInterpretationCertificate.
Check PAHFFinDeductiveBiInterpretationCertificate.
Check StandardModelInterpretationCertificateFor.
Check StandardModelHFInterpretationCertificate.
Check StandardModelFiniteInterpretationCertificate.
Check standardModelHFInterpretation.
Check standardModelFiniteInterpretation.
Check PA_standard_model_interpretable_with_HF_semantic.
Check PA_standard_model_interpretable_with_HFFin.
Check PA_biinterpretable_with_HF_standard.
Check PA_biinterpretable_with_HFFin_standard.

(* Rado-style busy-beaver interface and domination theorem. *)
Check BusyBeaver.IsSigma.
Check BusyBeaver.AttainableScore.
Check BusyBeaver.AttainableScoreAtMost.
Check BusyBeaver.sigma_mono_of_pos.
Check BusyBeaver.score_le_sigma_of_atMost.
Check BusyBeaver.sigma_eventually_dominates_every_total_recursive.
Check BusyBeaver.sigma_eventually_dominates_every_totalRecursiveInRadoModel.
Check BusyBeaver.sigma_eventually_dominates_every_totalRecursiveEventuallyInRadoModel.
Check BusyBeaver.sigma_eventually_dominates_every_totalRecursiveEventuallyLowerBoundInRadoModel.
Print Assumptions BusyBeaver.sigma_mono_of_pos.
Print Assumptions BusyBeaver.score_le_sigma_of_atMost.
Print Assumptions BusyBeaver.sigma_eventually_dominates_every_total_recursive.

(* Coq-side explicit counterpart of the Lean mathlib Turing-machine bridge. *)
Check BusyBeaverMathlib.positions_length_le_tape_length_of_read_true.
Check BusyBeaverMathlib.rado_positions_of_nat_offsets_nodup.
Check BusyBeaverMathlib.SupportedCompilerBridge.
Check BusyBeaverMathlib.supportedCompilerBridge_has_lowerBoundCompiler.
Check BusyBeaverMathlib.sigma_eventually_dominates_every_supported_total_recursive.
Print Assumptions
  BusyBeaverMathlib.sigma_eventually_dominates_every_supported_total_recursive.

Print Assumptions PA.Formula.sat_axiom_s.
Print Assumptions PA.Formula.soundness_BProv.
Print Assumptions sat_HF_model.
Print Assumptions standard_sat_HF.
Print Assumptions standard_sat_HFFin.
Print Assumptions PA_standard_model_interpretable_with_HF_semantic.
Print Assumptions PA_standard_model_interpretable_with_HFFin.
Print Assumptions PA_biinterpretable_with_HF_standard.
Print Assumptions PA_biinterpretable_with_HFFin_standard.

(* Self-contained shallow forward/reverse trade files. *)
Check Forward.Pairing.
Check Forward.Union.
Check Forward.Replacement.
Check Forward.Infinity.
Print Assumptions Forward.Pairing.

Check Reverse.Closure_holds.
Print Assumptions Reverse.Closure_holds.
