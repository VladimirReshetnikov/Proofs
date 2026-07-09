(* ===================================================================== *)
(*  Audit.v                                                              *)
(*                                                                       *)
(*  Coq analogue of the Lean Audit.lean file: type-check the headline    *)
(*  results and print the assumptions of the main semantic/deductive      *)
(*  checkpoints.  This file is intentionally an audit script rather than *)
(*  a proof development.                                                 *)
(* ===================================================================== *)

From SetTheory Require Import Fol Calculus Completeness Zf Equivalence PAHF.
From SetTheory Require Import BusyBeaver BusyBeaverMathlib BusyBeaverKnownValues.
From SetTheory Require Import Forward Reverse RiemannHypothesis.

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
Check BProv_context_cons.
Check BProv_impI.
Check BProv_impI_after_prefix.
Check BProv_andI.
Check BProv_botE.
Check BProv_andE1.
Check BProv_andE2.
Check BProv_orI1.
Check BProv_orI2.
Check BProv_orE.
Check BProv_orE_after_prefix.
Check BProv_allE.
Check BProv_exI.
Check BProv_allI_of_sentences.
Check BProv_exE_of_sentences.
Check completeness_inf_context.
Print Assumptions prov_iff_valid.

Check soundness.
Check ClosureFO_of_ZF.
Print Assumptions ClosureFO_of_ZF.

(* PA/HF translation and finite-HF bridge. *)
Check PA.Term.addRightNumeral.
Check PA.Term.mulRightNumeral.
Check PA.Term.rename_numeral.
Check PA.Term.subst_numeral.
Check PA.Term.subst_subst_numeral.
Check PA.Term.addRightNumeral_numeral.
Check PA.Term.subst_comp.
Check PA.Term.subst_rename_succ_up.
Check PA.Term.subst_ext_free.
Check PA.Term.subst_id.
Check PA.Formula.Ax_s.
Check PA.Formula.sat_axiom_s.
Check PA.Formula.Sentences.
Check PA.Formula.rename_eq_of_sentence.
Check PA.Formula.term_subst_var_rename.
Check PA.Formula.term_subst_instTerm_var.
Check PA.Formula.subst_var_rename.
Check PA.Formula.subst_instTerm_var.
Check PA.Formula.subst_comp.
Check PA.Formula.subst_rename_succ_up.
Check PA.Formula.subst_ext_free.
Check PA.Formula.subst_id.
Check PA.Formula.subst_eq_of_sentence.
Check PA.Formula.term_subst_instTerm_rename_succ.
Check PA.Formula.subst_instTerm_rename_succ.
Check PA.Formula.subst_instTerm_subst_up.
Check PA.Formula.map_subst_rename_succ_up.
Check PA.Formula.term_substZero_rename_succ.
Check PA.Formula.term_substSuccVar_rename_succ.
Check PA.Formula.rename_hfMemAt.
Check PA.Formula.leConstAt.
Check PA.Formula.succPredAt.
Check PA.Formula.zeroOrSuccPredAt.
Check PA.Formula.betaDiv2StepsThroughConstAt.
Check PA.Formula.leConstAt_nat.
Check PA.Formula.succPredAt_nat.
Check PA.Formula.zeroOrSuccPredAt_nat.
Check PA.Formula.betaDiv2StepsThroughConstAt_nat.
Check PA.Formula.BetaShiftTailThrough.
Check PA.Formula.boolTermAt.
Check PA.Formula.div2StepTermAt.
Check PA.Formula.boolTermAt_nat.
Check PA.Formula.div2StepTermAt_nat.
Check PA.Formula.leTermAt_nat.
Check PA.Formula.ltTermAt_nat.
Check PA.Formula.BProv_Ax_s_zeroOrSuccPredAt_all.
Check PA.Formula.BProv_Ax_s_zeroOrSuccPred_term.
Check PA.Formula.BProv_Ax_s_zeroOrSuccPredAt.
Check PA.Formula.BProv_Ax_s_add_eq_zero_left_all.
Check PA.Formula.BProv_Ax_s_add_eq_zero_left_terms.
Check PA.Formula.BProv_Ax_s_leConstAt_of_leAt_eqConst.
Check PA.Formula.BProv_Ax_s_eqConstAt_zero_of_leConstAt_zero.
Check PA.Formula.BProv_Ax_s_eqConstAt_zero_of_leAt_eqConst_zero.
Check PA.Formula.BProv_Ax_s_leConstAt_succ_cases.
Check PA.Formula.BProv_Ax_s_addRightNumeral.
Check PA.Formula.BProv_Ax_s_mulRightNumeral.
Check PA.Formula.BProv_Ax_s_addNumerals.
Check PA.Formula.BProv_Ax_s_mulRightNumeral_numeral.
Check PA.Formula.BProv_Ax_s_mulNumerals.
Check PA.Formula.BProv_Ax_s_leAt_of_eqConst.
Check PA.Formula.BProv_Ax_s_ltAt_of_eqConst.
Check PA.Formula.BProv_Ax_s_ltConst_of_eqConst.
Check PA.Formula.BProv_Ax_s_ltConst_closed.
Check PA.Formula.BProv_Ax_s_dvdAt_of_eqConst_mul.
Check PA.Formula.BProv_Ax_s_dvdAt_of_eqConst.
Check PA.Formula.BProv_Ax_s_boolAt_of_eqConst.
Check PA.Formula.BProv_Ax_s_div2StepAt_of_eqConst.
Check PA.Formula.BProv_Ax_s_div2StepAt_zero_one_bot.
Check PA.Formula.BProv_Ax_s_div2StepAt_zero_half_zero.
Check PA.Formula.BProv_Ax_s_div2StepAt_closedSubst.
Check PA.Formula.BProv_Ax_s_div2StepAt_constValueHalfSubst_of_eqConst.
Check PA.Formula.BProv_Ax_s_remAt_of_eqConst.
Check PA.Formula.BProv_Ax_s_remAt_constMod_of_eqConst.
Check PA.Formula.BProv_Ax_s_remAt_constRemMod_of_eqConst.
Check PA.Formula.BProv_Ax_s_betaModTerm_of_eqConst.
Check PA.Formula.BProv_Ax_s_betaModTerm_constIdx_of_eqConst.
Check PA.Formula.BProv_Ax_s_betaAt_of_eqConst.
Check PA.Formula.BProv_Ax_s_betaAt_constOutSubst_of_eqConst.
Check PA.Formula.BProv_Ax_s_betaAt_constOutIdxSubst_of_eqConst.
Check PA.Formula.BProv_Ax_s_betaAt_constIdxSubst_of_eqConst.
Check PA.Formula.BProv_Ax_s_betaAtConstIdx_of_eqConst.
Check PA.Formula.BProv_Ax_s_betaAtSuccIdx_of_eqConst.
Check PA.Formula.BProv_Ax_s_betaAtSuccIdx_constOutSubst_of_eqConst.
Check PA.Formula.BProv_Ax_s_betaDiv2StepWitnessAt_of_eqConst.
Check PA.Formula.BProv_Ax_s_betaDiv2BitAt_of_eqConst.
Check PA.Formula.BProv_Ax_s_betaAt_of_eqConst_entry.
Check PA.Formula.BProv_Ax_s_betaAt_constOutSubst_of_eqConst_entry.
Check PA.Formula.BProv_Ax_s_betaAt_constOutIdxSubst_of_eqConst_entry.
Check PA.Formula.BProv_Ax_s_betaAtConstIdx_of_eqConst_entry.
Check PA.Formula.BProv_Ax_s_betaAtSuccIdx_of_eqConst_entry.
Check PA.Formula.BProv_Ax_s_betaAtSuccIdx_constOutSubst_of_eqConst_entry.
Check PA.Formula.BProv_Ax_s_betaDiv2StepWitnessAt_of_eqConst_step.
Check PA.Formula.BProv_Ax_s_betaDiv2BitAt_of_eqConst_step.
Check PA.Formula.BProv_Ax_s_betaDiv2StepWitnessAt_body_zero_next_zero.
Check PA.Formula.BProv_Ax_s_betaDiv2BitAt_body_zero_one_bot.
Check PA.Formula.BProv_Ax_s_betaDiv2BitAt_current_zero_bot.
Check PA.Formula.BProv_Ax_s_betaDiv2StepsThroughAt_zero_of_eqConst_step.
Check PA.Formula.BProv_Ax_s_betaDiv2StepsThroughConstAt_zero_of_eqConst_step.
Check PA.Formula.BProv_Ax_s_betaDiv2StepsThroughConstAt_succ_of_eqConst_step.
Check PA.Formula.BProv_Ax_s_betaDiv2StepsThroughAt_of_const_eqConst.
Check PA.Formula.BProv_Ax_s_betaDiv2StepsThroughConstAt_of_eqConst_trace.
Check PA.Formula.BProv_Ax_s_betaDiv2StepsThroughAt_of_eqConst_trace.
Check PA.Formula.remTermTermAt.
Check PA.Formula.betaModTermTerm.
Check PA.Formula.betaTermTermAt.
Check PA.Formula.betaTermTermAtConstIdx.
Check PA.Formula.betaTermTermAtSuccIdx.
Check PA.Formula.betaTermAt_eq_betaTermTermAt_var.
Check PA.Formula.BProv_Ax_s_remTermTermAt_of_eq_add_mul_terms.
Check PA.Formula.BProv_Ax_s_remTermTermAt_zero_modulus_one.
Check PA.Formula.BProv_Ax_s_ltTermAt_of_remTermTermAt.
Check PA.Formula.BProv_Ax_s_eq_zero_of_ltTermAt_one.
Check PA.Formula.BProv_Ax_s_eq_zero_of_remTermTermAt_eq_one.
Check PA.Formula.BProv_Ax_s_betaModTermTerm_eq_one_of_eq_step_zero.
Check PA.Formula.BProv_Ax_s_betaTermTermAt_of_rem.
Check PA.Formula.BProv_Ax_s_betaTermTermAt_zero_of_eq_step_zero.
Check PA.Formula.BProv_Ax_s_eq_zero_of_betaTermTermAt_eq_step_zero.
Check PA.Formula.betaModTermTerm_nat.
Check PA.Formula.remTermTermAt_nat.
Check PA.Formula.betaTermTermAt_nat_entry.
Check PA.Formula.betaTermTermAtSuccIdx_nat_entry.
Check PA.Formula.betaDiv2StepWitnessTermAt.
Check PA.Formula.betaDiv2StepWitnessTermAt_nat.
Check PA.Formula.betaDiv2StepWitnessTermSuccIdxAt.
Check PA.Formula.betaDiv2StepsThroughTermAt.
Check PA.Formula.betaDiv2StepsThroughTermAt_nat.
Check PA.Formula.betaDiv2StepsThroughTermTermAt.
Check PA.Formula.betaDiv2StepsThroughTermTermAt_nat.
Check PA.Formula.betaShiftTailThroughTermAt.
Check PA.Formula.betaShiftTailThroughTermAt_nat.
Check PA.Formula.betaShiftTailExistsTermAt.
Check PA.Formula.betaShiftTailExistsTermAt_nat.
Check PA.Formula.betaShiftTailThroughConstAt.
Check PA.Formula.betaShiftTailThroughConstAt_nat.
Check PA.Formula.betaDiv2BitTermAt.
Check PA.Formula.betaDiv2BitTermAt_nat.
Check PA.Formula.betaDiv2BitOneTermExAt.
Check PA.Formula.betaDiv2BitOneTermExAt_nat.
Check PA.Formula.BProv_Ax_s_betaTermTermAtConstIdx_of_beta.
Check PA.Formula.BProv_Ax_s_hfMemAt_bitOneEx_of_bit.
Check PA.Formula.BProv_Ax_s_hfMemAt_of_closed_components.
Check PA.Formula.BProv_Ax_s_hfMemAt_of_closed_bit_components.
Check PA.Formula.BProv_Ax_s_hfMemTermAt_entry_of_betaTermTermAt_zero.
Check PA.Formula.BProv_Ax_s_betaShiftTailThroughTermAt_entry_of_leTerm.
Check PA.Formula.BProv_Ax_s_hfMemAt_entryComponent_of_eqConst_entry.
Check PA.Formula.BProv_Ax_s_hfMemAt_bitComponent_of_eqConst_bit.
Check PA.Formula.BProv_Ax_s_hfMemAt_stepsComponent_of_eqConst_trace.

(* PA statement of the Mertens/Littlewood form of RH. *)
Check notF.
Check remTermTermAt.
Check betaTermTermAt.
Check completePrimeFactorizationTraceAt.
Check mobiusPositiveTermAt.
Check mobiusNegativeTermAt.
Check mertensCountsTraceAt.
Check powTraceAt.
Check powRelAt.
Check mertensRiemannHypothesisBody.
Check mertensRiemannHypothesisSentence.
Check mertensRiemannHypothesisSentence_sentence.
Print Assumptions mertensRiemannHypothesisSentence_sentence.
Check PA.Formula.BProv_Ax_s_hfMemAt_of_eqConst_trace_with_steps.
Check PA.Formula.BProv_Ax_s_hfMemAt_of_eqConst_trace.
Check PA.Formula.BProv_Ax_s_hfMemAt_of_eqConst_mem.
Check PA.Formula.BProv_Ax_s_hfMemAt_bot_of_opened_final_current_zero.
Check PA.Formula.BProv_Ax_s_HF_empty_zero_body_of_member_bot.
Check PA.Formula.BProv_Ax_s_translated_HF_empty_of_zero_body.
Check PA.Formula.BProv_Ax_s_translated_HF_empty_of_zero_member_bot.
Check PA.Formula.hfContextAt.
Check PA.Formula.translateHFContext.
Check PA.Formula.translateHFContext_eq_hfContextAt_id.
Check PA.Formula.hfFormulaAt_ext.
Check PA.Formula.hfFormulaAt_ext_free.
Check PA.Formula.hfFormulaAt_source_rename.
Check PA.Formula.rename_hfFormulaAt.
Check PA.Formula.hfFormulaAt_rename_succ.
Check PA.Formula.hfContextAt_rename_succ.
Check PA.Formula.hfContextAt_cons_rename_succ.
Check PA.Formula.subst_instTerm_var_hfFormulaAt.
Check PA.Formula.hfFormulaAt_eq_translateHFFormula_of_HF_sentence.
Check PA.Formula.Prov_hfFormulaAt_of_Prov.
Check PA.Formula.Prov_subst.
Check PA.Formula.BProv_hfFormulaAt_of_BProv_HFFin.
Check PA.Formula.BProv_translateHFFormula_of_BProv_HFFin.
Check PA.Formula.BProv_lift.
Check PA.Formula.BProv_eqElim.
Check PA.Formula.BProv_eqRefl.
Check PA.Formula.BProv_eqSym.
Check PA.Formula.BProv_eqTrans.
Check PA.Formula.BProv_eq_congr_term.
Check PA.Formula.BProv_eq_congr_succ.
Check PA.Formula.BProv_eq_congr_add_left.
Check PA.Formula.BProv_eq_congr_add_right.
Check PA.Formula.BProv_eq_congr_add.
Check PA.Formula.BProv_eq_congr_mul_left.
Check PA.Formula.BProv_eq_congr_mul_right.
Check PA.Formula.BProv_eq_congr_mul.
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
Check PA.Formula.BProv_allI_of_sentences.
Check PA.Formula.BProv_exE_of_sentences.
Check PA.Formula.BProv_weaken_nil.
Check PA.Formula.BProv_ass.
Check PA.Formula.BProv_rename_of_sentences.
Check PA.Formula.BProv_subst_of_sentences.
Check PA.Formula.BProv_closeN_allE_rename.
Check PA.Formula.BProv_sealPA_allE_rename.
Check PA.Formula.BProv_inductionForm_mp.
Check PA.Formula.BProv_Ax_s_of_sealPA_rename.
Check PA.Formula.BProv_Ax_s_succInj_rename.
Check PA.Formula.BProv_Ax_s_succInj.
Check PA.Formula.BProv_Ax_s_succInj_terms.
Check PA.Formula.BProv_Ax_s_zeroNotSucc_rename.
Check PA.Formula.BProv_Ax_s_zeroNotSucc.
Check PA.Formula.BProv_Ax_s_zeroNotSucc_term.
Check PA.Formula.BProv_Ax_s_addZero_rename.
Check PA.Formula.BProv_Ax_s_addZero.
Check PA.Formula.BProv_Ax_s_addZero_term.
Check PA.Formula.BProv_Ax_s_addSucc_rename.
Check PA.Formula.BProv_Ax_s_addSucc.
Check PA.Formula.BProv_Ax_s_addSucc_terms.
Check PA.Formula.BProv_Ax_s_mulZero_rename.
Check PA.Formula.BProv_Ax_s_mulZero.
Check PA.Formula.BProv_Ax_s_mulZero_term.
Check PA.Formula.BProv_Ax_s_mulSucc_rename.
Check PA.Formula.BProv_Ax_s_mulSucc.
Check PA.Formula.BProv_Ax_s_mulSucc_terms.
Check PA.Formula.BProv_Ax_s_inductionForm_rename.
Check PA.Formula.BProv_Ax_s_inductionForm.
Check PA.Formula.BProv_Ax_s_induction_rule.
Check PA.Formula.TranslatedHFAxiomProofs.
Check PA.Formula.TranslatedHFFinAxiomProofs.
Check PA.Formula.BProv_Ax_s_of_translatedHFAx_of_proofs.
Check PA.Formula.BProv_Ax_s_of_translatedHFFinAx_of_proofs.
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
Check rename_HF_emptyAt.
Check rename_HF_adjoinAt.
Check rename_HF_succAt.
Check rename_HF_singleAt.
Check rename_HF_upairAt.
Check rename_HF_kpairAt.
Check rename_HF_pairMemAt.
Check rename_HF_pairFunctionalAt.
Check rename_HF_pairKeysBelowSuccAt.
Check rename_HF_pairTotalBelowSuccAt.
Check rename_HF_pairSuccStepAt.
Check rename_HF_pairBaseAt.
Check rename_HF_pairZeroBaseAt.
Check rename_HF_succRecApproxAt.
Check rename_addGraphAt.
Check rename_mulStepAt.
Check rename_mulRecApproxAt.
Check rename_mulGraphAt.
Check termGraphAt_map_ext_free.
Check termGraphAt_PA_rename.
Check termGraphAt_rename.
Check termGraphAt_inst_out.
Check formulaAt_PA_rename.
Check rename_domainForm_up.
Check formulaAt_rename.
Check formulaAt_rename_succ_upVarMap.
Check formulaAt_subst_instTerm_var.
Check formulaAt_map_ext_free.
Check formulaAt_eq_translateFormula_of_PA_sentence.
Check translateContextAt.
Check translateContextAt_id.
Check translateContextAt_rename_succ_upVarMap.
Check mem_translateContextAt_of_mem.
Check BProv_translate_allE_raw.
Check BProv_formulaAt_ass.
Check BProv_formulaAt_ax.
Check domainContextAt.
Check rename_domainForm_inst.
Check rename_domainForm_inst_zero.
Check domainContextAt_rename.
Check mem_domainContextAt.
Check mem_domainContextAt_mono.
Check BProv_mono_domainContextAt.
Check domainContextAt_upVarMap_succ.
Check BProv_domainContextAt_var.
Check BProv_formulaAt_impI.
Check BProv_formulaAt_impE.
Check BProv_formulaAt_botE.
Check BProv_formulaAt_lem.
Check BProv_formulaAt_eqRefl_var.
Check formulaAt_eqRefl_zero_valid_of_HFFinAx_s.
Check BProv_HFFin_formulaAt_eqRefl_zero_nil.
Check BProv_HFFin_formulaAt_eqRefl_zero.
Check BProv_formulaAt_eq_var_of_eq.
Check BProv_formulaAt_andI.
Check BProv_formulaAt_andE1.
Check BProv_formulaAt_andE2.
Check BProv_formulaAt_orI1.
Check BProv_formulaAt_orI2.
Check BProv_formulaAt_orE.
Check BProv_formulaAt_eq_of_termGraphsAt.
Check BProv_termGraphAt_eqElim_out.
Check BProv_formulaAt_eqRefl_of_termGraphAt.
Check BProv_eq_of_formulaAt_eq_var.
Check BProv_formulaAt_eqElim_var.
Check BProv_formulaAt_allI_raw.
Check BProv_formulaAt_allI.
Check BProv_formulaAt_allI_domainContext.
Check BProv_formulaAt_allI_domainContext_of_sentences.
Check BProv_formulaAt_allE_raw.
Check BProv_formulaAt_allE_var.
Check BProv_formulaAt_allE_slot_context.
Check BProv_formulaAt_slot_eqElim_context.
Check BProv_formulaAt_allE_equal_slot_context.
Check BProv_formulaAt_allE_var_context.
Check BProv_formulaAt_allE_var_domainContext.
Check BProv_formulaAt_exI_raw.
Check BProv_formulaAt_exI_var.
Check BProv_formulaAt_exI_slot_context.
Check BProv_formulaAt_exI_equal_slot_context.
Check BProv_formulaAt_exI_var_context.
Check BProv_formulaAt_exI_var_domainContext.
Check BProv_formulaAt_exE_raw.
Check BProv_formulaAt_exE.
Check BProv_formulaAt_exE_domainContext_of_sentences.
Check BProv_formulaAt_of_Prov_with_term_rules.
Check BProv_formulaAt_of_PA_BProv_with_term_rules.

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

(* Proved theorems and executable definitions. *)
Check BusyBeaverMathlib.positions_length_le_tape_length_of_read_true.
Check BusyBeaverMathlib.rado_positions_of_nat_offsets_nodup.
Check BusyBeaverMathlib.supportedCompilerBridge_has_lowerBoundCompiler.
Check BusyBeaverMathlib.sigma_eventually_dominates_every_supported_total_recursive.
Check BusyBeaverMathlib.initInputTape.
Check BusyBeaverMathlib.initInputTape_zero.
Check BusyBeaverMathlib.initInputTape_succ.
Check BusyBeaverMathlib.initInputTape_read_nat.
Check BusyBeaverMathlib.initInputTape_read_neg.
Check BusyBeaverMathlib.initInputTape_matches_tm0_init.
Check BusyBeaverMathlib.InitThenTM0State.
Check BusyBeaverMathlib.initThenTM0ToTypedRado.
Check BusyBeaverMathlib.liftSimCfg.
Check BusyBeaverMathlib.liftSimCfg_step.
Check BusyBeaverMathlib.liftSimCfg_reaches.
Check BusyBeaverMathlib.initThenTM0Start.
Check BusyBeaverMathlib.initThenTM0WriteCfg.
Check BusyBeaverMathlib.initThenTM0ReturnCfg.
Check BusyBeaverMathlib.initThenTM0SimInitCfg.
Check BusyBeaverMathlib.initThenTM0_write_reaches.
Check BusyBeaverMathlib.initThenTM0_return_reaches.
Check BusyBeaverMathlib.initThenTM0_reaches_sim_init.
Check BusyBeaverMathlib.tm0_eval_to_init_wrapper_lowerBound.
Check BusyBeaverMathlib.tm2to1_trInit_length_pos.
Check BusyBeaverMathlib.encoded_partrec_input_length_pos.
Check BusyBeaverMathlib.tm2to1_trInit_length_le_succ.
Check BusyBeaverMathlib.encoded_partrec_input_length_le.
Check BusyBeaverMathlib.TM1to1EncodedInput_length.
Check BusyBeaverMathlib.partrecToTM1Encoding_width_pos.

(* Encoded-input budget arithmetic: real theorems, ported from the Lean
   proofs in lean/SetTheory/BusyBeaverMathlib.lean. *)
Check BusyBeaverMathlib.linear_mul_le_two_pow_pred_of_large.
Check BusyBeaverMathlib.nat_size_linear_le_self_of_large.
Check BusyBeaverMathlib.init_wrapper_state_count_le_linear.
Check BusyBeaverMathlib.init_wrapper_state_count_le_linear_size.
Print Assumptions BusyBeaverMathlib.linear_mul_le_two_pow_pred_of_large.
Print Assumptions BusyBeaverMathlib.nat_size_linear_le_self_of_large.
Print Assumptions BusyBeaverMathlib.init_wrapper_state_count_le_linear_size.

(* ------------------------------------------------------------------ *)
(*  Assumption interfaces and placeholders, NOT theorems.              *)
(*                                                                     *)
(*  The Coq development has no mathlib, so the recursive-function /    *)
(*  Turing-machine compiler connection proved in Lean is packaged as   *)
(*  explicit assumption records (their fields are hypotheses consumers *)
(*  must discharge), and the Lean `Fintype.card` / mathlib translation *)
(*  lengths appear only as numeric placeholder Definitions.  Checking  *)
(*  them below documents the interface; it does not certify any proof. *)
(* ------------------------------------------------------------------ *)
Check BusyBeaverMathlib.SupportedCompilerBridge.                (* assumption record *)
Check BusyBeaverMathlib.totalRecursiveMathlib_init_wrapper_attainable_lowerBound_with_encoding.
                                       (* projection of TotalRecursiveMathlibBridge *)
Check BusyBeaverMathlib.fintype_card_sum.                       (* numeric placeholder *)
Check BusyBeaverMathlib.trPosNum_length.                        (* numeric placeholder *)
Check BusyBeaverMathlib.trNum_length.                           (* numeric placeholder *)
Check BusyBeaverMathlib.trNat_length.                           (* numeric placeholder *)
Check BusyBeaverMathlib.trList_singleton_length.                (* numeric placeholder *)
Check BusyBeaverMathlib.initThenTM0State_card.                  (* numeric placeholder *)

(* Conditional consequences of the assumption records above. *)
Check BusyBeaverMathlib.totalRecursiveMathlib_hasEventuallyAtMostLowerBoundCompiler.
Check BusyBeaverMathlib.sigma_eventually_dominates_every_totalRecursiveMathlib.
Print Assumptions
  BusyBeaverMathlib.sigma_eventually_dominates_every_supported_total_recursive.
Print Assumptions
  BusyBeaverMathlib.sigma_eventually_dominates_every_totalRecursiveMathlib.

(* Concrete small-state busy-beaver witnesses and certificate wrappers. *)
Check BusyBeaverKnownValues.sigma1Champion.
Check BusyBeaverKnownValues.sigma2Champion.
Check BusyBeaverKnownValues.sigma3Champion.
Check BusyBeaverKnownValues.sigma4Champion.
Check BusyBeaverKnownValues.sigma1Champion_haltsWithScore.
Check BusyBeaverKnownValues.sigma2Champion_haltsWithScore.
Check BusyBeaverKnownValues.sigma3Champion_haltsWithScore.
Check BusyBeaverKnownValues.sigma4Champion_haltsWithScore.
Check BusyBeaverKnownValues.attainableScore_one_one.
Check BusyBeaverKnownValues.attainableScore_two_four.
Check BusyBeaverKnownValues.attainableScore_three_six.
Check BusyBeaverKnownValues.attainableScore_four_thirteen.
Check BusyBeaverKnownValues.a028444_prefix_lower_bounds_through_four.
Check BusyBeaverKnownValues.upperBound_one.
Check BusyBeaverKnownValues.ExactScore.
Check BusyBeaverKnownValues.ExactScore.sigma_eq.
Check BusyBeaverKnownValues.exactScore_one.
Check BusyBeaverKnownValues.sigma_one_eq_one.
Check BusyBeaverKnownValues.A028444UpperBoundsThroughFour.
Check BusyBeaverKnownValues.A028444UpperBoundsTwoThroughFour.
Check BusyBeaverKnownValues.A028444UpperBoundsThroughFour.of_twoThroughFour.
Check BusyBeaverKnownValues.a028444_values_through_four_from_upperBounds.
Check BusyBeaverKnownValues.a028444_values_through_four_from_remainingUpperBounds.
Print Assumptions BusyBeaverKnownValues.upperBound_one.
Print Assumptions
  BusyBeaverKnownValues.a028444_values_through_four_from_remainingUpperBounds.

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
