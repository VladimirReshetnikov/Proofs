/-
  Audit.lean — the Lean analogue of the Coq files' trailing `Check` /
  `Print Assumptions` commands: type-check the headline results and print
  the axioms each depends on.  Expected: only Lean's standard classical
  axioms (`Classical.choice`, `propext`, `Quot.sound`) — no `sorry`.
-/
import SetTheory

open SetTheory

-- the headline: full deductive equivalence T ⊢ φ ⟺ ZF ⊢ φ
#check @T_iff_ZF
#print axioms T_iff_ZF
#print axioms T_iff_ZF_via_theory_equiv

-- syntactic directions and same-models
#check @ZF_implies_T
#check @T_implies_ZF
#check @T_ZF_same_models
#print axioms T_ZF_same_models

-- Gödel completeness layer
#check @completeness
#check @prov_iff_valid
#check @completeness_inf
#check @theory_equiv
#print axioms prov_iff_valid

-- calculus soundness and the deep reverse (internal recursion theorem)
#check @soundness
#check @ClosureFO_of_ZF
#print axioms ClosureFO_of_ZF

-- PA/HF Ackermann/von-Neumann semantic bi-interpretability checkpoint
#check @PA.Formula.Ax
#check @PA.Formula.sat_axiom
#check @PA.Formula.Ax_s
#check @PA.Formula.sat_axiom_s
#check @PA.Term.Free
#check @PA.Term.free_lt_bound
#check @PA.Term.numeral
#check @PA.Term.numeralValue
#check @PA.Term.eval_numeral
#check @PA.Term.numeralValue_natModel
#check @PA.Term.eval_numeral_natModel
#check @PA.Formula.Free
#check @PA.Formula.Sentence
#check @PA.Formula.sealPA_sentence
#check @PA.Formula.sentence_ax_s
#check @PA.Formula.leAt
#check @PA.Formula.ltAt
#check @PA.Formula.dvdAt
#check @PA.Formula.eqConstAt
#check @PA.Formula.zeroAt
#check @PA.Formula.oneAt
#check @PA.Formula.twoAt
#check @PA.Formula.nonzeroAt
#check @PA.Formula.boolAt
#check @PA.Formula.doubleEqAt
#check @PA.Formula.oddDoubleEqAt
#check @PA.Formula.div2StepAt
#check @PA.Formula.remAt
#check @PA.Formula.betaModTerm
#check @PA.Formula.betaAt
#check @PA.Formula.betaAtConstIdx
#check @PA.Formula.betaAtSuccIdx
#check @PA.Formula.BetaModulus
#check @PA.Formula.BetaEntry
#check @PA.Formula.betaFact
#check @PA.Formula.BetaModuliProduct
#check @PA.Formula.BetaDiv2Step
#check @PA.Formula.BetaDiv2StepsThrough
#check @PA.Formula.BetaDiv2Bit
#check @PA.Formula.HFMemTrace
#check @PA.Formula.betaDiv2StepWitnessAt
#check @PA.Formula.betaDiv2StepAt
#check @PA.Formula.betaDiv2StepsThroughAt
#check @PA.Formula.betaDiv2BitAt
#check @PA.Formula.hfMemAt
#check @PA.Formula.leAt_nat
#check @PA.Formula.ltAt_nat
#check @PA.Formula.dvdAt_nat
#check @PA.Formula.eqConstAt_nat
#check @PA.Formula.zeroAt_nat
#check @PA.Formula.oneAt_nat
#check @PA.Formula.twoAt_nat
#check @PA.Formula.nonzeroAt_nat
#check @PA.Formula.boolAt_nat
#check @PA.Formula.doubleEqAt_nat
#check @PA.Formula.oddDoubleEqAt_nat
#check @PA.Formula.div2StepAt_nat
#check @PA.Formula.betaModTerm_nat
#check @PA.Formula.remAt_nat
#check @PA.Formula.betaAt_nat
#check @PA.Formula.betaAtConstIdx_nat
#check @PA.Formula.betaAtSuccIdx_nat
#check @PA.Formula.betaAt_nat_entry
#check @PA.Formula.betaAtConstIdx_nat_entry
#check @PA.Formula.betaAtSuccIdx_nat_entry
#check @PA.Formula.betaDiv2StepWitnessAt_nat
#check @PA.Formula.betaDiv2StepAt_nat
#check @PA.Formula.betaDiv2StepsThroughAt_nat
#check @PA.Formula.betaDiv2BitAt_nat
#check @PA.Formula.hfMemAt_nat_trace
#check @PA.Formula.betaFact_pos
#check @PA.Formula.BetaModuliProduct_pos
#check @PA.Formula.dvd_betaFact_of_pos_le
#check @PA.Formula.BetaModulus_pos
#check @PA.Formula.BetaModulus_coprime_step
#check @PA.Formula.BetaModulus_sub
#check @PA.Formula.BetaModulus_pair_coprime_of_dvd_step
#check @PA.Formula.BetaModulus_pair_coprime_of_lt_le
#check @PA.Formula.BetaModuliProduct_coprime_modulus_of_le
#check @PA.Formula.BetaModuliProduct_coprime_next_of_le
#check @PA.Formula.int_bezout_gcd
#check @PA.Formula.coprime_int_bezout
#check @PA.Formula.int_nonneg_shift
#check @PA.Formula.int_crt_shape_left
#check @PA.Formula.int_crt_shape_right
#check @PA.Formula.crt_two_mod
#check @PA.Formula.BetaEntry_value_lt
#check @PA.Formula.BetaEntry_mod_eq
#check @PA.Formula.BetaEntry_of_mod_eq
#check @PA.Formula.BetaModuliProduct_dvd_of_lt
#check @PA.Formula.mod_eq_of_mod_BetaModuliProduct_eq
#check @PA.Formula.BetaEntry_of_mod_BetaModuliProduct_eq
#check @PA.Formula.BetaModulus_pair_coprime_of_lt_le_mul_betaFact
#check @PA.Formula.BetaModuliProduct_coprime_modulus_of_le_mul_betaFact
#check @PA.Formula.BetaModuliProduct_coprime_next_of_le_mul_betaFact
#check @PA.Formula.beta_entries_exist_lt_mul_betaFact
#check @PA.Formula.beta_entries_exist_through_mul_betaFact
#check @PA.Formula.shiftRight_lt_trace_modulus
#check @PA.Formula.div2_step_shiftRight
#check @PA.Formula.div2_step_shiftRight_one
#check @PA.Formula.HFMemTrace_exists_of_mem
#check @PA.Formula.BetaEntry_functional
#check @PA.Formula.BetaDiv2Step_div_two
#check @PA.Formula.BetaDiv2Step_bit_one_testBit_zero
#check @PA.Formula.HFMemTrace_entry_shiftRight
#check @PA.Formula.HFMemTrace_mem
#check @PA.Formula.hfMemAt_sound
#check @PA.Formula.hfMemAt_complete
#check @PA.Formula.hfMemAt_exact
#check @PA.Formula.hfMemAt_free
#check @PA.Formula.hfUpVarMap
#check @PA.Formula.hfFormulaAt
#check @PA.Formula.hfFormulaAt_free
#check @PA.Formula.translateHFFormula
#check @PA.Formula.hfFormulaAt_exact
#check @PA.Formula.translateHFFormula_exact
#check @PA.Formula.translated_HF_axiom_sat_nat
#check @PA.Formula.hfFormulaAt_sentence_of_HF_sentence
#check @PA.Formula.translateHFFormula_sentence_of_HF_sentence
#check @PA.Formula.translated_HF_axiom_sentence
#check @PA.Formula.translatedHFAx
#check @PA.Formula.Sentences_translatedHFAx
#check @PA.Formula.standard_sat_translatedHFAx
#check @AckermannHF.HFAx_s
#check @AckermannHF.Sentences_HF
#check @AckermannHF.eq_empty_iff_no_mem
#check @AckermannHF.exists_mem_of_ne_empty
#check @AckermannHF.exists_max_mem_of_ne_empty
#check @AckermannHF.HF_emptyAt_empty
#check @AckermannHF.HF_adjoinAt_adjoin
#check @AckermannHF.HF_succAt_spec
#check @AckermannHF.single_spec
#check @AckermannHF.upair_spec
#check @AckermannHF.kpair_mem
#check @AckermannHF.kpair_injective
#check @AckermannHF.HF_singleAt_spec
#check @AckermannHF.HF_upairAt_spec
#check @AckermannHF.HF_kpairAt_spec
#check @AckermannHF.HF_pairMemAt_spec
#check @AckermannHF.PairFunctional
#check @AckermannHF.PairKeysBelowSucc
#check @AckermannHF.PairTotalBelowSucc
#check @AckermannHF.PairSuccStep
#check @AckermannHF.SuccRecApprox
#check @AckermannHF.HF_pairFunctionalAt_spec
#check @AckermannHF.HF_pairKeysBelowSuccAt_spec
#check @AckermannHF.HF_pairTotalBelowSuccAt_spec
#check @AckermannHF.HF_pairSuccStepAt_spec
#check @AckermannHF.HF_pairBaseAt_spec
#check @AckermannHF.HF_pairZeroBaseAt_spec
#check @AckermannHF.HF_succRecApproxAt_spec
#check @AckermannHF.HF_subsetAt_spec
#check @AckermannHF.HF_transitiveAt_spec
#check @AckermannHF.HF_memTotalOnAt_spec
#check @AckermannHF.HF_ordinalLikeAt_spec
#check @AckermannHF.HF_emptyAt_free
#check @AckermannHF.HF_adjoinAt_free
#check @AckermannHF.HF_pairMemAt_free
#check @AckermannHF.HF_succRecApproxAt_free
#check @AckermannHF.HF_ordinalLikeAt_free
#check @AckermannHF.OrdinalLike.of_mem
#check @AckermannHF.OrdinalLike.empty
#check @AckermannHF.OrdinalLike.adjoin_self
#check @AckermannHF.ordinalCode_ordinalLike
#check @AckermannHF.HF_ordinalLikeAt_of_ordinalCode
#check @AckermannHF.ordinalLike_is_ordinalCode
#check @AckermannHF.HF_ordinalLikeAt_exact
#check @AckermannHF.succIterObj_ordinalCode
#check @AckermannHF.succRecTrace_mem_iff
#check @AckermannHF.succRecTrace_pair_mem
#check @AckermannHF.succRecTrace_functional
#check @AckermannHF.succRecTrace_keysBelowSucc
#check @AckermannHF.succRecTrace_totalBelowSucc
#check @AckermannHF.succRecTrace_succStep
#check @AckermannHF.succRecTrace_succRecApprox
#check @AckermannHF.succRecApprox_value_of_le
#check @AckermannHF.mulRecTrace_mem_iff
#check @AckermannHF.mulRecTrace_pair_mem
#check @AckermannHF.mulRecTrace_functional
#check @AckermannHF.mulRecTrace_keysBelowSucc
#check @AckermannHF.mulRecTrace_totalBelowSucc
#check @AckermannHF.PAInHF.domainForm
#check @AckermannHF.PAInHF.zeroGraph
#check @AckermannHF.PAInHF.succGraph
#check @AckermannHF.PAInHF.addGraphAt
#check @AckermannHF.PAInHF.addGraph
#check @AckermannHF.PAInHF.mulStepAt
#check @AckermannHF.PAInHF.mulRecApproxAt
#check @AckermannHF.PAInHF.mulGraphAt
#check @AckermannHF.PAInHF.mulGraph
#check @AckermannHF.PAInHF.domain_ordinalCode
#check @AckermannHF.PAInHF.domain_exact
#check @AckermannHF.PAInHF.zeroGraph_ordinalCode
#check @AckermannHF.PAInHF.zeroGraph_exact_on_ordinalCode
#check @AckermannHF.PAInHF.succGraph_ordinalCode
#check @AckermannHF.PAInHF.succGraph_exact_on_ordinalCodes
#check @AckermannHF.PAInHF.addGraph_ordinalCode
#check @AckermannHF.PAInHF.addGraphAt_ordinalCode
#check @AckermannHF.PAInHF.addGraphAt_value_of_ordinalInputs
#check @AckermannHF.PAInHF.addGraphAt_exact_on_ordinalCodes
#check @AckermannHF.PAInHF.addGraph_exact_on_ordinalCodes
#check @AckermannHF.PAInHF.mulGraph_ordinalCode
#check @AckermannHF.PAInHF.mulRecApproxAt_value_of_le
#check @AckermannHF.PAInHF.mulGraph_exact_on_ordinalCodes
#check @AckermannHF.PAInHF.mulGraph_value_of_ordinalInputs
#check @AckermannHF.PAInHF.domainForm_free
#check @AckermannHF.PAInHF.addGraphAt_free
#check @AckermannHF.PAInHF.mulGraphAt_free
#check @AckermannHF.PAInHF.zeroGraph_domain
#check @AckermannHF.PAInHF.succGraph_preserves_domain
#check @AckermannHF.PAInHF.termGraphAt
#check @AckermannHF.PAInHF.termGraphAt_free
#check @AckermannHF.PAInHF.termGraphAt_exact
#check @AckermannHF.PAInHF.upVarMap
#check @AckermannHF.PAInHF.formulaAt
#check @AckermannHF.PAInHF.formulaAt_free
#check @AckermannHF.PAInHF.formulaAt_exact
#check @AckermannHF.PAInHF.translateFormula
#check @AckermannHF.PAInHF.translateFormula_exact
#check @AckermannHF.PAInHF.translated_PA_axiom_sat_codes
#check @AckermannHF.PAInHF.formulaAt_sentence_of_PA_sentence
#check @AckermannHF.PAInHF.translateFormula_sentence_of_PA_sentence
#check @AckermannHF.PAInHF.translated_PA_axiom_sentence
#check @AckermannHF.PAInHF.translatedPAAx
#check @AckermannHF.PAInHF.Sentences_translatedPAAx
#check @AckermannHF.PAInHF.standard_sat_translatedPAAx
#check @AckermannHF.sat_HF_model
#check @AckermannHF.standard_sat_HF
#check @AckermannHF.ordinalHF_sat_HF
#check @AckermannHF.ordinalPA_sat_PA
#check @AckermannHF.standardShallowBiInterpretation
#check @AckermannHF.PA_biinterpretable_with_HF_standard
#print axioms PA.Formula.sat_axiom
#print axioms PA.Formula.sat_axiom_s
#print axioms AckermannHF.sat_HF_model
#print axioms AckermannHF.standard_sat_HF
#print axioms AckermannHF.PA_biinterpretable_with_HF_standard

-- the shallow self-contained pair, with their free dependency audits
#check @Forward.Pairing
#check @Forward.Union
#check @Forward.Replacement
#check @Forward.Infinity
#print axioms Forward.Pairing
#check @Reverse.Closure_holds
#print axioms Reverse.Closure_holds
