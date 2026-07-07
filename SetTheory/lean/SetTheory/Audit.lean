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
#check @AckermannHF.HF_succRecApproxAt_spec
#check @AckermannHF.HF_subsetAt_spec
#check @AckermannHF.HF_transitiveAt_spec
#check @AckermannHF.HF_memTotalOnAt_spec
#check @AckermannHF.HF_ordinalLikeAt_spec
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
#check @AckermannHF.PAInHF.domain_ordinalCode
#check @AckermannHF.PAInHF.domain_exact
#check @AckermannHF.PAInHF.zeroGraph_ordinalCode
#check @AckermannHF.PAInHF.zeroGraph_exact_on_ordinalCode
#check @AckermannHF.PAInHF.succGraph_ordinalCode
#check @AckermannHF.PAInHF.succGraph_exact_on_ordinalCodes
#check @AckermannHF.PAInHF.addGraph_ordinalCode
#check @AckermannHF.PAInHF.addGraphAt_ordinalCode
#check @AckermannHF.PAInHF.addGraph_exact_on_ordinalCodes
#check @AckermannHF.PAInHF.zeroGraph_domain
#check @AckermannHF.PAInHF.succGraph_preserves_domain
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
