import PAFiniteBasisReduction

/-! Kernel audit for the completed finite-basis reduction.  The arithmetic
finite-fragment strictness premise is deliberately visible in the type of the
conditional headline theorem. -/

open LeanProofs.PAFiniteBasisReduction

#check @ListTheory
#check @bprov_listTheory_iff_prov
#check @ProvablyEquivalent
#check @FiniteAxiomatization
#check @FiniteSubtheoryBasis
#check @bound_finite_axiomatization
#check @finiteAxiomatization_to_finiteSubtheoryBasis
#check @finiteAxiomatization_iff_finiteSubtheoryBasis
#check @PAInductionFragmentStrictness
#check @PAFiniteFragmentStrictness
#check @ConsistentList
#check @paFiniteFragment_consistent
#check @finiteFragmentStrictness_of_inductionFragmentStrictness
#check @finiteFragmentStrictness_of_mostowski
#check @no_finiteSubtheoryBasis_of_finiteFragmentStrictness
#check @finiteFragmentStrictness_iff_no_finiteSubtheoryBasis
#check @pa_not_finitely_axiomatizable_of_finiteFragmentStrictness
#check @pa_not_finitely_axiomatizable_iff_finiteFragmentStrictness
#check @pa_not_finitely_axiomatizable_of_strict_fragments
#check @termRank
#check @formulaRank
#check @PARankFragment
#check @FinitelyEnumerated
#check @termsOfRankAtMost
#check @mem_termsOfRankAtMost
#check @termRank_le_finite
#check @formulasOfRankAtMost
#check @mem_formulasOfRankAtMost
#check @formulaRank_le_finite
#check @paRankFragmentAxioms
#check @mem_paRankFragmentAxioms
#check @paRankFragment_finite
#check @paRankFragment_subset_ax_s
#check @paRankFragment_mono
#check @paAxiom_mem_some_rankFragment
#check @finitePAFragment_bounded_by_rank
#check @PARankFragmentStrictness
#check @PARankFragmentSentenceStrictness
#check @SetTheory.PA.PreModel
#check @SetTheory.PA.Model.mk
#check @SetTheory.PA.Model.toPreModel
#check @SetTheory.PA.Model.toPreModel_zero
#check @SetTheory.PA.Model.toPreModel_succ
#check @SetTheory.PA.Model.toPreModel_add
#check @SetTheory.PA.Model.toPreModel_mul
#check @SetTheory.PA.Term.eval
#check @SetTheory.PA.Term.eval_ext_free
#check @SetTheory.PA.Formula.Sat
#check @SetTheory.PA.Formula.Sat_ext_free
#check @SetTheory.PA.Formula.soundness
#check @SetTheory.PA.Formula.soundness_BProv
#check @not_bprov_of_preModel_counterexample
#check @PARankFragmentCountermodels
#check @rankFragmentSentenceStrictness_of_countermodels
#check @inductionFragmentStrictness_of_rankFragmentStrictness
#check @finiteFragmentStrictness_of_rankFragmentStrictness
#check @finiteFragmentStrictness_of_rankFragmentSentenceStrictness
#check @finiteFragmentStrictness_of_rankFragmentCountermodels
#check @pa_not_finitely_axiomatizable_of_rankFragmentStrictness
#check @pa_not_finitely_axiomatizable_of_rankFragmentCountermodels
#check @TwoChain
#check @twoChainPreModel
#check @zeroOrSuccFormula
#check @twoChain_not_sat_inductionForm
#check @formulaRank_pos
#check @twoChain_sat_rankZero
#check @exists_sat_of_sat_closeN
#check @twoChain_not_sat_sealed_induction
#check @rankZero_not_bprov_induction
#check @rankZero_witness_is_pa_axiom
#check @rankZero_strictness_witness
#check @rankZero_pa_axiom_separation
#check @NonstandardHFFin.Sat_tag_relativize
#check @NonstandardHFFin.Sat_tag_candidateAt
#check @NonstandardHFFin.Sat_tag_starBound_iff
#check @NonstandardHFFin.Ax_BCon
#check @NonstandardHFFin.nonstandardHFFin_translated_exists
#check @NonstandardHFFin.nonstandardHFFin_fofam_exists

-- The standard full PA model remains usable wherever only raw arithmetic
-- operations are required.
example : SetTheory.PA.PreModel Nat := SetTheory.PA.natModel

#print axioms bound_finite_axiomatization
#print axioms bprov_listTheory_iff_prov
#print axioms finiteAxiomatization_to_finiteSubtheoryBasis
#print axioms finiteAxiomatization_iff_finiteSubtheoryBasis
#print axioms paFiniteFragment_consistent
#print axioms finiteFragmentStrictness_of_inductionFragmentStrictness
#print axioms finiteFragmentStrictness_of_mostowski
#print axioms no_finiteSubtheoryBasis_of_finiteFragmentStrictness
#print axioms finiteFragmentStrictness_iff_no_finiteSubtheoryBasis
#print axioms pa_not_finitely_axiomatizable_of_finiteFragmentStrictness
#print axioms pa_not_finitely_axiomatizable_iff_finiteFragmentStrictness
#print axioms no_finiteSubtheoryBasis_of_strict_fragments
#print axioms pa_not_finitely_axiomatizable_of_strict_fragments
#print axioms mem_termsOfRankAtMost
#print axioms termRank_le_finite
#print axioms mem_formulasOfRankAtMost
#print axioms formulaRank_le_finite
#print axioms mem_paRankFragmentAxioms
#print axioms paRankFragment_finite
#print axioms SetTheory.PA.Term.eval_ext_free
#print axioms SetTheory.PA.Formula.Sat_ext_free
#print axioms paRankFragment_subset_ax_s
#print axioms paRankFragment_mono
#print axioms paAxiom_mem_some_rankFragment
#print axioms finitePAFragment_bounded_by_rank
#print axioms not_bprov_of_preModel_counterexample
#print axioms rankFragmentSentenceStrictness_of_countermodels
#print axioms inductionFragmentStrictness_of_rankFragmentStrictness
#print axioms finiteFragmentStrictness_of_rankFragmentStrictness
#print axioms finiteFragmentStrictness_of_rankFragmentSentenceStrictness
#print axioms finiteFragmentStrictness_of_rankFragmentCountermodels
#print axioms pa_not_finitely_axiomatizable_of_rankFragmentStrictness
#print axioms pa_not_finitely_axiomatizable_of_rankFragmentCountermodels
#print axioms twoChain_not_sat_inductionForm
#print axioms formulaRank_pos
#print axioms twoChain_sat_rankZero
#print axioms exists_sat_of_sat_closeN
#print axioms twoChain_not_sat_sealed_induction
#print axioms rankZero_not_bprov_induction
#print axioms rankZero_witness_is_pa_axiom
#print axioms rankZero_strictness_witness
#print axioms rankZero_pa_axiom_separation
#print axioms NonstandardHFFin.Sat_tag_starBound_iff
#print axioms NonstandardHFFin.Ax_BCon
#print axioms NonstandardHFFin.nonstandardHFFin_translated_exists
#print axioms NonstandardHFFin.nonstandardHFFin_fofam_exists
