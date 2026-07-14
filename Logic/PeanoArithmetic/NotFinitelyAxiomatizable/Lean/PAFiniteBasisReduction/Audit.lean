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
#check @pa_not_finitely_axiomatizable_of_strict_fragments

#print axioms bound_finite_axiomatization
#print axioms bprov_listTheory_iff_prov
#print axioms finiteAxiomatization_to_finiteSubtheoryBasis
#print axioms finiteAxiomatization_iff_finiteSubtheoryBasis
#print axioms no_finiteSubtheoryBasis_of_strict_fragments
#print axioms pa_not_finitely_axiomatizable_of_strict_fragments
