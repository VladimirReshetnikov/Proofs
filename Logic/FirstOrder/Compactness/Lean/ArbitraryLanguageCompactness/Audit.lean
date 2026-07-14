import ArbitraryLanguageCompactness

/-! Kernel-assumption audit for the arbitrary-language compactness theorem. -/

open LeanProofs.FirstOrderCompactness

#check @arbitrary_language_compactness
#check @FirstOrder.Language.Theory.isSatisfiable_iff_isFinitelySatisfiable
#print axioms arbitrary_language_compactness
#print axioms FirstOrder.Language.Theory.isSatisfiable_iff_isFinitelySatisfiable
