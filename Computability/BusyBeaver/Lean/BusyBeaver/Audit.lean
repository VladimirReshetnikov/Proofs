import BusyBeaver

/-! Assumption audit for the mathlib-free Busy Beaver core. -/

open SetTheory

#check @BusyBeaver.IsSigma
#check @BusyBeaver.AttainableScore
#check @BusyBeaver.sigma_mono_of_pos
#check @BusyBeaver.score_le_sigma_of_atMost
#check @BusyBeaver.sigma_eventually_dominates_every_total_recursive
#check @BusyBeaver.KnownValues.sigma2Champion_haltsWithScore
#print axioms BusyBeaver.sigma_eventually_dominates_every_total_recursive
