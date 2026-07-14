import PrincipleOfExplosion

/-! Assumption audit for the principle of explosion. -/

open LeanProofs.NaturalDeduction
open LeanProofs.PrincipleOfExplosion

#check @classical_excludedMiddle
#check @intuitionistic_to_classical
#check @derives_explosion
#check @derives_explosion_sequent
#check @intuitionistic_explosion
#check @intuitionistic_explosion_sequent
#check @intuitionistic_explosion_implication
#check @classical_explosion
#check @classical_explosion_sequent
#check @classical_explosion_implication

#print axioms classical_excludedMiddle
#print axioms intuitionistic_to_classical
#print axioms intuitionistic_explosion_sequent
#print axioms intuitionistic_explosion_implication
#print axioms classical_explosion_sequent
#print axioms classical_explosion_implication
