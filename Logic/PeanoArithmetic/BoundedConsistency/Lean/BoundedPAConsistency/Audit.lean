import BoundedPAConsistency.Basic
import BoundedPAConsistency.Internal

/-!
# Kernel audit for bounded PA consistency, phase one

The checks below keep the public metatheoretic surface visible and ask Lean to
report the assumptions of the key hierarchy, erasure, cofinality, collapse,
and standard-model consistency theorems.
-/

open LeanProofs.BoundedPAConsistency

#check sigmaRank
#check piRank
#check quantifierGroups
#check hierarchyRanks_rename
#check hierarchyRanks_subst
#check quantifierGroups_mixed_branches
#check ProvTree
#check eraseProvTree
#check provTree_complete
#check proofOccurrenceRank
#check ProofAllBounded
#check RestrictedProv
#check RestrictedBProv
#check restrictedProv_erase
#check restrictedBProv_erase
#check restrictedProv_cofinal
#check restrictedBProv_cofinal
#check conclusionRestrictedProv_bot_iff
#check conclusionRestrictedBProv_bot_iff
#check restrictedPA_consistent_standard
#check LeanProofs.BoundedPAConsistency.Internal.inductionAtHierarchy
#check LeanProofs.BoundedPAConsistency.Internal.inductionInPeanoModel

#print axioms hierarchyRanks_rename
#print axioms hierarchyRanks_subst
#print axioms provTree_complete
#print axioms restrictedBProv_erase
#print axioms restrictedBProv_cofinal
#print axioms conclusionRestrictedBProv_bot_iff
#print axioms restrictedPA_consistent_standard
#print axioms LeanProofs.BoundedPAConsistency.Internal.inductionAtHierarchy
#print axioms LeanProofs.BoundedPAConsistency.Internal.inductionInPeanoModel
