import BoundedPAConsistency.UniformProofPackage

/-!
# Kernel audit for existential uniform proof packages

These checks expose the exact reduction supplied by `UniformProofPackage`.
They deliberately do not assert that a concrete package relation, its base
witness, or its successor constructor has already been built.
-/

open LeanProofs.BoundedPAConsistency.UniformProofPackage

#check HasPARestrictedConsistencyProofPackage
#check hasPARestrictedConsistencyProofPackage_definable
#check paRestrictedConsistencyProofSelectorIn_of_package

#print axioms hasPARestrictedConsistencyProofPackage_definable
#print axioms paRestrictedConsistencyProofSelectorIn_of_package
