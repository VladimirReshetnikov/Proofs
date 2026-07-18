import BoundedPAConsistency.Basic
import BoundedPAConsistency.CodedHierarchy
import BoundedPAConsistency.Internal
import BoundedPAConsistency.QuantifierFreeTruth
import BoundedPAConsistency.RestrictedConsistency

/-!
# Bounded-complexity consistency for PA

This facade exposes the metatheoretic proof-tree development and the
nonstandard-model infrastructure for the internal theorem: coded hierarchy
ranks, term and rank-zero formula evaluation, the all-occurrences Delta-one
derivation fixed point, and the fixed-external-bound Pi-one consistency
sentence.  The remaining work is the higher-level partial-truth construction
and its internal soundness proof.  In particular, this module does not yet
claim an object-level PA derivation; see the project README for the exact
boundary and roadmap.
-/
