import BoundedPAConsistency.Basic
import BoundedPAConsistency.CodedHierarchy
import BoundedPAConsistency.Internal
import BoundedPAConsistency.OrientedHierarchy
import BoundedPAConsistency.QuantifierFreeTruth
import BoundedPAConsistency.QuantifierFreeTarski
import BoundedPAConsistency.QuantifierFreeTransport
import BoundedPAConsistency.QuantifierFreeSoundness
import BoundedPAConsistency.RestrictedConsistency
import BoundedPAConsistency.TermEvaluationTransport

/-!
# Bounded-complexity consistency for PA

This facade exposes the metatheoretic proof-tree development and the
nonstandard-model infrastructure for the internal theorem: coded hierarchy
ranks, term and rank-zero formula evaluation, the all-occurrences Delta-one
derivation fixed point, and the fixed-external-bound Pi-one consistency
sentence.  Term evaluation now commutes internally with free-variable shift
and simultaneous substitution, and the rank-zero truth predicate has
structural domain inversion, atomic/Boolean Tarski clauses, and internal
transport under negation, shift, and substitution on nonstandard codes.  The
rank-zero logical rules are sound for every nonstandard restricted derivation,
conditional only on the explicitly displayed rank-zero theory-axiom premise.
The remaining work includes discharging that premise for PA and constructing
higher-level partial truth.  In particular, this module does not yet claim an
object-level PA derivation; see the project README for the exact boundary and
roadmap.
-/
