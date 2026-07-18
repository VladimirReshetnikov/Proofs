import BoundedPAConsistency.Basic
import BoundedPAConsistency.CodedHierarchy
import BoundedPAConsistency.FixedLevelTruthCertificate
import BoundedPAConsistency.FixedLevelTruthDefinability
import BoundedPAConsistency.Internal
import BoundedPAConsistency.OrientedHierarchy
import BoundedPAConsistency.QuantifierFreeTruth
import BoundedPAConsistency.QuantifierFreeTarski
import BoundedPAConsistency.QuantifierFreeTransport
import BoundedPAConsistency.QuantifierFreeSoundness
import BoundedPAConsistency.QuantifierFreePAAxioms
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
rank-zero logical rules are sound for every nonstandard restricted derivation.
The PA axiom recognizer is discharged internally at rank zero, yielding the
checked object theorem `PA ⊢ Con₀(PA)`.
Externally indexed positive-level Sigma/Pi truth predicates are represented at
the expected arithmetical-hierarchy levels, and their internally finite HFS
certificates satisfy the positive Boolean and existential clauses.  The
remaining work is to prove the polarity-changing clauses and the higher-level
PA axiom/rule soundness needed for arbitrary positive external bounds.  See
the project README for the exact boundary and roadmap.
-/
