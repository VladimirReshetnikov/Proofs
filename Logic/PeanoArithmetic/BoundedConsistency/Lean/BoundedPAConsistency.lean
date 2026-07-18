import BoundedPAConsistency.AbstractSoundness
import BoundedPAConsistency.Basic
import BoundedPAConsistency.CodedHierarchy
import BoundedPAConsistency.FixedLevelPAInduction
import BoundedPAConsistency.FixedLevelSequentDefinability
import BoundedPAConsistency.FixedLevelSoundness
import BoundedPAConsistency.FixedLevelTruthCertificate
import BoundedPAConsistency.FixedLevelTruthCoherence
import BoundedPAConsistency.FixedLevelTruthDefinability
import BoundedPAConsistency.FixedLevelTruthLaws
import BoundedPAConsistency.FixedLevelTruthSubstitution
import BoundedPAConsistency.FixedLevelTruthTarski
import BoundedPAConsistency.Internal
import BoundedPAConsistency.ModelFormulaInduction
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
the expected arithmetical-hierarchy levels.  Their internally finite HFS
certificates satisfy the Boolean and quantified oriented Tarski clauses,
including the polarity switches at universal and existential heads.  They are
coherent on overlapping polarity domains and commute with nonstandard coded
shift and simultaneous substitution.  At each fixed external bound,
`SigmaTrue (n + 1)` therefore supplies the complete semantic-law interface for
the already proved soundness of every coded logical inference.  The remaining
Lean work is truth of all internally recognized positive-level PA axioms and
the final object-theory assembly.  See the project README for the exact
boundary and roadmap.
-/
