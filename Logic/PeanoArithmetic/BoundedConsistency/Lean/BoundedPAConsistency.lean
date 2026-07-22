import BoundedPAConsistency.AbstractSoundness
import BoundedPAConsistency.Basic
import BoundedPAConsistency.CodedHierarchy
import BoundedPAConsistency.FixedLevelPAInduction
import BoundedPAConsistency.FixedLevelPAInductionAxioms
import BoundedPAConsistency.FixedLevelPAAxioms
import BoundedPAConsistency.FixedLevelPAMinusAxioms
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
import BoundedPAConsistency.UniformInternalProvability
import BoundedPAConsistency.UniformProofPackage

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
the already proved soundness of every coded logical inference.  Standard
quotation adequacy discharges every axiom recognized by the finite
`PeanoMinus` branch at every level.  A separate represented induction
argument proves truth of every possibly nonstandard induction-axiom code,
including a nonstandard number of leading universal quantifiers.  Splitting
the complete PA recognizer and applying arithmetic completeness yields the
object theorem `PA ⊢ Con_n(PA)` for every external natural number `n`.  See
the project README for the exact statement and the remaining Rocq work. For
the genuinely uniform sentence, existential Sigma-one proof packages reduce
the missing model-internal selector to explicit base, successor, and final
proof-extraction obligations without requiring a canonical compiler.
-/
