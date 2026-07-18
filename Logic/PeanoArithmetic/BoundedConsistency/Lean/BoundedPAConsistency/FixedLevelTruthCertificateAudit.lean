import BoundedPAConsistency.FixedLevelTruthCertificate

/-!
# Kernel audit for fixed-level truth certificates

These checks exercise the certificate operations over arbitrary elements of
an arbitrary model of `I Sigma 1`.  In particular, the formula and certificate
codes below are not assumed to be standard natural numbers.
-/

namespace LeanProofs.BoundedPAConsistency.FixedLevelTruthCertificateAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.OrientedHierarchy
open LeanProofs.BoundedPAConsistency.FixedLevelTruth
open LeanProofs.BoundedPAConsistency.FixedLevelTruthCertificate

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* ISigma 1]

#check HasTruthState.mono
#check SigmaRecordValid.mono
#check sigmaTrue_succ_of_qfTrue
#check sigmaTrue_succ_and_iff
#check sigmaTrue_succ_or_iff
#check sigmaTrue_succ_exs_iff

example {n : ℕ} {bound free p q : V}
    (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q) :
    SigmaTrue (n + 1) bound free (p ^⋏ q) ↔
      SigmaTrue (n + 1) bound free p ∧
        SigmaTrue (n + 1) bound free q :=
  sigmaTrue_succ_and_iff hp hq

example {n : ℕ} {bound free q : V} (hq : IsUFormula ℒₒᵣ q) :
    SigmaTrue (n + 1) bound free (^∃ q) ↔
      ∃ a, SigmaTrue (n + 1) (bound ⁀' a) free q :=
  sigmaTrue_succ_exs_iff hq

#print axioms HasTruthState.mono
#print axioms SigmaRecordValid.mono
#print axioms sigmaTrue_succ_of_qfTrue
#print axioms sigmaTrue_succ_and_iff
#print axioms sigmaTrue_succ_or_iff
#print axioms sigmaTrue_succ_exs_iff

end LeanProofs.BoundedPAConsistency.FixedLevelTruthCertificateAudit
