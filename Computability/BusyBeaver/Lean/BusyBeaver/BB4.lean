/-
  BusyBeaver/BB4.lean

  Public facade for the independent Lean proof of the exact four-state Busy
  Beaver score.  Semantic TNF normalization and nonhalting-leaf soundness are
  separate from the sharded kernel computation assembled here.
-/

import BusyBeaver.BB4.Certificates
import BusyBeaver.KnownValues

namespace SetTheory
namespace BusyBeaver
namespace BB4

open KnownValues

/-- Kernel-checked coverage of the complete root-reflection search. -/
theorem searchCoverage :
    Guided.verifyRoot Certificates.rootCertificate = true :=
  Certificates.verifyRoot_rootCertificate

/-- Every halting four-state machine leaves at most thirteen marked cells. -/
theorem all_tables_score_le_thirteen (M : Machine 4) {score : Nat}
    (hHalt : M.HaltsWithScore score) : score ≤ 13 :=
  Guided.upperBound_of_verifyRoot searchCoverage ⟨M, hHalt⟩

/-- No halting four-state machine leaves more than thirteen marked cells. -/
theorem upperBound_four {score : Nat} : AttainableScore 4 score → score ≤ 13 := by
  rintro ⟨M, hHalt⟩
  exact all_tables_score_le_thirteen M hHalt

/-- Thirteen is attained and is an upper bound for every four-state score. -/
theorem exactScore_four : KnownValues.ExactScore 4 13 := by
  constructor
  · exact KnownValues.attainableScore_four_thirteen
  · intro other hScore
    exact upperBound_four hScore

/-- The fourth value of OEIS A028444 in the repository's Rado-machine model. -/
theorem sigma_four_eq_thirteen {Sigma : Nat → Nat} (hSigma : IsSigma Sigma) :
    Sigma 4 = 13 :=
  KnownValues.ExactScore.sigma_eq hSigma (by decide) exactScore_four

end BB4
end BusyBeaver
end SetTheory
