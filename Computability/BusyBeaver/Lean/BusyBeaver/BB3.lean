/-
  BusyBeaverBB3.lean

  Public facade for the independently checked Lean proof of the exact
  three-state Busy Beaver score.  The executable search is organized into
  twelve first-transition certificate groups, subdivided further where useful
  for kernel computation.  This file only assembles their coverage result with
  the generic soundness theorem and the explicit six-mark champion.
-/

import BusyBeaver.BB3.Certificates
import BusyBeaver.KnownValues

namespace SetTheory
namespace BusyBeaver
namespace BB3

open KnownValues

/-- Kernel-checked coverage of the complete lazy three-state search tree. -/
theorem searchCoverage : check NGram.leaf = true :=
  Certificates.check_leaf

/-- Every halting three-state transition table leaves at most six marked
cells. -/
theorem all_tables_score_le_six (M : Machine 3) {score : Nat}
    (hHalt : M.HaltsWithScore score) : score ≤ 6 :=
  upperBound_of_check NGram.leaf_sound searchCoverage ⟨M, hHalt⟩

/-- No halting three-state machine leaves more than six marked cells. -/
theorem upperBound_three {score : Nat} : AttainableScore 3 score → score ≤ 6 := by
  rintro ⟨M, hHalt⟩
  exact all_tables_score_le_six M hHalt

/-- Six is attained and is an upper bound for every three-state score. -/
theorem exactScore_three : KnownValues.ExactScore 3 6 := by
  constructor
  · exact KnownValues.attainableScore_three_six
  · intro other hScore
    exact upperBound_three hScore

/-- The third value of OEIS A028444 in the repository's Rado-machine model. -/
theorem sigma_three_eq_six {Sigma : Nat -> Nat} (hSigma : IsSigma Sigma) :
    Sigma 3 = 6 :=
  KnownValues.ExactScore.sigma_eq hSigma (by decide) exactScore_three

end BB3
end BusyBeaver
end SetTheory
