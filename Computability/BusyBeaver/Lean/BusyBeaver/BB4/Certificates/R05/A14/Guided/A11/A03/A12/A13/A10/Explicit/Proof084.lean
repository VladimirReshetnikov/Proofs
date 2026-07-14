import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof084.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof084.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof084.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof084.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append084 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids084_parts :
    explicitMids084Part0 ++
      (explicitMids084Part1 ++
        (explicitMids084Part2 ++ explicitMids084Part3)) =
      explicitMids084 := by
  decide

theorem explicitMidLengths084 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids084 := by
  have h := explicitAll_append084 explicitMidLengths084Part0
    (explicitAll_append084 explicitMidLengths084Part1
      (explicitAll_append084 explicitMidLengths084Part2
        explicitMidLengths084Part3))
  rw [explicitMids084_parts] at h
  exact h

theorem explicitClosed084 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids084 := by
  have h := explicitAll_append084 explicitClosed084Part0
    (explicitAll_append084 explicitClosed084Part1
      (explicitAll_append084 explicitClosed084Part2
        explicitClosed084Part3))
  rw [explicitMids084_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
