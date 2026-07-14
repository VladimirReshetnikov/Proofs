import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof031.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof031.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof031.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof031.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append031 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids031_parts :
    explicitMids031Part0 ++
      (explicitMids031Part1 ++
        (explicitMids031Part2 ++ explicitMids031Part3)) =
      explicitMids031 := by
  decide

theorem explicitMidLengths031 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids031 := by
  have h := explicitAll_append031 explicitMidLengths031Part0
    (explicitAll_append031 explicitMidLengths031Part1
      (explicitAll_append031 explicitMidLengths031Part2
        explicitMidLengths031Part3))
  rw [explicitMids031_parts] at h
  exact h

theorem explicitClosed031 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids031 := by
  have h := explicitAll_append031 explicitClosed031Part0
    (explicitAll_append031 explicitClosed031Part1
      (explicitAll_append031 explicitClosed031Part2
        explicitClosed031Part3))
  rw [explicitMids031_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
