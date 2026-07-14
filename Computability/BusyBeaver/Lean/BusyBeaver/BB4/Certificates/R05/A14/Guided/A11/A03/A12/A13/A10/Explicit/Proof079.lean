import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof079.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof079.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof079.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof079.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append079 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids079_parts :
    explicitMids079Part0 ++
      (explicitMids079Part1 ++
        (explicitMids079Part2 ++ explicitMids079Part3)) =
      explicitMids079 := by
  decide

theorem explicitMidLengths079 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids079 := by
  have h := explicitAll_append079 explicitMidLengths079Part0
    (explicitAll_append079 explicitMidLengths079Part1
      (explicitAll_append079 explicitMidLengths079Part2
        explicitMidLengths079Part3))
  rw [explicitMids079_parts] at h
  exact h

theorem explicitClosed079 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids079 := by
  have h := explicitAll_append079 explicitClosed079Part0
    (explicitAll_append079 explicitClosed079Part1
      (explicitAll_append079 explicitClosed079Part2
        explicitClosed079Part3))
  rw [explicitMids079_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
