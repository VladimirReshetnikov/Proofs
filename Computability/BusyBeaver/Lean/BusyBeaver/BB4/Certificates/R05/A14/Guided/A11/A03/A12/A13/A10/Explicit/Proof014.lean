import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof014.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof014.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof014.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof014.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append014 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids014_parts :
    explicitMids014Part0 ++
      (explicitMids014Part1 ++
        (explicitMids014Part2 ++ explicitMids014Part3)) =
      explicitMids014 := by
  decide

theorem explicitMidLengths014 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids014 := by
  have h := explicitAll_append014 explicitMidLengths014Part0
    (explicitAll_append014 explicitMidLengths014Part1
      (explicitAll_append014 explicitMidLengths014Part2
        explicitMidLengths014Part3))
  rw [explicitMids014_parts] at h
  exact h

theorem explicitClosed014 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids014 := by
  have h := explicitAll_append014 explicitClosed014Part0
    (explicitAll_append014 explicitClosed014Part1
      (explicitAll_append014 explicitClosed014Part2
        explicitClosed014Part3))
  rw [explicitMids014_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
