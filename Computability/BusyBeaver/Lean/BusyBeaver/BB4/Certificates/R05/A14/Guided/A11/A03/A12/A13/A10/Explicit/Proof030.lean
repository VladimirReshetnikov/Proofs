import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof030.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof030.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof030.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof030.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append030 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids030_parts :
    explicitMids030Part0 ++
      (explicitMids030Part1 ++
        (explicitMids030Part2 ++ explicitMids030Part3)) =
      explicitMids030 := by
  decide

theorem explicitMidLengths030 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids030 := by
  have h := explicitAll_append030 explicitMidLengths030Part0
    (explicitAll_append030 explicitMidLengths030Part1
      (explicitAll_append030 explicitMidLengths030Part2
        explicitMidLengths030Part3))
  rw [explicitMids030_parts] at h
  exact h

theorem explicitClosed030 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids030 := by
  have h := explicitAll_append030 explicitClosed030Part0
    (explicitAll_append030 explicitClosed030Part1
      (explicitAll_append030 explicitClosed030Part2
        explicitClosed030Part3))
  rw [explicitMids030_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
