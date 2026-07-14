import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof054.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof054.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof054.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof054.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append054 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids054_parts :
    explicitMids054Part0 ++
      (explicitMids054Part1 ++
        (explicitMids054Part2 ++ explicitMids054Part3)) =
      explicitMids054 := by
  decide

theorem explicitMidLengths054 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids054 := by
  have h := explicitAll_append054 explicitMidLengths054Part0
    (explicitAll_append054 explicitMidLengths054Part1
      (explicitAll_append054 explicitMidLengths054Part2
        explicitMidLengths054Part3))
  rw [explicitMids054_parts] at h
  exact h

theorem explicitClosed054 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids054 := by
  have h := explicitAll_append054 explicitClosed054Part0
    (explicitAll_append054 explicitClosed054Part1
      (explicitAll_append054 explicitClosed054Part2
        explicitClosed054Part3))
  rw [explicitMids054_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
