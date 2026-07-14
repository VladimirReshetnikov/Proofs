import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof000.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof000.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof000.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof000.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append000 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids000_parts :
    explicitMids000Part0 ++
      (explicitMids000Part1 ++
        (explicitMids000Part2 ++ explicitMids000Part3)) =
      explicitMids000 := by
  decide

theorem explicitMidLengths000 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids000 := by
  have h := explicitAll_append000 explicitMidLengths000Part0
    (explicitAll_append000 explicitMidLengths000Part1
      (explicitAll_append000 explicitMidLengths000Part2
        explicitMidLengths000Part3))
  rw [explicitMids000_parts] at h
  exact h

theorem explicitClosed000 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids000 := by
  have h := explicitAll_append000 explicitClosed000Part0
    (explicitAll_append000 explicitClosed000Part1
      (explicitAll_append000 explicitClosed000Part2
        explicitClosed000Part3))
  rw [explicitMids000_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
