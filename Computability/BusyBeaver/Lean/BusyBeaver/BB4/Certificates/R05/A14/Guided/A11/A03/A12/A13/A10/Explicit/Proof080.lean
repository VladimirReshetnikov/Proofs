import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof080.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof080.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof080.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof080.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append080 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids080_parts :
    explicitMids080Part0 ++
      (explicitMids080Part1 ++
        (explicitMids080Part2 ++ explicitMids080Part3)) =
      explicitMids080 := by
  decide

theorem explicitMidLengths080 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids080 := by
  have h := explicitAll_append080 explicitMidLengths080Part0
    (explicitAll_append080 explicitMidLengths080Part1
      (explicitAll_append080 explicitMidLengths080Part2
        explicitMidLengths080Part3))
  rw [explicitMids080_parts] at h
  exact h

theorem explicitClosed080 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids080 := by
  have h := explicitAll_append080 explicitClosed080Part0
    (explicitAll_append080 explicitClosed080Part1
      (explicitAll_append080 explicitClosed080Part2
        explicitClosed080Part3))
  rw [explicitMids080_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
