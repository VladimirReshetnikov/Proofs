import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof041.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof041.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof041.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof041.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append041 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids041_parts :
    explicitMids041Part0 ++
      (explicitMids041Part1 ++
        (explicitMids041Part2 ++ explicitMids041Part3)) =
      explicitMids041 := by
  decide

theorem explicitMidLengths041 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids041 := by
  have h := explicitAll_append041 explicitMidLengths041Part0
    (explicitAll_append041 explicitMidLengths041Part1
      (explicitAll_append041 explicitMidLengths041Part2
        explicitMidLengths041Part3))
  rw [explicitMids041_parts] at h
  exact h

theorem explicitClosed041 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids041 := by
  have h := explicitAll_append041 explicitClosed041Part0
    (explicitAll_append041 explicitClosed041Part1
      (explicitAll_append041 explicitClosed041Part2
        explicitClosed041Part3))
  rw [explicitMids041_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
