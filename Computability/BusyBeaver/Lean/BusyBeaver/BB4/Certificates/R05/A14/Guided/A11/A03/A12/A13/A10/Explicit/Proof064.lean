import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof064.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof064.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof064.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof064.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append064 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids064_parts :
    explicitMids064Part0 ++
      (explicitMids064Part1 ++
        (explicitMids064Part2 ++ explicitMids064Part3)) =
      explicitMids064 := by
  decide

theorem explicitMidLengths064 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids064 := by
  have h := explicitAll_append064 explicitMidLengths064Part0
    (explicitAll_append064 explicitMidLengths064Part1
      (explicitAll_append064 explicitMidLengths064Part2
        explicitMidLengths064Part3))
  rw [explicitMids064_parts] at h
  exact h

theorem explicitClosed064 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids064 := by
  have h := explicitAll_append064 explicitClosed064Part0
    (explicitAll_append064 explicitClosed064Part1
      (explicitAll_append064 explicitClosed064Part2
        explicitClosed064Part3))
  rw [explicitMids064_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
