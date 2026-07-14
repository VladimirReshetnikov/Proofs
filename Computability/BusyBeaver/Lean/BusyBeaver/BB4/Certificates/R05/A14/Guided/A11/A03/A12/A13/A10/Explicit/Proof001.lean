import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof001.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof001.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof001.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof001.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append001 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids001_parts :
    explicitMids001Part0 ++
      (explicitMids001Part1 ++
        (explicitMids001Part2 ++ explicitMids001Part3)) =
      explicitMids001 := by
  decide

theorem explicitMidLengths001 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids001 := by
  have h := explicitAll_append001 explicitMidLengths001Part0
    (explicitAll_append001 explicitMidLengths001Part1
      (explicitAll_append001 explicitMidLengths001Part2
        explicitMidLengths001Part3))
  rw [explicitMids001_parts] at h
  exact h

theorem explicitClosed001 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids001 := by
  have h := explicitAll_append001 explicitClosed001Part0
    (explicitAll_append001 explicitClosed001Part1
      (explicitAll_append001 explicitClosed001Part2
        explicitClosed001Part3))
  rw [explicitMids001_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
