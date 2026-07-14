import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof049.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof049.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof049.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof049.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append049 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids049_parts :
    explicitMids049Part0 ++
      (explicitMids049Part1 ++
        (explicitMids049Part2 ++ explicitMids049Part3)) =
      explicitMids049 := by
  decide

theorem explicitMidLengths049 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids049 := by
  have h := explicitAll_append049 explicitMidLengths049Part0
    (explicitAll_append049 explicitMidLengths049Part1
      (explicitAll_append049 explicitMidLengths049Part2
        explicitMidLengths049Part3))
  rw [explicitMids049_parts] at h
  exact h

theorem explicitClosed049 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids049 := by
  have h := explicitAll_append049 explicitClosed049Part0
    (explicitAll_append049 explicitClosed049Part1
      (explicitAll_append049 explicitClosed049Part2
        explicitClosed049Part3))
  rw [explicitMids049_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
