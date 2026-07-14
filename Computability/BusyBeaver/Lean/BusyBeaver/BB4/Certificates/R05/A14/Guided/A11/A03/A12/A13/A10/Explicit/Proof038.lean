import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof038.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof038.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof038.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof038.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append038 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids038_parts :
    explicitMids038Part0 ++
      (explicitMids038Part1 ++
        (explicitMids038Part2 ++ explicitMids038Part3)) =
      explicitMids038 := by
  decide

theorem explicitMidLengths038 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids038 := by
  have h := explicitAll_append038 explicitMidLengths038Part0
    (explicitAll_append038 explicitMidLengths038Part1
      (explicitAll_append038 explicitMidLengths038Part2
        explicitMidLengths038Part3))
  rw [explicitMids038_parts] at h
  exact h

theorem explicitClosed038 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids038 := by
  have h := explicitAll_append038 explicitClosed038Part0
    (explicitAll_append038 explicitClosed038Part1
      (explicitAll_append038 explicitClosed038Part2
        explicitClosed038Part3))
  rw [explicitMids038_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
