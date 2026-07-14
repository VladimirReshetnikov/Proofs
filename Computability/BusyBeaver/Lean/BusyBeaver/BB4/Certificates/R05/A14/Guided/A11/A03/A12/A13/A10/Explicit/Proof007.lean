import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof007.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof007.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof007.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof007.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append007 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids007_parts :
    explicitMids007Part0 ++
      (explicitMids007Part1 ++
        (explicitMids007Part2 ++ explicitMids007Part3)) =
      explicitMids007 := by
  decide

theorem explicitMidLengths007 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids007 := by
  have h := explicitAll_append007 explicitMidLengths007Part0
    (explicitAll_append007 explicitMidLengths007Part1
      (explicitAll_append007 explicitMidLengths007Part2
        explicitMidLengths007Part3))
  rw [explicitMids007_parts] at h
  exact h

theorem explicitClosed007 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids007 := by
  have h := explicitAll_append007 explicitClosed007Part0
    (explicitAll_append007 explicitClosed007Part1
      (explicitAll_append007 explicitClosed007Part2
        explicitClosed007Part3))
  rw [explicitMids007_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
