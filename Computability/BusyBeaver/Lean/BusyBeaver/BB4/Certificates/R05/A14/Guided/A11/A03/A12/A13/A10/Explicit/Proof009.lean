import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof009.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof009.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof009.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof009.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append009 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids009_parts :
    explicitMids009Part0 ++
      (explicitMids009Part1 ++
        (explicitMids009Part2 ++ explicitMids009Part3)) =
      explicitMids009 := by
  decide

theorem explicitMidLengths009 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids009 := by
  have h := explicitAll_append009 explicitMidLengths009Part0
    (explicitAll_append009 explicitMidLengths009Part1
      (explicitAll_append009 explicitMidLengths009Part2
        explicitMidLengths009Part3))
  rw [explicitMids009_parts] at h
  exact h

theorem explicitClosed009 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids009 := by
  have h := explicitAll_append009 explicitClosed009Part0
    (explicitAll_append009 explicitClosed009Part1
      (explicitAll_append009 explicitClosed009Part2
        explicitClosed009Part3))
  rw [explicitMids009_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
