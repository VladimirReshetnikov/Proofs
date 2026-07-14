import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof027.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof027.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof027.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof027.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append027 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids027_parts :
    explicitMids027Part0 ++
      (explicitMids027Part1 ++
        (explicitMids027Part2 ++ explicitMids027Part3)) =
      explicitMids027 := by
  decide

theorem explicitMidLengths027 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids027 := by
  have h := explicitAll_append027 explicitMidLengths027Part0
    (explicitAll_append027 explicitMidLengths027Part1
      (explicitAll_append027 explicitMidLengths027Part2
        explicitMidLengths027Part3))
  rw [explicitMids027_parts] at h
  exact h

theorem explicitClosed027 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids027 := by
  have h := explicitAll_append027 explicitClosed027Part0
    (explicitAll_append027 explicitClosed027Part1
      (explicitAll_append027 explicitClosed027Part2
        explicitClosed027Part3))
  rw [explicitMids027_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
