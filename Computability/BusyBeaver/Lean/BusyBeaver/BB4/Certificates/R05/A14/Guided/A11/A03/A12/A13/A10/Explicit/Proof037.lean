import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof037.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof037.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof037.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof037.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append037 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids037_parts :
    explicitMids037Part0 ++
      (explicitMids037Part1 ++
        (explicitMids037Part2 ++ explicitMids037Part3)) =
      explicitMids037 := by
  decide

theorem explicitMidLengths037 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids037 := by
  have h := explicitAll_append037 explicitMidLengths037Part0
    (explicitAll_append037 explicitMidLengths037Part1
      (explicitAll_append037 explicitMidLengths037Part2
        explicitMidLengths037Part3))
  rw [explicitMids037_parts] at h
  exact h

theorem explicitClosed037 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids037 := by
  have h := explicitAll_append037 explicitClosed037Part0
    (explicitAll_append037 explicitClosed037Part1
      (explicitAll_append037 explicitClosed037Part2
        explicitClosed037Part3))
  rw [explicitMids037_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
