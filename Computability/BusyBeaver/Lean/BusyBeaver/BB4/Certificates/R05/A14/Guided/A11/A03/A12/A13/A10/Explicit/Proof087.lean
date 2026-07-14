import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof087.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof087.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof087.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof087.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append087 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids087_parts :
    explicitMids087Part0 ++
      (explicitMids087Part1 ++
        (explicitMids087Part2 ++ explicitMids087Part3)) =
      explicitMids087 := by
  decide

theorem explicitMidLengths087 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids087 := by
  have h := explicitAll_append087 explicitMidLengths087Part0
    (explicitAll_append087 explicitMidLengths087Part1
      (explicitAll_append087 explicitMidLengths087Part2
        explicitMidLengths087Part3))
  rw [explicitMids087_parts] at h
  exact h

theorem explicitClosed087 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids087 := by
  have h := explicitAll_append087 explicitClosed087Part0
    (explicitAll_append087 explicitClosed087Part1
      (explicitAll_append087 explicitClosed087Part2
        explicitClosed087Part3))
  rw [explicitMids087_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
