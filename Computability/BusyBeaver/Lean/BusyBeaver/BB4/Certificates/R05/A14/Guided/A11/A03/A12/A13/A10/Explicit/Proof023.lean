import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof023.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof023.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof023.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof023.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append023 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids023_parts :
    explicitMids023Part0 ++
      (explicitMids023Part1 ++
        (explicitMids023Part2 ++ explicitMids023Part3)) =
      explicitMids023 := by
  decide

theorem explicitMidLengths023 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids023 := by
  have h := explicitAll_append023 explicitMidLengths023Part0
    (explicitAll_append023 explicitMidLengths023Part1
      (explicitAll_append023 explicitMidLengths023Part2
        explicitMidLengths023Part3))
  rw [explicitMids023_parts] at h
  exact h

theorem explicitClosed023 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids023 := by
  have h := explicitAll_append023 explicitClosed023Part0
    (explicitAll_append023 explicitClosed023Part1
      (explicitAll_append023 explicitClosed023Part2
        explicitClosed023Part3))
  rw [explicitMids023_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
