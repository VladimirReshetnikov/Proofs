import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof010.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof010.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof010.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof010.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append010 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids010_parts :
    explicitMids010Part0 ++
      (explicitMids010Part1 ++
        (explicitMids010Part2 ++ explicitMids010Part3)) =
      explicitMids010 := by
  decide

theorem explicitMidLengths010 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids010 := by
  have h := explicitAll_append010 explicitMidLengths010Part0
    (explicitAll_append010 explicitMidLengths010Part1
      (explicitAll_append010 explicitMidLengths010Part2
        explicitMidLengths010Part3))
  rw [explicitMids010_parts] at h
  exact h

theorem explicitClosed010 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids010 := by
  have h := explicitAll_append010 explicitClosed010Part0
    (explicitAll_append010 explicitClosed010Part1
      (explicitAll_append010 explicitClosed010Part2
        explicitClosed010Part3))
  rw [explicitMids010_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
