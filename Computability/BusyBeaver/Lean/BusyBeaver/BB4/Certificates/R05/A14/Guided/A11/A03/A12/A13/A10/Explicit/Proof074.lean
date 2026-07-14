import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof074.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof074.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof074.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof074.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append074 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids074_parts :
    explicitMids074Part0 ++
      (explicitMids074Part1 ++
        (explicitMids074Part2 ++ explicitMids074Part3)) =
      explicitMids074 := by
  decide

theorem explicitMidLengths074 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids074 := by
  have h := explicitAll_append074 explicitMidLengths074Part0
    (explicitAll_append074 explicitMidLengths074Part1
      (explicitAll_append074 explicitMidLengths074Part2
        explicitMidLengths074Part3))
  rw [explicitMids074_parts] at h
  exact h

theorem explicitClosed074 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids074 := by
  have h := explicitAll_append074 explicitClosed074Part0
    (explicitAll_append074 explicitClosed074Part1
      (explicitAll_append074 explicitClosed074Part2
        explicitClosed074Part3))
  rw [explicitMids074_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
