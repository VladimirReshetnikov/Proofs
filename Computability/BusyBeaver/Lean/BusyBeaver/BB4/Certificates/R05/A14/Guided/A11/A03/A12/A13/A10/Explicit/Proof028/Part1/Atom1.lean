import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Certificate

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

def explicitMids028Part1Atom1 : List (NGram.MidWord NGram.HistorySymbol) :=
  (explicitMids028.drop 9).take 1

theorem explicitMidLengths028Part1Atom1 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids028Part1Atom1 := by
  decide

set_option maxHeartbeats 1600000 in
theorem explicitClosed028Part1Atom1 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids028Part1Atom1 := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
