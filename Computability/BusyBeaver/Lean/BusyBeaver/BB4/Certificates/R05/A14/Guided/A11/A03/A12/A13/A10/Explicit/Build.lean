import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

set_option maxHeartbeats 1600000 in
theorem explicitBuild :
    NGram.buildCandidate explicitBlank
      (NGram.historyTransition 4 explicitTable) 2 2 600 =
      some explicitCertificate := by
  rfl

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
