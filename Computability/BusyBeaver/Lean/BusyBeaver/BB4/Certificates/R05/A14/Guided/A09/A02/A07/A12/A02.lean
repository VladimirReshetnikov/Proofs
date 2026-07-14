import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a09_a02_a07_a12_a02 : Guided.Work :=
  after [a09, a02, a07, a12, a02]

def certificate_a09_a02_a07_a12_a02 : Guided.Certificate :=
  Guided.Certificate.history2x2

set_option maxHeartbeats 1600000 in
theorem verified_a09_a02_a07_a12_a02 :
    work_a09_a02_a07_a12_a02.check certificate_a09_a02_a07_a12_a02 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
