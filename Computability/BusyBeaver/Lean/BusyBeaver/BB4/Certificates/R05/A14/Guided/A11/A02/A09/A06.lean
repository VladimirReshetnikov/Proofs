import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a11_a02_a09_a06 : Guided.Work :=
  after [a11, a02, a09, a06]

def certificate_a11_a02_a09_a06 : Guided.Certificate :=
  Guided.Certificate.history2x2

set_option maxHeartbeats 1600000 in
theorem verified_a11_a02_a09_a06 :
    work_a11_a02_a09_a06.check certificate_a11_a02_a09_a06 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
