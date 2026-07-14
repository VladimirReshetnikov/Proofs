import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a11_a00_a06_a09_a11 : Guided.Work :=
  after [a11, a00, a06, a09, a11]

def certificate_a11_a00_a06_a09_a11 : Guided.Certificate :=
  Guided.Certificate.history2x2

set_option maxHeartbeats 1600000 in
theorem verified_a11_a00_a06_a09_a11 :
    work_a11_a00_a06_a09_a11.check certificate_a11_a00_a06_a09_a11 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
