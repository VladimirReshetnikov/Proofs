import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a11_a00_a13_a02_a10 : Guided.Work :=
  after [a11, a00, a13, a02, a10]

def certificate_a11_a00_a13_a02_a10 : Guided.Certificate :=
  Guided.Certificate.history2x3

set_option maxHeartbeats 1600000 in
theorem verified_a11_a00_a13_a02_a10 :
    work_a11_a00_a13_a02_a10.check certificate_a11_a00_a13_a02_a10 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
