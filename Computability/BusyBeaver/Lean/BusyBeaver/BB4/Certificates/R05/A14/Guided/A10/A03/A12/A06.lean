import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a10_a03_a12_a06 : Guided.Work :=
  after [a10, a03, a12, a06]

def certificate_a10_a03_a12_a06 : Guided.Certificate :=
  Guided.Certificate.history4x2

set_option maxHeartbeats 1600000 in
theorem verified_a10_a03_a12_a06 :
    work_a10_a03_a12_a06.check certificate_a10_a03_a12_a06 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
