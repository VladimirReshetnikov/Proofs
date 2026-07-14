import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a11_a03_a08_a12_a15 : Guided.Work :=
  after [a11, a03, a08, a12, a15]

def certificate_a11_a03_a08_a12_a15 : Guided.Certificate :=
  Guided.Certificate.history2x3

set_option maxHeartbeats 1600000 in
theorem verified_a11_a03_a08_a12_a15 :
    work_a11_a03_a08_a12_a15.check certificate_a11_a03_a08_a12_a15 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
