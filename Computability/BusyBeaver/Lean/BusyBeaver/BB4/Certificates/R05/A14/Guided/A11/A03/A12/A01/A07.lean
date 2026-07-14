import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a11_a03_a12_a01_a07 : Guided.Work :=
  after [a11, a03, a12, a01, a07]

def certificate_a11_a03_a12_a01_a07 : Guided.Certificate :=
  Guided.Certificate.history6x2

set_option maxHeartbeats 1600000 in
theorem verified_a11_a03_a12_a01_a07 :
    work_a11_a03_a12_a01_a07.check certificate_a11_a03_a12_a01_a07 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
