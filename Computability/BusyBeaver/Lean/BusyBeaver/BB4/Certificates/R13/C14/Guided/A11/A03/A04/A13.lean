import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a11_a03_a04_a13 : Guided.Work :=
  after [a11, a03, a04, a13]

def certificate_a11_a03_a04_a13 : Guided.Certificate :=
  Guided.Certificate.history2x2

set_option maxHeartbeats 1600000 in
theorem verified_a11_a03_a04_a13 :
    work_a11_a03_a04_a13.check certificate_a11_a03_a04_a13 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
