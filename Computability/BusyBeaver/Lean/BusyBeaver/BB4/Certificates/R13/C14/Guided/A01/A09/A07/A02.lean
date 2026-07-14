import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a01_a09_a07_a02 : Guided.Work :=
  after [a01, a09, a07, a02]

def certificate_a01_a09_a07_a02 : Guided.Certificate :=
  Guided.Certificate.branch16
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.history2x2)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.history2x3)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)

set_option maxHeartbeats 1600000 in
theorem verified_a01_a09_a07_a02 :
    work_a01_a09_a07_a02.check certificate_a01_a09_a07_a02 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
