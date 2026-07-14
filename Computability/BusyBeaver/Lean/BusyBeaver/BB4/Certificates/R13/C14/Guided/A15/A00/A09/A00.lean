import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a15_a00_a09_a00 : Guided.Work :=
  after [a15, a00, a09, a00]

def certificate_a15_a00_a09_a00 : Guided.Certificate :=
  Guided.Certificate.branch16
    (Guided.Certificate.bool3)
    (Guided.Certificate.bool3)
    (Guided.Certificate.bool3)
    (Guided.Certificate.branch16
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete))
    (Guided.Certificate.history2x2)
    (Guided.Certificate.bool3)
    (Guided.Certificate.branch16
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete))
    (Guided.Certificate.bool3)
    (Guided.Certificate.bool3)
    (Guided.Certificate.bool3)
    (Guided.Certificate.branch16
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete))
    (Guided.Certificate.branch16
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete))
    (Guided.Certificate.bool3)
    (Guided.Certificate.bool3)
    (Guided.Certificate.branch16
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete)
      (Guided.Certificate.complete))
    (Guided.Certificate.bool3)

set_option maxHeartbeats 1600000 in
theorem verified_a15_a00_a09_a00 :
    work_a15_a00_a09_a00.check certificate_a15_a00_a09_a00 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
