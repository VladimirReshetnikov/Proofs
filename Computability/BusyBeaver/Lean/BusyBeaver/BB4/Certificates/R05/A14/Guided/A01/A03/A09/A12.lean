import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a01_a03_a09_a12 : Guided.Work :=
  after [a01, a03, a09, a12]

def certificate_a01_a03_a09_a12 : Guided.Certificate :=
  Guided.Certificate.branch16
    (Guided.Certificate.bool3)
    (Guided.Certificate.bool2)
    (Guided.Certificate.bool2)
    (Guided.Certificate.bool2)
    (Guided.Certificate.bool2)
    (Guided.Certificate.bool2)
    (Guided.Certificate.bool2)
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
    (Guided.Certificate.bool2)
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
    (Guided.Certificate.bool2)
    (Guided.Certificate.bool2)
    (Guided.Certificate.bool2)
    (Guided.Certificate.history2x2)

set_option maxHeartbeats 1600000 in
theorem verified_a01_a03_a09_a12 :
    work_a01_a03_a09_a12.check certificate_a01_a03_a09_a12 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
