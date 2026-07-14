import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a03_a08_a00_a15 : Guided.Work :=
  after [a03, a08, a00, a15]

def certificate_a03_a08_a00_a15 : Guided.Certificate :=
  Guided.Certificate.branch16
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
    (Guided.Certificate.bool2)
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
    (Guided.Certificate.bool3)
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
    (Guided.Certificate.bool2)
    (Guided.Certificate.bool2)
    (Guided.Certificate.history4x2)
    (Guided.Certificate.history4x2)
    (Guided.Certificate.bool2)
    (Guided.Certificate.bool2)

set_option maxHeartbeats 1600000 in
theorem verified_a03_a08_a00_a15 :
    work_a03_a08_a00_a15.check certificate_a03_a08_a00_a15 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
