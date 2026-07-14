import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a10_a12_a11_a03 : Guided.Work :=
  after [a10, a12, a11, a03]

def certificate_a10_a12_a11_a03 : Guided.Certificate :=
  Guided.Certificate.branch16
    (Guided.Certificate.bool2)
    (Guided.Certificate.bool2)
    (Guided.Certificate.bool2)
    (Guided.Certificate.bool2)
    (Guided.Certificate.history2x3)
    (Guided.Certificate.bool3)
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
    (Guided.Certificate.history4x2)
    (Guided.Certificate.bool2)
    (Guided.Certificate.bool2)
    (Guided.Certificate.history4x2)
    (Guided.Certificate.bool2)
    (Guided.Certificate.bool2)
    (Guided.Certificate.bool2)

set_option maxHeartbeats 1600000 in
theorem verified_a10_a12_a11_a03 :
    work_a10_a12_a11_a03.check certificate_a10_a12_a11_a03 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
