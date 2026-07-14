import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a00_a09_a07_a13 : Guided.Work :=
  after [a00, a09, a07, a13]

def certificate_a00_a09_a07_a13 : Guided.Certificate :=
  Guided.Certificate.branch16
    (Guided.Certificate.bool2)
    (Guided.Certificate.bool2)
    (Guided.Certificate.bool2)
    (Guided.Certificate.bool3)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
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
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
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

theorem verified_a00_a09_a07_a13 :
    work_a00_a09_a07_a13.check certificate_a00_a09_a07_a13 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
