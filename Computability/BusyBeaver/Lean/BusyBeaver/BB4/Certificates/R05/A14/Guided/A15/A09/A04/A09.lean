import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a15_a09_a04_a09 : Guided.Work :=
  after [a15, a09, a04, a09]

def certificate_a15_a09_a04_a09 : Guided.Certificate :=
  Guided.Certificate.branch16
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
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool2)
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
    (Guided.Certificate.bool1)

theorem verified_a15_a09_a04_a09 :
    work_a15_a09_a04_a09.check certificate_a15_a09_a04_a09 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
