import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a07_a11_a06_a04 : Guided.Work :=
  after [a07, a11, a06, a04]

def certificate_a07_a11_a06_a04 : Guided.Certificate :=
  Guided.Certificate.branch16
    (Guided.Certificate.bool2)
    (Guided.Certificate.bool2)
    (Guided.Certificate.bool2)
    (Guided.Certificate.bool3)
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
    (Guided.Certificate.bool2)
    (Guided.Certificate.bool2)
    (Guided.Certificate.bool2)
    (Guided.Certificate.bool2)
    (Guided.Certificate.bool2)
    (Guided.Certificate.bool2)
    (Guided.Certificate.bool2)

theorem verified_a07_a11_a06_a04 :
    work_a07_a11_a06_a04.check certificate_a07_a11_a06_a04 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
