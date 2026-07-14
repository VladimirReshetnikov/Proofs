import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a11_a10_a09_a04_a11 : Guided.Work :=
  after [a11, a10, a09, a04, a11]

def certificate_a11_a10_a09_a04_a11 : Guided.Certificate :=
  Guided.Certificate.branch16
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
    (Guided.Certificate.complete)

theorem verified_a11_a10_a09_a04_a11 :
    work_a11_a10_a09_a04_a11.check certificate_a11_a10_a09_a04_a11 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
