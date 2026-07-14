import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a11_a00_a09_a13_a07 : Guided.Work :=
  after [a11, a00, a09, a13, a07]

def certificate_a11_a00_a09_a13_a07 : Guided.Certificate :=
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

theorem verified_a11_a00_a09_a13_a07 :
    work_a11_a00_a09_a13_a07.check certificate_a11_a00_a09_a13_a07 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
