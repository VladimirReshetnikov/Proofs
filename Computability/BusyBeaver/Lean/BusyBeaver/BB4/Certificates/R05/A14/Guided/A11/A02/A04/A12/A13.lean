import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a11_a02_a04_a12_a13 : Guided.Work :=
  after [a11, a02, a04, a12, a13]

def certificate_a11_a02_a04_a12_a13 : Guided.Certificate :=
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

theorem verified_a11_a02_a04_a12_a13 :
    work_a11_a02_a04_a12_a13.check certificate_a11_a02_a04_a12_a13 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
