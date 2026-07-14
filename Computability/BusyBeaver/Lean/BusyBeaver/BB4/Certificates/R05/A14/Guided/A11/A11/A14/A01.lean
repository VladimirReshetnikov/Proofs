import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a11_a11_a14_a01 : Guided.Work :=
  after [a11, a11, a14, a01]

def certificate_a11_a11_a14_a01 : Guided.Certificate :=
  Guided.Certificate.branch16
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool2)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool2)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)

theorem verified_a11_a11_a14_a01 :
    work_a11_a11_a14_a01.check certificate_a11_a11_a14_a01 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
