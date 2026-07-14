import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a11_a01_a13_a07 : Guided.Work :=
  after [a11, a01, a13, a07]

def certificate_a11_a01_a13_a07 : Guided.Certificate :=
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

theorem verified_a11_a01_a13_a07 :
    work_a11_a01_a13_a07.check certificate_a11_a01_a13_a07 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
