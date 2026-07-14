import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a09_a09_a11_a03 : Guided.Work :=
  after [a09, a09, a11, a03]

def certificate_a09_a09_a11_a03 : Guided.Certificate :=
  Guided.Certificate.branch16
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
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)

theorem verified_a09_a09_a11_a03 :
    work_a09_a09_a11_a03.check certificate_a09_a09_a11_a03 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
