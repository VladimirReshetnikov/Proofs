import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a02_a01_a07 : Guided.Work :=
  after [a02, a01, a07]

def certificate_a02_a01_a07 : Guided.Certificate :=
  Guided.Certificate.branch16
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
    (Guided.Certificate.bool1)

theorem verified_a02_a01_a07 :
    work_a02_a01_a07.check certificate_a02_a01_a07 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
