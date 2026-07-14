import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a03_a09_a05_a02 : Guided.Work :=
  after [a03, a09, a05, a02]

def certificate_a03_a09_a05_a02 : Guided.Certificate :=
  Guided.Certificate.branch16
    (Guided.Certificate.bool2)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool3)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)

theorem verified_a03_a09_a05_a02 :
    work_a03_a09_a05_a02.check certificate_a03_a09_a05_a02 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
