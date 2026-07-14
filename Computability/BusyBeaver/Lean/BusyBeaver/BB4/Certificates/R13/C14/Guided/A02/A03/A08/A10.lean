import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a02_a03_a08_a10 : Guided.Work :=
  after [a02, a03, a08, a10]

def certificate_a02_a03_a08_a10 : Guided.Certificate :=
  Guided.Certificate.branch16
    (Guided.Certificate.bool2)
    (Guided.Certificate.bool2)
    (Guided.Certificate.bool2)
    (Guided.Certificate.bool2)
    (Guided.Certificate.bool2)
    (Guided.Certificate.bool2)
    (Guided.Certificate.bool2)
    (Guided.Certificate.bool2)
    (Guided.Certificate.bool2)
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

theorem verified_a02_a03_a08_a10 :
    work_a02_a03_a08_a10.check certificate_a02_a03_a08_a10 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
