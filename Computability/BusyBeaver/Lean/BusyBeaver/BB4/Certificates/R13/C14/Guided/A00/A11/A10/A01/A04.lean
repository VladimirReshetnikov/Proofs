import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a00_a11_a10_a01_a04 : Guided.Work :=
  after [a00, a11, a10, a01, a04]

def certificate_a00_a11_a10_a01_a04 : Guided.Certificate :=
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

theorem verified_a00_a11_a10_a01_a04 :
    work_a00_a11_a10_a01_a04.check certificate_a00_a11_a10_a01_a04 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
