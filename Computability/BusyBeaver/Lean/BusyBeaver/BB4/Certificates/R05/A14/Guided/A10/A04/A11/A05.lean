import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a10_a04_a11_a05 : Guided.Work :=
  after [a10, a04, a11, a05]

def certificate_a10_a04_a11_a05 : Guided.Certificate :=
  Guided.Certificate.branch16
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)
    (Guided.Certificate.bool1)

theorem verified_a10_a04_a11_a05 :
    work_a10_a04_a11_a05.check certificate_a10_a04_a11_a05 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
