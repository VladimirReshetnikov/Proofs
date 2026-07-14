import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a10_a12_a08_a06 : Guided.Work :=
  after [a10, a12, a08, a06]

def certificate_a10_a12_a08_a06 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a10_a12_a08_a06 :
    work_a10_a12_a08_a06.check certificate_a10_a12_a08_a06 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
