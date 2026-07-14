import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a15_a10_a01_a04 : Guided.Work :=
  after [a15, a10, a01, a04]

def certificate_a15_a10_a01_a04 : Guided.Certificate :=
  Guided.Certificate.bool2

theorem verified_a15_a10_a01_a04 :
    work_a15_a10_a01_a04.check certificate_a15_a10_a01_a04 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
