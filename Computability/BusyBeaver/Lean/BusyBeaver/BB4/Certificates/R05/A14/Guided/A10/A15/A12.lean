import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a10_a15_a12 : Guided.Work :=
  after [a10, a15, a12]

def certificate_a10_a15_a12 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a10_a15_a12 :
    work_a10_a15_a12.check certificate_a10_a15_a12 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
