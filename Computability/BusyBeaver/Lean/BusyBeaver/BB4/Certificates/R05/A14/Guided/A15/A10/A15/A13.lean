import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a15_a10_a15_a13 : Guided.Work :=
  after [a15, a10, a15, a13]

def certificate_a15_a10_a15_a13 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a15_a10_a15_a13 :
    work_a15_a10_a15_a13.check certificate_a15_a10_a15_a13 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
