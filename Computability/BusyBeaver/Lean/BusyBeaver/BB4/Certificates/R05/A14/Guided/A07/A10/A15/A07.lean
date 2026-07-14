import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a07_a10_a15_a07 : Guided.Work :=
  after [a07, a10, a15, a07]

def certificate_a07_a10_a15_a07 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a07_a10_a15_a07 :
    work_a07_a10_a15_a07.check certificate_a07_a10_a15_a07 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
