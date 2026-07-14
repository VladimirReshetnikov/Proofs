import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a07_a10_a03_a15 : Guided.Work :=
  after [a07, a10, a03, a15]

def certificate_a07_a10_a03_a15 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a07_a10_a03_a15 :
    work_a07_a10_a03_a15.check certificate_a07_a10_a03_a15 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
