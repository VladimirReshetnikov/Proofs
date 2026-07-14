import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a10_a15_a11_a03 : Guided.Work :=
  after [a10, a15, a11, a03]

def certificate_a10_a15_a11_a03 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a10_a15_a11_a03 :
    work_a10_a15_a11_a03.check certificate_a10_a15_a11_a03 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
