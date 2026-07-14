import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a08_a03_a10_a03 : Guided.Work :=
  after [a08, a03, a10, a03]

def certificate_a08_a03_a10_a03 : Guided.Certificate :=
  Guided.Certificate.bool2

theorem verified_a08_a03_a10_a03 :
    work_a08_a03_a10_a03.check certificate_a08_a03_a10_a03 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
