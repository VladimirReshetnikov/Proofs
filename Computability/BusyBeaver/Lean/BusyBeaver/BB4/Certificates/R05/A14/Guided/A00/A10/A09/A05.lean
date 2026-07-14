import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a00_a10_a09_a05 : Guided.Work :=
  after [a00, a10, a09, a05]

def certificate_a00_a10_a09_a05 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a00_a10_a09_a05 :
    work_a00_a10_a09_a05.check certificate_a00_a10_a09_a05 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
