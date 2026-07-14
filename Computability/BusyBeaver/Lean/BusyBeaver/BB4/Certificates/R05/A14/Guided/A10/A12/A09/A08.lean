import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a10_a12_a09_a08 : Guided.Work :=
  after [a10, a12, a09, a08]

def certificate_a10_a12_a09_a08 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a10_a12_a09_a08 :
    work_a10_a12_a09_a08.check certificate_a10_a12_a09_a08 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
