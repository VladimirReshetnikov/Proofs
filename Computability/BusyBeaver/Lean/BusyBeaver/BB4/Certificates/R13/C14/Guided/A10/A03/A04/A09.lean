import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a10_a03_a04_a09 : Guided.Work :=
  after [a10, a03, a04, a09]

def certificate_a10_a03_a04_a09 : Guided.Certificate :=
  Guided.Certificate.bool2

theorem verified_a10_a03_a04_a09 :
    work_a10_a03_a04_a09.check certificate_a10_a03_a04_a09 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
