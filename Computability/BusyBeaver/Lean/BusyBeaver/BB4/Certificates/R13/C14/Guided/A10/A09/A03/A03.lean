import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a10_a09_a03_a03 : Guided.Work :=
  after [a10, a09, a03, a03]

def certificate_a10_a09_a03_a03 : Guided.Certificate :=
  Guided.Certificate.bool2

theorem verified_a10_a09_a03_a03 :
    work_a10_a09_a03_a03.check certificate_a10_a09_a03_a03 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
