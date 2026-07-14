import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a09_a10_a15_a01 : Guided.Work :=
  after [a09, a10, a15, a01]

def certificate_a09_a10_a15_a01 : Guided.Certificate :=
  Guided.Certificate.bool2

theorem verified_a09_a10_a15_a01 :
    work_a09_a10_a15_a01.check certificate_a09_a10_a15_a01 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
