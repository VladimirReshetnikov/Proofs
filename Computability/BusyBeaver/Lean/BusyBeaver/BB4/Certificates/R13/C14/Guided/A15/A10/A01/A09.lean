import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a15_a10_a01_a09 : Guided.Work :=
  after [a15, a10, a01, a09]

def certificate_a15_a10_a01_a09 : Guided.Certificate :=
  Guided.Certificate.bool3

theorem verified_a15_a10_a01_a09 :
    work_a15_a10_a01_a09.check certificate_a15_a10_a01_a09 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
