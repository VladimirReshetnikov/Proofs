import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a01_a10_a15_a13 : Guided.Work :=
  after [a01, a10, a15, a13]

def certificate_a01_a10_a15_a13 : Guided.Certificate :=
  Guided.Certificate.bool2

theorem verified_a01_a10_a15_a13 :
    work_a01_a10_a15_a13.check certificate_a01_a10_a15_a13 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
