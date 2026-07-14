import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a01_a15_a09_a01 : Guided.Work :=
  after [a01, a15, a09, a01]

def certificate_a01_a15_a09_a01 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a01_a15_a09_a01 :
    work_a01_a15_a09_a01.check certificate_a01_a15_a09_a01 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
