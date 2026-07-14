import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a01_a09_a00_a12 : Guided.Work :=
  after [a01, a09, a00, a12]

def certificate_a01_a09_a00_a12 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a01_a09_a00_a12 :
    work_a01_a09_a00_a12.check certificate_a01_a09_a00_a12 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
