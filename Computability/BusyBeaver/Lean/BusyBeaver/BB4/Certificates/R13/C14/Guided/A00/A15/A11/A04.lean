import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a00_a15_a11_a04 : Guided.Work :=
  after [a00, a15, a11, a04]

def certificate_a00_a15_a11_a04 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a00_a15_a11_a04 :
    work_a00_a15_a11_a04.check certificate_a00_a15_a11_a04 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
