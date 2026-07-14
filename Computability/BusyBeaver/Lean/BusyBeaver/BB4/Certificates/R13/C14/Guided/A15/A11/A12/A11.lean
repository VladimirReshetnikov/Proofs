import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a15_a11_a12_a11 : Guided.Work :=
  after [a15, a11, a12, a11]

def certificate_a15_a11_a12_a11 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a15_a11_a12_a11 :
    work_a15_a11_a12_a11.check certificate_a15_a11_a12_a11 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
