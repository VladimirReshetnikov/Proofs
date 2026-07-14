import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a11_a12_a15_a12 : Guided.Work :=
  after [a11, a12, a15, a12]

def certificate_a11_a12_a15_a12 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a11_a12_a15_a12 :
    work_a11_a12_a15_a12.check certificate_a11_a12_a15_a12 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
