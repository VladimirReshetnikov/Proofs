import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a01_a11_a12_a00 : Guided.Work :=
  after [a01, a11, a12, a00]

def certificate_a01_a11_a12_a00 : Guided.Certificate :=
  Guided.Certificate.bool2

theorem verified_a01_a11_a12_a00 :
    work_a01_a11_a12_a00.check certificate_a01_a11_a12_a00 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
