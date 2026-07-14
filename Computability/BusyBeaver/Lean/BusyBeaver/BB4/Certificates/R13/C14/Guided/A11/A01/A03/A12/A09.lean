import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a11_a01_a03_a12_a09 : Guided.Work :=
  after [a11, a01, a03, a12, a09]

def certificate_a11_a01_a03_a12_a09 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a11_a01_a03_a12_a09 :
    work_a11_a01_a03_a12_a09.check certificate_a11_a01_a03_a12_a09 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
