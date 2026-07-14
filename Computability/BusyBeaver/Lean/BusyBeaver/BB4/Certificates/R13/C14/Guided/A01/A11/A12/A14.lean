import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a01_a11_a12_a14 : Guided.Work :=
  after [a01, a11, a12, a14]

def certificate_a01_a11_a12_a14 : Guided.Certificate :=
  Guided.Certificate.bool2

theorem verified_a01_a11_a12_a14 :
    work_a01_a11_a12_a14.check certificate_a01_a11_a12_a14 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
