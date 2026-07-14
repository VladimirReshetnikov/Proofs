import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a09_a11_a01_a05 : Guided.Work :=
  after [a09, a11, a01, a05]

def certificate_a09_a11_a01_a05 : Guided.Certificate :=
  Guided.Certificate.bool2

theorem verified_a09_a11_a01_a05 :
    work_a09_a11_a01_a05.check certificate_a09_a11_a01_a05 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
