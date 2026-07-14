import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a09_a11_a05_a15 : Guided.Work :=
  after [a09, a11, a05, a15]

def certificate_a09_a11_a05_a15 : Guided.Certificate :=
  Guided.Certificate.bool2

theorem verified_a09_a11_a05_a15 :
    work_a09_a11_a05_a15.check certificate_a09_a11_a05_a15 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
