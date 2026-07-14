import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a11_a08_a11_a15 : Guided.Work :=
  after [a11, a08, a11, a15]

def certificate_a11_a08_a11_a15 : Guided.Certificate :=
  Guided.Certificate.bool2

theorem verified_a11_a08_a11_a15 :
    work_a11_a08_a11_a15.check certificate_a11_a08_a11_a15 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
