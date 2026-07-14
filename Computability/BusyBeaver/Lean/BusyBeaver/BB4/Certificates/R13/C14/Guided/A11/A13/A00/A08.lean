import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a11_a13_a00_a08 : Guided.Work :=
  after [a11, a13, a00, a08]

def certificate_a11_a13_a00_a08 : Guided.Certificate :=
  Guided.Certificate.bool2

theorem verified_a11_a13_a00_a08 :
    work_a11_a13_a00_a08.check certificate_a11_a13_a00_a08 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
