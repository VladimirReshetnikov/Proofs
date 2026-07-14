import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a03_a15_a00_a11 : Guided.Work :=
  after [a03, a15, a00, a11]

def certificate_a03_a15_a00_a11 : Guided.Certificate :=
  Guided.Certificate.bool2

theorem verified_a03_a15_a00_a11 :
    work_a03_a15_a00_a11.check certificate_a03_a15_a00_a11 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
