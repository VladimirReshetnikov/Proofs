import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a00_a11_a06_a00 : Guided.Work :=
  after [a00, a11, a06, a00]

def certificate_a00_a11_a06_a00 : Guided.Certificate :=
  Guided.Certificate.bool2

theorem verified_a00_a11_a06_a00 :
    work_a00_a11_a06_a00.check certificate_a00_a11_a06_a00 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
