import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a11_a04_a07_a04 : Guided.Work :=
  after [a11, a04, a07, a04]

def certificate_a11_a04_a07_a04 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a11_a04_a07_a04 :
    work_a11_a04_a07_a04.check certificate_a11_a04_a07_a04 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
