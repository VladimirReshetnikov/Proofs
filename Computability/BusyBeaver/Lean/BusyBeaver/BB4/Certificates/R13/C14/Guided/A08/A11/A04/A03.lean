import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a08_a11_a04_a03 : Guided.Work :=
  after [a08, a11, a04, a03]

def certificate_a08_a11_a04_a03 : Guided.Certificate :=
  Guided.Certificate.bool2

theorem verified_a08_a11_a04_a03 :
    work_a08_a11_a04_a03.check certificate_a08_a11_a04_a03 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
