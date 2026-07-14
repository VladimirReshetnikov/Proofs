import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a11_a12_a08_a03 : Guided.Work :=
  after [a11, a12, a08, a03]

def certificate_a11_a12_a08_a03 : Guided.Certificate :=
  Guided.Certificate.bool2

theorem verified_a11_a12_a08_a03 :
    work_a11_a12_a08_a03.check certificate_a11_a12_a08_a03 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
