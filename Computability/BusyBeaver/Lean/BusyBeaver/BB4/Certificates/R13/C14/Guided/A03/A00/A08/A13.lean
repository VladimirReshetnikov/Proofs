import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a03_a00_a08_a13 : Guided.Work :=
  after [a03, a00, a08, a13]

def certificate_a03_a00_a08_a13 : Guided.Certificate :=
  Guided.Certificate.bool2

theorem verified_a03_a00_a08_a13 :
    work_a03_a00_a08_a13.check certificate_a03_a00_a08_a13 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
