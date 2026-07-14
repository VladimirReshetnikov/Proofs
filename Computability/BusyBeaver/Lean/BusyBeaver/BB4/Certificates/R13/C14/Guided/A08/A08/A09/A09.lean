import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a08_a08_a09_a09 : Guided.Work :=
  after [a08, a08, a09, a09]

def certificate_a08_a08_a09_a09 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a08_a08_a09_a09 :
    work_a08_a08_a09_a09.check certificate_a08_a08_a09_a09 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
