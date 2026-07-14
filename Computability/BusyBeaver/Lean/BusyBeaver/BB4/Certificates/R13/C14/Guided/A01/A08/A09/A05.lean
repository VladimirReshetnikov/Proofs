import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a01_a08_a09_a05 : Guided.Work :=
  after [a01, a08, a09, a05]

def certificate_a01_a08_a09_a05 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a01_a08_a09_a05 :
    work_a01_a08_a09_a05.check certificate_a01_a08_a09_a05 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
