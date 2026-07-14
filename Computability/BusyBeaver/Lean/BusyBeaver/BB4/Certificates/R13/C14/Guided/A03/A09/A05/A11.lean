import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a03_a09_a05_a11 : Guided.Work :=
  after [a03, a09, a05, a11]

def certificate_a03_a09_a05_a11 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a03_a09_a05_a11 :
    work_a03_a09_a05_a11.check certificate_a03_a09_a05_a11 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
