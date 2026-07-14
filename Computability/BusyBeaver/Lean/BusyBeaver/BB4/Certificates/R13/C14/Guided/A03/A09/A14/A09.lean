import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a03_a09_a14_a09 : Guided.Work :=
  after [a03, a09, a14, a09]

def certificate_a03_a09_a14_a09 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a03_a09_a14_a09 :
    work_a03_a09_a14_a09.check certificate_a03_a09_a14_a09 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
