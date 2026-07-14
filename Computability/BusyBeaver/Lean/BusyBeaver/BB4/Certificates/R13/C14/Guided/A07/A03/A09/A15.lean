import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a07_a03_a09_a15 : Guided.Work :=
  after [a07, a03, a09, a15]

def certificate_a07_a03_a09_a15 : Guided.Certificate :=
  Guided.Certificate.bool3

theorem verified_a07_a03_a09_a15 :
    work_a07_a03_a09_a15.check certificate_a07_a03_a09_a15 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
