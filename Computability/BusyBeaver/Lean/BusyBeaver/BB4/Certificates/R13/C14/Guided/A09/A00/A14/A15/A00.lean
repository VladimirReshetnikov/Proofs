import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a09_a00_a14_a15_a00 : Guided.Work :=
  after [a09, a00, a14, a15, a00]

def certificate_a09_a00_a14_a15_a00 : Guided.Certificate :=
  Guided.Certificate.bool3

theorem verified_a09_a00_a14_a15_a00 :
    work_a09_a00_a14_a15_a00.check certificate_a09_a00_a14_a15_a00 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
