import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a15_a02_a07 : Guided.Work :=
  after [a15, a02, a07]

def certificate_a15_a02_a07 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a15_a02_a07 :
    work_a15_a02_a07.check certificate_a15_a02_a07 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
