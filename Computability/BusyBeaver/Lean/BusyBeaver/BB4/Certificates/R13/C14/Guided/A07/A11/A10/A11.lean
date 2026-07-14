import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a07_a11_a10_a11 : Guided.Work :=
  after [a07, a11, a10, a11]

def certificate_a07_a11_a10_a11 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a07_a11_a10_a11 :
    work_a07_a11_a10_a11.check certificate_a07_a11_a10_a11 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
