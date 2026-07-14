import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a00_a11_a10_a07 : Guided.Work :=
  after [a00, a11, a10, a07]

def certificate_a00_a11_a10_a07 : Guided.Certificate :=
  Guided.Certificate.bool3

theorem verified_a00_a11_a10_a07 :
    work_a00_a11_a10_a07.check certificate_a00_a11_a10_a07 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
