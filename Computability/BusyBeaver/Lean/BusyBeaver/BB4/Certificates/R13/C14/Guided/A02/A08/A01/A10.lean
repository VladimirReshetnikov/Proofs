import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a02_a08_a01_a10 : Guided.Work :=
  after [a02, a08, a01, a10]

def certificate_a02_a08_a01_a10 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a02_a08_a01_a10 :
    work_a02_a08_a01_a10.check certificate_a02_a08_a01_a10 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
