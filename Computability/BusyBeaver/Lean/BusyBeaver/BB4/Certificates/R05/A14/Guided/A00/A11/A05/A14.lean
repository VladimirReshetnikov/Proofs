import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a00_a11_a05_a14 : Guided.Work :=
  after [a00, a11, a05, a14]

def certificate_a00_a11_a05_a14 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a00_a11_a05_a14 :
    work_a00_a11_a05_a14.check certificate_a00_a11_a05_a14 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
