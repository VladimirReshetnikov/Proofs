import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C07.C01Leaf
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C07.Common

namespace SetTheory.BusyBeaver.BB4.Certificates

set_option maxRecDepth 10000 in
theorem seventhBranch_a13_a01_a02_a11_a12_a07_a01 : seventhBranch_a13_a01_a02_a11_a12_a07 a01 = true := by
  change TNF.checkFrom leaf 96 4 table_a13_a01_a02_a11_a12_a07_a01
    start_a13_a01_a02_a11_a12_a07_a01 = true
  rw [checkFrom_eq_zero_of_runAssigned leaf 4
    table_a13_a01_a02_a11_a12_a07_a01 96
    start_a13_a01_a02_a11_a12_a07_a01
    endpoint_a13_a01_a02_a11_a12_a07_a01
    replay_a13_a01_a02_a11_a12_a07_a01]
  simpa [TNF.checkFrom,
    endpoint_state_a13_a01_a02_a11_a12_a07_a01] using
      leaf_a13_a01_a02_a11_a12_a07_a01
        endpoint_a13_a01_a02_a11_a12_a07_a01

end SetTheory.BusyBeaver.BB4.Certificates
