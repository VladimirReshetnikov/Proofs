/-
  AuditMathlib.lean — assumption audit for the mathlib-backed busy-beaver
  modules, the companion of `Audit.lean` for modules that the standalone
  (dependency-free) SetTheory workspace deliberately excludes.

  Like `BusyBeaverMathlib.lean` itself, this file is NOT imported by the
  workspace root `SetTheory.lean`; it is built from the root `src/Lean`
  Lake workspace (which exposes these sources as the `SetTheory` library
  pinned to mathlib v4.31.0):

      cd src/Lean
      lake build SetTheory.AuditMathlib

  Expected: only Lean's standard classical axioms
  (`propext`, `Classical.choice`, `Quot.sound`) — no `sorry`, no `axiom`.
-/
import SetTheory.BusyBeaverBB2
import SetTheory.BusyBeaverMathlib

open SetTheory

-- the compiler interface, proved unconditionally from mathlib's
-- recursion theory and Turing-machine reductions
#check @BusyBeaver.totalRecursiveMathlib_hasEventuallyAtMostLowerBoundCompiler
#print axioms BusyBeaver.totalRecursiveMathlib_hasEventuallyAtMostLowerBoundCompiler

-- the headline: any busy-beaver score function eventually dominates
-- every mathlib-total-recursive function `Nat -> Nat`
#check @BusyBeaver.sigma_eventually_dominates_every_totalRecursiveMathlib
#print axioms BusyBeaver.sigma_eventually_dominates_every_totalRecursiveMathlib

-- the exhaustive two-state score classification
#check @BusyBeaver.BB2.all_tables_score_le_four
#check @BusyBeaver.BB2.upperBound_two
#check @BusyBeaver.BB2.exactScore_two
#check @BusyBeaver.BB2.sigma_two_eq_four
#print axioms BusyBeaver.BB2.all_tables_score_le_four
#print axioms BusyBeaver.BB2.upperBound_two
#print axioms BusyBeaver.BB2.sigma_two_eq_four
