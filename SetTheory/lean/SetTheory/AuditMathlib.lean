/-
  AuditMathlib.lean — assumption audit for the mathlib-backed busy-beaver
  bridge, the companion of `Audit.lean` for the module that the standalone
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
