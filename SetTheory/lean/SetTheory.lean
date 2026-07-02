/-
  SetTheory — Lean 4 port of the Rocq/Coq development in `src/SetTheory/`:
  Vladimir Reshetnikov's "Closure" axiomatization of set theory and its
  machine-checked equivalence with ZF.

  Module map (mirroring the Coq files):
  - `SetTheory.Fol`          ← Fol.v          (generic FOL over {∈, =})
  - `SetTheory.Calculus`     ← Calculus.v     (ND calculus + soundness)
  - `SetTheory.Completeness` ← Completeness.v (Gödel completeness, compactness)
  - `SetTheory.Zf`           ← Zf.v           (first-order ZF, recursion theorem)
  - `SetTheory.Equivalence`  ← Equivalence.v  (the Closure axiomatization T, T_iff_ZF)
  - `SetTheory.Forward`      ← Forward.v      (shallow forward trade, self-contained)
  - `SetTheory.Reverse`      ← Reverse.v      (shallow reverse trade, self-contained)
-/
import SetTheory.Fol
import SetTheory.Calculus
import SetTheory.Completeness
import SetTheory.Zf
import SetTheory.Equivalence
import SetTheory.Forward
import SetTheory.Reverse
