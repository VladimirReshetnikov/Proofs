# No finite PA model — Rocq/Coq

This development reuses both PA-model interfaces from
`Logic/Interpretability/PAHF/Coq/PAHF.v`: the top-level `PAModel` and the
distinct nested `PA.Model` used by the syntactic development.
A `FinitePresentation A` is explicit mutually inverse encoding and decoding
between `A` and `Fin.t n`. The proof transports this to the standard finite
enumeration, applies the constructive finite-endomap theorem, and contradicts
PA successor injectivity plus zero's absence from the successor image.

Only those two successor axioms are used. Separate headline theorems cover
`PAModel` and `PA.Model`, and neither has classical assumptions despite the
broader imports needed by other parts of `PAHF.v`.

The local `_CoqProject` provides the `FirstOrder`, `PAHF`, and
`NoFinitePAModel` logical mappings. Once the PAHF dependency is built, run
from this directory:

```powershell
coqc -Q ../../../FirstOrder/Coq FirstOrder -Q ../../../Interpretability/PAHF/Coq PAHF -Q . NoFinitePAModel NoFiniteModel.v
coqc -Q ../../../FirstOrder/Coq FirstOrder -Q ../../../Interpretability/PAHF/Coq PAHF -Q . NoFinitePAModel Audit.v
coqchk -silent -Q ../../../FirstOrder/Coq FirstOrder -Q ../../../Interpretability/PAHF/Coq PAHF -Q . NoFinitePAModel NoFinitePAModel.NoFiniteModel NoFinitePAModel.Audit
```
