# Third-party notices

`CombinatoryLogic/SKIArithmetic.lean` and
`CombinatoryLogic/PartrecToSKI.lean` are adapted and modified from the
Combinatory Logic Library (`leanprover/cslib`) pull request #403 at commit
`0c998e71`. The retained upstream copyright notices name Thomas Waring and
Jesse Alama.

`CombinatoryLogic/SKIConfluence.lean` is adapted and modified from
`leanprover/cslib`'s
`Cslib/Languages/CombinatoryLogic/Confluence.lean`, blob
`9fc3c7d18b2fc9eddaa63a59f90b8967c59a3743` at repository commit
`e5ed905c3d004cdbf7ee1ed17ad7bee19abd7915`. Its retained upstream
copyright notice names Thomas Waring.

`CombinatoryLogic/SKIEvaluation.lean` is adapted and modified from
`leanprover/cslib`'s
`Cslib/Languages/CombinatoryLogic/Evaluation.lean`, blob
`500a2f66a63c1395bef36ac2a101d31fd9e1776f` at repository commit
`e5ed905c3d004cdbf7ee1ed17ad7bee19abd7915`. Its retained upstream
copyright notice names Thomas Waring. Recursion- and Rice-theorem material
from the upstream file is not included.

`CombinatoryLogic/SKIChurchConfluence.lean` adapts the `churchK` normal-form
argument from the same upstream Evaluation blob and commit. It connects that
argument to the local `IsChurch`, `toChurch`, and `ObservesChurch` relations.
Its retained upstream copyright notice names Thomas Waring.

These five files are distributed under the Apache License, Version 2.0,
whose text is in `LICENSE-Apache-2.0`.

The remainder of this directory continues to use the repository's root
license unless an individual file says otherwise.
