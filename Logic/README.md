# Logic

- [`FirstOrder/`](FirstOrder/) is a reusable one-binary-relation first-order
  syntax and semantics, natural-deduction calculus, soundness proof, Goedel
  completeness theorem, compactness lift, and deductive-transfer machinery.
- [`Propositional/ShefferStroke/`](Propositional/ShefferStroke/) formalizes
  NAND/NOR translations and Nicod's single-axiom calculus.
- [`Equational/`](Equational/) contains the sound equational checker and the
  Wolfram/Meredith/Sheffer/Huntington Boolean-algebra certificates.
- [`Interpretability/PAHF/`](Interpretability/PAHF/) proves the deductive
  bi-interpretation of PA with finite-generation hereditary finite set theory.

The FirstOrder and PAHF Lean projects are mathlib-free and have standalone
Lake configurations as well as root integration targets.
