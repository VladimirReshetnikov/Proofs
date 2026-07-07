# Coq Ports of LeanProofs

- Created (UTC): 2026-07-07T03:24:49Z
- Repository HEAD: f3be2772be5658f305f509b584b0cb99d97cbe7a

This directory contains Rocq/Coq ports of proof modules from the root
`src/Lean/LeanProofs/` Lean workspace.  The ports are intentionally
Coq-idiomatic rather than line-by-line translations: each module preserves the
mathematical certificate surface where practical, but uses Coq standard-library
definitions, tactics, and proof organization.

The SetTheory project already has its own Coq development in
`src/Lean/SetTheory/`; it is not duplicated here.

Current ports:

- `Nicod.v` ports the NAND language, Nicod axiom/rule derivations, soundness,
  and functional-completeness lemmas from `Nicod.lean`.
- `ArctanSquareIdentity.v` ports the quadratic arctangent identity proof.
- `EquationalLogic.v` ports the executable first-order equational proof
  checker and its soundness theorem.
- `WolframBooleanCertificates.v` ports the Wolfram/Meredith generated
  equational certificates against that checker.
- `WolframBooleanHuntingtonCertificates.v` ports the generated
  Sheffer-to-Huntington certificate.

Build from `src/Lean/`:

```powershell
coqc -Q CoqProofs LeanProofsCoq CoqProofs/Nicod.v
coqc -Q CoqProofs LeanProofsCoq CoqProofs/ArctanSquareIdentity.v
coqc -Q CoqProofs LeanProofsCoq CoqProofs/EquationalLogic.v
coqc -Q CoqProofs LeanProofsCoq CoqProofs/WolframBooleanCertificates.v
coqc -Q CoqProofs LeanProofsCoq CoqProofs/WolframBooleanHuntingtonCertificates.v
```
