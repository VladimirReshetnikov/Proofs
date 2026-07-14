# Coq Library of Undecidability Proofs — focused source snapshot

This directory vendors the transitive Rocq source closure needed for the
partial-recursive-function/weak-call-by-value-lambda-calculus equivalence from
the [Coq Library of Undecidability
Proofs](https://github.com/uds-psl/coq-library-undecidability).

- Upstream branch: `rocq-9.0`
- Upstream commit: `806690d024009b11a4e4e6354f8ee63bdcacc3a6`
- Upstream license: Mozilla Public License 2.0, retained in [`LICENSE`](LICENSE)
- Logical load path: `Undecidability`
- Tested toolchain: Rocq 9.0.1 with MetaRocq

The snapshot contains 186 unmodified `.v` files (1,946,937 bytes). They are
the union of the transitive dependencies of these two upstream endpoints:

- `theories/Synthetic/Models_Equivalent.v`
- `theories/L/Util/ClosedLAdmissible.v`

[`SOURCE_MANIFEST.txt`](SOURCE_MANIFEST.txt) records the exact files in a
valid dependency order. No generated `.vo`, `.vos`, `.vok`, `.glob`, or
`.aux` artifact is vendored. The nested `.gitattributes` disables line-ending
conversion so the committed upstream source blobs remain byte-for-byte exact.

The source selection was computed from a clean checkout of the pinned commit
with:

```powershell
coqdep `
  -Q theories Undecidability `
  -sort `
  theories/Synthetic/Models_Equivalent.v `
  theories/L/Util/ClosedLAdmissible.v
```

The repository-authored corollary using this snapshot is
`Computability/CombinatoryLogic/Coq/RecursiveEquivalence.v`. That corollary is
separate from this MPL-2.0-covered subtree.

## Updating the snapshot

Check out the intended upstream commit, rerun the `coqdep` command above,
copy exactly the reported source files while preserving their paths below
`theories/`, and regenerate `SOURCE_MANIFEST.txt` and the matching source
entries in the root `_CoqProject`. Preserve the upstream license and update
the provenance and byte/file counts in this document.
