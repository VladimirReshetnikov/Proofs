# Rocq 9.2 compatibility overlay

Rocq 9.2 split the prover and standard library into `rocq-*` packages.  As of
July 2026, Coquelicot 3.4.4 and Interval 4.11.4 still request the historical
`coq-core` and `coq-stdlib` package names, and the released MathComp 2.5 opam
metadata excludes Rocq 9.2.  The proof sources themselves remain compatible.
The released Elpi plugin 3.4.0 also advertises 9.2 compatibility, but its build
selects APIs from the standalone standard-library version (9.1) rather than the
prover version (9.2).  The installer pins a repair derived from upstream
`master` that selects the Rocq 9.2 API explicitly.

[`Install.ps1`](Install.ps1) installs two empty package-name adapters and pins
the official Elpi and MathComp repositories at known Rocq-9.2-compatible
revisions.  It then installs Rocq 9.2, its standalone standard library,
Coquelicot, Interval, and MetaRocq into the selected opam switch.

```powershell
pwsh -File Tools/Rocq92Compat/Install.ps1
```

The adapters contain no binaries or theories.  `rocq-core` and `rocq-stdlib`
remain the sole providers of the implementation and standard library.

On Windows, the installer also compiles a tiny launcher and exposes native
`coqc.exe`, `coqdep.exe`, and related entry points.  The launcher inserts the
appropriate Rocq 9.2 subcommand and prevents Dune from resolving an older Rocq
Platform executable before a `.cmd` shim.

Finally, the bundled local opam repository adjusts three Windows-only build
commands from `./remake` to the generated `./remake.exe`.  Package sources,
versions, dependency constraints, and release checksums are unchanged.  The
installer provides unprefixed aliases to opam's matching MinGW compiler, so
`configure` cannot mix a WinLibs compiler with opam's runtime DLLs.
It also discards a stale `.remake` dependency cache before a Windows retry,
because a loader-level interruption can leave that derived file truncated.
Coquelicot and Interval use one `remake` worker on Windows because their
parallel recursive dependency scans race while reading that same cache.
