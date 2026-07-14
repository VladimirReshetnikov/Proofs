# Computability

[`BusyBeaver/`](BusyBeaver/) contains the repository-authored Busy Beaver
machine model, domination theorems, exact small-state score certificates, and
bridges to the vendored time certificates under [`../lib/Coq-BB5/`](../lib/Coq-BB5/).

The score and time functions are distinct measures. The proved values
`Sigma(2)=4`, `Sigma(3)=6`, `Sigma(4)=13` and `BB(2)=6`, `BB(3)=21`,
`BB(4)=107` therefore intentionally differ.

The Lean BB2/BB3 classifications are large opt-in targets. The Lean BB4 TNF
reduction is sound, while its exhaustive root equality remains conditional.
