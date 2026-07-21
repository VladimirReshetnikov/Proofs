(**
  The presently justified provability statement for bounded consistency.

  For every *metatheoretic* level, the existing bounded-consistency theorem
  gives a concrete PA derivation.  The first derivability condition from
  [RawCodedPAProvability] quotes that derivation back into PA.  Consequently
  PA proves, separately at every standard level, that PA proves the
  corresponding bounded-consistency sentence.

  The binder in the theorem below intentionally remains outside [BProv].
  Moving it into the object formula would require a single arithmetized
  proof compiler that also works at nonstandard levels in arbitrary models;
  pointwise semantic completeness does not supply such a compiler.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From BoundedPAConsistency Require Import
  RawCodedRestrictedPAConsistency
  RawCodedRestrictedPAConsistencyTheorem
  RawCodedPAProvability.

Module PABoundedRawCodedPAProvabilityRestrictedConsistency.

Import ListNotations.
Import PA.
Import PABoundedRawCodedRestrictedPAConsistency.
Import PABoundedRawCodedRestrictedPAConsistencyTheorem.
Import PABoundedRawCodedPAProvability.

Definition restrictedPAConsistencyProvabilityFormula
    (level : nat) : formula :=
  codedPAProvabilityFormula (restrictedPAConsistencyFormula level).

Theorem PA_BProv_restrictedPAConsistencyProvabilityFormula : forall level,
  Formula.BProv Formula.Ax_s []
    (restrictedPAConsistencyProvabilityFormula level).
Proof.
  intro level.
  apply PA_BProv_codedPAProvability_of_BProv.
  exact (PA_BProv_restrictedPAConsistencyFormula level).
Qed.

End PABoundedRawCodedPAProvabilityRestrictedConsistency.
