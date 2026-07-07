(*
  Coq port of the finite TSV-metadata layer from
  LeanProofs/A198683N12Magnitude.lean.

  The Lean module also contains complex-analytic separation lemmas.  This Coq
  module ports the retained-data certificate: among the 5139 n = 12 candidate
  rows, candidate 57 is the unique row marked by each overflow/magnitude flag.
  Instead of embedding three literal 5139-entry lists, the Coq port generates
  the same one-hot lists directly.
*)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List.

Import ListNotations.
Set Implicit Arguments.
Open Scope nat_scope.
Set Warnings "-abstract-large-number".

Module LeanProofs.
Module A198683N12Magnitude.

Fixpoint positionsWithLabelFrom (target idx : nat) (labels : list nat)
    : list nat :=
  match labels with
  | [] => []
  | label :: rest =>
      if Nat.eqb label target then
        idx :: positionsWithLabelFrom target (idx + 1) rest
      else
        positionsWithLabelFrom target (idx + 1) rest
  end.

Definition positionsWithLabel (target : nat) (labels : list nat) : list nat :=
  positionsWithLabelFrom target 0 labels.

Definition flagAt (target idx : nat) : nat :=
  if Nat.eqb idx target then 1 else 0.

Fixpoint oneHotFrom (len target idx : nat) : list nat :=
  match len with
  | 0 => []
  | S len' => flagAt target idx :: oneHotFrom len' target (S idx)
  end.

Definition oneHot (len target : nat) : list nat :=
  oneHotFrom len target 0.

Theorem oneHotFrom_length (len target idx : nat) :
    length (oneHotFrom len target idx) = len.
Proof.
  revert target idx.
  induction len as [|len ih]; simpl.
  - intros target idx. reflexivity.
  - intros target idx. now rewrite ih.
Qed.

Theorem oneHot_length (len target : nat) :
    length (oneHot len target) = len.
Proof.
  apply oneHotFrom_length.
Qed.

Theorem oneHotFrom_nth (len target idx offset : nat)
    (hoffset : offset < len) :
    nth offset (oneHotFrom len target idx) 0 =
      flagAt target (idx + offset).
Proof.
  revert idx offset hoffset.
  induction len as [|len ih]; intros idx offset hoffset.
  - lia.
  - destruct offset as [|offset].
    + simpl. now rewrite Nat.add_0_r.
    + simpl.
      rewrite ih by lia.
      f_equal.
      lia.
Qed.

Theorem oneHot_nth (len target idx : nat) (hidx : idx < len) :
    nth idx (oneHot len target) 0 = flagAt target idx.
Proof.
  unfold oneHot.
  rewrite oneHotFrom_nth by exact hidx.
  now rewrite Nat.add_0_l.
Qed.

Theorem oneHot_zero_except (len target idx : nat)
    (hidx : idx < len) (hne : idx <> target) :
    nth idx (oneHot len target) 0 = 0.
Proof.
  rewrite oneHot_nth by exact hidx.
  unfold flagAt.
  destruct (Nat.eqb idx target) eqn:heq.
  - apply Nat.eqb_eq in heq. contradiction.
  - reflexivity.
Qed.

Definition n12CandidateRows : nat := 5139.

Definition overflowCandidateIndex : nat := 57.

Definition hugeNegativeReExponentFlags : list nat :=
  oneHot n12CandidateRows overflowCandidateIndex.

Definition negativeReExponentAboveTenFlags : list nat :=
  oneHot n12CandidateRows overflowCandidateIndex.

Definition overflowRegimeFlags : list nat :=
  oneHot n12CandidateRows overflowCandidateIndex.

Theorem hugeNegativeReExponentFlags_length :
    length hugeNegativeReExponentFlags = 5139.
Proof. reflexivity. Qed.

Theorem hugeNegativeReExponentFlags_only_fifty_seven :
    positionsWithLabel 1 hugeNegativeReExponentFlags = [57].
Proof. vm_compute. reflexivity. Qed.

Theorem hugeNegativeReExponentFlags_fifty_seven :
    nth 57 hugeNegativeReExponentFlags 0 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem hugeNegativeReExponentFlags_zero_except_fifty_seven :
    forall i : nat,
      i < length hugeNegativeReExponentFlags ->
      i <> 57 ->
      nth i hugeNegativeReExponentFlags 0 = 0.
Proof.
  intros i hi hne.
  unfold hugeNegativeReExponentFlags, n12CandidateRows,
    overflowCandidateIndex in *.
  rewrite oneHot_length in hi.
  exact (oneHot_zero_except (len := 5139) (target := 57) (idx := i) hi hne).
Qed.

Theorem negativeReExponentAboveTenFlags_length :
    length negativeReExponentAboveTenFlags = 5139.
Proof. reflexivity. Qed.

Theorem negativeReExponentAboveTenFlags_only_fifty_seven :
    positionsWithLabel 1 negativeReExponentAboveTenFlags = [57].
Proof. vm_compute. reflexivity. Qed.

Theorem negativeReExponentAboveTenFlags_fifty_seven :
    nth 57 negativeReExponentAboveTenFlags 0 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem negativeReExponentAboveTenFlags_zero_except_fifty_seven :
    forall i : nat,
      i < length negativeReExponentAboveTenFlags ->
      i <> 57 ->
      nth i negativeReExponentAboveTenFlags 0 = 0.
Proof.
  intros i hi hne.
  unfold negativeReExponentAboveTenFlags, n12CandidateRows,
    overflowCandidateIndex in *.
  rewrite oneHot_length in hi.
  exact (oneHot_zero_except (len := 5139) (target := 57) (idx := i) hi hne).
Qed.

Theorem overflowRegimeFlags_length :
    length overflowRegimeFlags = 5139.
Proof. reflexivity. Qed.

Theorem overflowRegimeFlags_only_fifty_seven :
    positionsWithLabel 1 overflowRegimeFlags = [57].
Proof. vm_compute. reflexivity. Qed.

Theorem overflowRegimeFlags_fifty_seven :
    nth 57 overflowRegimeFlags 0 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem overflowRegimeFlags_zero_except_fifty_seven :
    forall i : nat,
      i < length overflowRegimeFlags ->
      i <> 57 ->
      nth i overflowRegimeFlags 0 = 0.
Proof.
  intros i hi hne.
  unfold overflowRegimeFlags, n12CandidateRows,
    overflowCandidateIndex in *.
  rewrite oneHot_length in hi.
  exact (oneHot_zero_except (len := 5139) (target := 57) (idx := i) hi hne).
Qed.

Theorem hugeNegativeReExponentFlags_eq_overflow_positions :
    positionsWithLabel 1 hugeNegativeReExponentFlags =
      positionsWithLabel 1 overflowRegimeFlags.
Proof. vm_compute. reflexivity. Qed.

End A198683N12Magnitude.
End LeanProofs.
