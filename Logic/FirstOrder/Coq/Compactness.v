(* ===================================================================== *)
(*  Compactness.v                                                        *)
(*                                                                       *)
(*  The semantic compactness theorem for the repository's first-order    *)
(*  language.  Theories are predicates on formulas and finite            *)
(*  subtheories are lists.  The hard implication combines finitary       *)
(*  proof support, soundness, and the Henkin model-existence theorem      *)
(*  [model_of_BCon].                                                      *)
(* ===================================================================== *)

From Stdlib Require Import List.
From FirstOrder Require Import Fol Calculus Completeness.

Import ListNotations.

Module FirstOrderCompactness.

Definition TheoryHasModel (T : form -> Prop) : Prop :=
  exists (Dom : Type) (m : Dom -> Dom -> Prop) (v : nat -> Dom),
    forall phi, T phi -> Sat Dom m v phi.

Definition FiniteSubtheoriesHaveModels (T : form -> Prop) : Prop :=
  forall G : list form,
    (forall phi, In phi G -> T phi) ->
    exists (Dom : Type) (m : Dom -> Dom -> Prop) (v : nat -> Dom),
      forall phi, In phi G -> Sat Dom m v phi.

Theorem theoryHasModel_finiteSubtheoriesHaveModels :
  forall T, TheoryHasModel T -> FiniteSubtheoriesHaveModels T.
Proof.
  intros T [Dom [m [v Hmodel]]] G HGT.
  exists Dom, m, v.
  intros phi Hphi.
  exact (Hmodel phi (HGT phi Hphi)).
Qed.

Theorem theoryHasModel_of_finiteSubtheoriesHaveModels :
  forall T, Sentences T -> FiniteSubtheoriesHaveModels T -> TheoryHasModel T.
Proof.
  intros T Hsentences Hfinite.
  assert (Hcon : BCon T nil).
  {
    intros [G [HGT Hbot]].
    destruct (Hfinite G HGT) as [Dom [m [v Hmodel]]].
    rewrite app_nil_r in Hbot.
    exact (soundness Dom m G fBot Hbot v Hmodel).
  }
  destruct (model_of_BCon T nil Hsentences Hcon)
    as [Dom [m [v [Hmodel _]]]].
  exists Dom, m, v.
  exact Hmodel.
Qed.

(** **First-order compactness theorem.**  A theory of sentences has a model
    if and only if every finite subtheory has a model. *)
Theorem compactness :
  forall T, Sentences T ->
    (TheoryHasModel T <-> FiniteSubtheoriesHaveModels T).
Proof.
  intros T Hsentences.
  split.
  - apply theoryHasModel_finiteSubtheoriesHaveModels.
  - apply theoryHasModel_of_finiteSubtheoriesHaveModels.
    exact Hsentences.
Qed.

End FirstOrderCompactness.
