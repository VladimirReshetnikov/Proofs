(* ===================================================================== *)
(*  ClassicalCompleteness.v                                              *)
(*                                                                       *)
(*  Textbook interfaces for Goedel's completeness theorem, backed by     *)
(*  the independent Henkin construction in Completeness.v.               *)
(* ===================================================================== *)

From Stdlib Require Import List.
From FirstOrder Require Import Fol Calculus Completeness Compactness.

Import ListNotations.
Import FirstOrderCompactness.

Module FirstOrderClassicalCompleteness.

Definition SemanticConsequence (G : list form) (phi : form) : Prop :=
  forall (Dom : Type) (m : Dom -> Dom -> Prop) (v : nat -> Dom),
    (forall g, In g G -> Sat Dom m v g) -> Sat Dom m v phi.

Definition SyntacticConsequence (G : list form) (phi : form) : Prop :=
  Prov G phi.

Definition LogicallyValid (phi : form) : Prop :=
  SemanticConsequence nil phi.

Definition TheorySemanticConsequence (T : form -> Prop) (phi : form) : Prop :=
  forall (Dom : Type) (m : Dom -> Dom -> Prop) (v : nat -> Dom),
    (forall g, T g -> Sat Dom m v g) -> Sat Dom m v phi.

Definition TheorySyntacticConsequence (T : form -> Prop) (phi : form) : Prop :=
  BProv T nil phi.

Definition TheoryConsistent (T : form -> Prop) : Prop :=
  BCon T nil.

(** **Goedel completeness, finite-context form:** semantic consequence
    implies syntactic consequence. *)
Theorem godel_completeness :
  forall G phi, SemanticConsequence G phi -> SyntacticConsequence G phi.
Proof. exact completeness. Qed.

(** Soundness and completeness identify derivability with semantic
    consequence. *)
Theorem godel_soundness_and_completeness :
  forall G phi, SyntacticConsequence G phi <-> SemanticConsequence G phi.
Proof. exact prov_iff_valid. Qed.

(** Goedel's original validity formulation. *)
Theorem godel_original_completeness :
  forall phi, LogicallyValid phi -> Prov nil phi.
Proof. exact (godel_completeness nil). Qed.

(** **Goedel completeness for arbitrary sentence theories:** semantic
    consequence has a derivation using finitely many axioms of the theory. *)
Theorem godel_completeness_for_theories :
  forall T phi, Sentences T ->
    TheorySemanticConsequence T phi -> TheorySyntacticConsequence T phi.
Proof.
  intros T phi HT Hsemantic.
  apply (completeness_inf_context T nil phi HT).
  intros Dom m v Hmodel _.
  exact (Hsemantic Dom m v Hmodel).
Qed.

(** Soundness and completeness for arbitrary sentence theories. *)
Theorem godel_soundness_and_completeness_for_theories :
  forall T phi, Sentences T ->
    (TheorySyntacticConsequence T phi <-> TheorySemanticConsequence T phi).
Proof.
  intros T phi HT. split.
  - intros Hproof Dom m v Hmodel.
    apply (soundness_BProv Dom m T nil phi Hproof v Hmodel).
    intros g Hg. contradiction.
  - exact (godel_completeness_for_theories T phi HT).
Qed.

(** **Model-existence form of Goedel completeness:** every syntactically
    consistent theory of sentences has a model. *)
Theorem godel_model_existence :
  forall T, Sentences T -> TheoryConsistent T -> TheoryHasModel T.
Proof.
  intros T HT Hconsistent.
  destruct (model_of_BCon T nil HT Hconsistent)
    as [Dom [m [v [Hmodel _]]]].
  exists Dom, m, v.
  exact Hmodel.
Qed.

End FirstOrderClassicalCompleteness.
