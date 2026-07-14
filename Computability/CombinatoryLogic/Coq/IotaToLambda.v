(* ===================================================================== *)
(*  IotaToLambda.v                                                     *)
(*                                                                       *)
(*  A faithful syntactic embedding of the Iota runtime calculus into     *)
(*  closed weak untyped lambda terms.  Runtime S and K receive their      *)
(*  canonical lambda terms, and                                          *)
(*                                                                       *)
(*      iota = lambda x. x S K.                                          *)
(*                                                                       *)
(*  Application is preserved exactly.  Every contextual runtime          *)
(*  contraction is simulated by a nonempty lambda reduction, and the     *)
(*  translation is injective even on the larger runtime syntax.           *)
(* ===================================================================== *)

From CombinatoryLogic Require Import Reduction Lambda Iota.

Set Implicit Arguments.

Module IotaToLambda.

Module L := UntypedLambda.
Module R := IotaRuntime.

Definition up {V : Type} (t : L.term V) : L.term (option V) :=
  L.map (@Some V) t.

Lemma subst0_up : forall (V : Type) (argument t : L.term V),
  L.subst0 argument (up t) = t.
Proof.
  intros V argument t.
  unfold up.
  apply L.subst0_map_some.
Qed.

(* Canonical closed lambda representatives, polymorphic in an unused      *)
(* ambient variable type.                                                 *)
Definition lambdaK {V : Type} : L.term V :=
  L.lam (L.lam (L.var (Some None))).

Definition lambdaS {V : Type} : L.term V :=
  L.lam (L.lam (L.lam
    (L.app
      (L.app (L.var (Some (Some None))) (L.var None))
      (L.app (L.var (Some None)) (L.var None))))).

Definition lambdaIota {V : Type} : L.term V :=
  L.lam (L.app (L.app (L.var None) lambdaS) lambdaK).

Lemma bind_lift_up : forall (A B : Type) (sigma : A -> L.term B) t,
  L.bind (L.liftSubst sigma) (up t) = up (L.bind sigma t).
Proof.
  intros A B sigma t.
  unfold up.
  rewrite L.bind_map.
  rewrite L.map_bind.
  apply L.bind_ext.
  intro x. reflexivity.
Qed.

Definition sBodyAfterX {V : Type} (x : L.term V) :
    L.term (option V) :=
  L.lam
    (L.app
      (L.app (up (up x)) (L.var None))
      (L.app (L.var (Some None)) (L.var None))).

Definition sAfterX {V : Type} (x : L.term V) : L.term V :=
  L.lam (sBodyAfterX x).

Definition sBodyAfterXY {V : Type} (x y : L.term V) :
    L.term (option V) :=
  L.app
    (L.app (up x) (L.var None))
    (L.app (up y) (L.var None)).

Definition sAfterXY {V : Type} (x y : L.term V) : L.term V :=
  L.lam (sBodyAfterXY x y).

Lemma lambdaIota_subst : forall (V : Type) (x : L.term V),
  L.subst0 x
    (L.app (L.app (L.var None) (@lambdaS (option V)))
      (@lambdaK (option V))) =
  L.app (L.app x (@lambdaS V)) (@lambdaK V).
Proof. reflexivity. Qed.

Lemma lambdaK_subst : forall (V : Type) (x : L.term V),
  L.subst0 x (L.lam (L.var (Some None))) = L.lam (up x).
Proof. reflexivity. Qed.

Lemma lambdaS_subst_x : forall (V : Type) (x : L.term V),
  L.subst0 x
    (L.lam (L.lam
      (L.app
        (L.app (L.var (Some (Some None))) (L.var None))
        (L.app (L.var (Some None)) (L.var None))))) =
  sAfterX x.
Proof. reflexivity. Qed.

Lemma lambdaS_subst_y : forall (V : Type) (x y : L.term V),
  L.subst0 y (sBodyAfterX x) = sAfterXY x y.
Proof.
  intros V x y.
  unfold sBodyAfterX, sAfterXY, sBodyAfterXY, L.subst0.
  cbn [L.bind L.liftSubst].
  rewrite bind_lift_up.
  fold (L.subst0 y (up x)).
  rewrite subst0_up.
  reflexivity.
Qed.

Lemma lambdaS_subst_z : forall (V : Type) (x y z : L.term V),
  L.subst0 z (sBodyAfterXY x y) =
  L.app (L.app x z) (L.app y z).
Proof.
  intros V x y z.
  unfold sBodyAfterXY, L.subst0, up.
  cbn [L.bind].
  rewrite !L.bind_map.
  rewrite !L.bind_var.
  reflexivity.
Qed.

Theorem lambdaIota_correct_positive : forall (V : Type) (x : L.term V),
  L.progresses (L.app (@lambdaIota V) x)
    (L.app (L.app x (@lambdaS V)) (@lambdaK V)).
Proof.
  intros V x.
  unfold L.progresses, lambdaIota.
  eapply Reduction.plus_step.
  - apply L.step_beta.
  - rewrite lambdaIota_subst.
    apply Reduction.star_refl.
Qed.

Theorem lambdaK_correct_positive : forall (V : Type) (x y : L.term V),
  L.progresses (L.app (L.app (@lambdaK V) x) y) x.
Proof.
  intros V x y.
  unfold L.progresses, lambdaK.
  eapply Reduction.plus_step.
  - apply L.step_app_left.
    apply L.step_beta.
  - rewrite lambdaK_subst.
    eapply Reduction.star_step.
    + apply L.step_beta.
    + rewrite subst0_up.
      apply Reduction.star_refl.
Qed.

Theorem lambdaS_correct_positive : forall (V : Type)
    (x y z : L.term V),
  L.progresses
    (L.app (L.app (L.app (@lambdaS V) x) y) z)
    (L.app (L.app x z) (L.app y z)).
Proof.
  intros V x y z.
  unfold L.progresses, lambdaS.
  eapply Reduction.plus_step.
  - apply L.step_app_left.
    apply L.step_app_left.
    apply L.step_beta.
  - rewrite lambdaS_subst_x.
    eapply Reduction.star_step.
    + apply L.step_app_left.
      apply L.step_beta.
    + rewrite lambdaS_subst_y.
      eapply Reduction.star_step.
      * apply L.step_beta.
      * rewrite lambdaS_subst_z.
        apply Reduction.star_refl.
Qed.

Fixpoint encodeRuntime (source : R.term) : L.term Empty_set :=
  match source with
  | R.iota => lambdaIota
  | R.konst => lambdaK
  | R.scomb => lambdaS
  | R.app lhs rhs => L.app (encodeRuntime lhs) (encodeRuntime rhs)
  end.

Theorem encodeRuntime_app : forall lhs rhs,
  encodeRuntime (R.app lhs rhs) =
  L.app (encodeRuntime lhs) (encodeRuntime rhs).
Proof. reflexivity. Qed.

Theorem encodeRuntime_step_positive : forall source target,
  R.step source target ->
  L.progresses (encodeRuntime source) (encodeRuntime target).
Proof.
  intros source target hstep.
  induction hstep as
    [x | x y | x y z | x x' y hstep IH | x y y' hstep IH].
  - cbn [encodeRuntime].
    apply lambdaIota_correct_positive.
  - cbn [encodeRuntime].
    apply lambdaK_correct_positive.
  - cbn [encodeRuntime].
    apply lambdaS_correct_positive.
  - cbn [encodeRuntime].
    now apply L.progresses_app_left.
  - cbn [encodeRuntime].
    now apply L.progresses_app_right.
Qed.

Theorem encodeRuntime_step : forall source target,
  R.step source target ->
  L.reaches (encodeRuntime source) (encodeRuntime target).
Proof.
  intros source target hstep.
  apply Reduction.plus_to_star.
  exact (encodeRuntime_step_positive hstep).
Qed.

Theorem encodeRuntime_steps : forall source target,
  R.reaches source target ->
  L.reaches (encodeRuntime source) (encodeRuntime target).
Proof.
  intros source target hsteps.
  induction hsteps as [source | source middle target hstep hsteps IH].
  - apply L.reaches_refl.
  - eapply L.reaches_trans.
    + exact (encodeRuntime_step hstep).
    + exact IH.
Qed.

Theorem encodeRuntime_progresses : forall source target,
  R.progresses source target ->
  L.progresses (encodeRuntime source) (encodeRuntime target).
Proof.
  intros source target hprogress.
  destruct hprogress as [source middle target hstep hsteps].
  unfold L.progresses, L.reaches in *.
  eapply Reduction.plus_star_trans.
  - exact (encodeRuntime_step_positive hstep).
  - exact (encodeRuntime_steps hsteps).
Qed.

Theorem encodeRuntime_injective : forall x y,
  encodeRuntime x = encodeRuntime y -> x = y.
Proof.
  induction x as [| | |xl IHxl xr IHxr]; intros y heq;
    destruct y as [| | |yl yr]; cbn [encodeRuntime] in heq;
    try reflexivity; try discriminate.
  injection heq as hleft hright.
  f_equal.
  - now apply IHxl.
  - now apply IHxr.
Qed.

Fixpoint encodePure (source : Iota.term) : L.term Empty_set :=
  match source with
  | Iota.iota => lambdaIota
  | Iota.app lhs rhs => L.app (encodePure lhs) (encodePure rhs)
  end.

Theorem encodePure_app : forall lhs rhs,
  encodePure (Iota.app lhs rhs) =
  L.app (encodePure lhs) (encodePure rhs).
Proof. reflexivity. Qed.

Theorem encode_embed : forall source,
  encodeRuntime (Iota.embed source) = encodePure source.
Proof.
  intro source.
  induction source as [|lhs IHlhs rhs IHrhs];
    cbn [Iota.embed encodeRuntime encodePure].
  - reflexivity.
  - now rewrite IHlhs, IHrhs.
Qed.

Theorem encodePure_injective : forall x y,
  encodePure x = encodePure y -> x = y.
Proof.
  intros x y heq.
  apply Iota.embed_injective.
  apply encodeRuntime_injective.
  now rewrite !encode_embed.
Qed.

Theorem encodePure_reaches : forall source target,
  Iota.reaches source target ->
  L.reaches (encodePure source) (encodePure target).
Proof.
  intros source target hsteps.
  unfold Iota.reaches in hsteps.
  rewrite <- !encode_embed.
  exact (encodeRuntime_steps hsteps).
Qed.

Theorem encodePure_progresses : forall source target,
  Iota.progresses source target ->
  L.progresses (encodePure source) (encodePure target).
Proof.
  intros source target hprogress.
  unfold Iota.progresses in hprogress.
  rewrite <- !encode_embed.
  exact (encodeRuntime_progresses hprogress).
Qed.

Record FaithfulIotaLambdaEmbedding : Type := {
  iotaLambdaEncode : Iota.term -> L.term Empty_set;
  iotaLambdaEncode_injective : forall x y,
    iotaLambdaEncode x = iotaLambdaEncode y -> x = y;
  iotaLambdaEncode_app : forall lhs rhs,
    iotaLambdaEncode (Iota.app lhs rhs) =
    L.app (iotaLambdaEncode lhs) (iotaLambdaEncode rhs);
  iotaLambdaEncode_reaches : forall source target,
    Iota.reaches source target ->
    L.reaches (iotaLambdaEncode source) (iotaLambdaEncode target);
  iotaLambdaEncode_progresses : forall source target,
    Iota.progresses source target ->
    L.progresses (iotaLambdaEncode source) (iotaLambdaEncode target)
}.

Definition faithful_iota_lambda_embedding : FaithfulIotaLambdaEmbedding :=
  {| iotaLambdaEncode := encodePure;
     iotaLambdaEncode_injective := encodePure_injective;
     iotaLambdaEncode_app := encodePure_app;
     iotaLambdaEncode_reaches := encodePure_reaches;
     iotaLambdaEncode_progresses := encodePure_progresses |}.

End IotaToLambda.
