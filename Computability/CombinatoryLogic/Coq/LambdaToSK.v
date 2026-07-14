(* ===================================================================== *)
(*  LambdaToSK.v                                                       *)
(*                                                                       *)
(*  A fully checked bracket-abstraction compiler from intrinsically      *)
(*  scoped untyped lambda terms to pure S-K terms.  The source uses weak  *)
(*  contextual beta reduction.  Every individual source contraction is  *)
(*  simulated by one or more target contractions.                        *)
(*                                                                       *)
(*  The final interface deliberately records both exact preservation of  *)
(*  application and positive simulation.  Thus its universality claim    *)
(*  cannot be discharged merely by mapping every source term to one      *)
(*  target term and using reflexivity of a closure.                       *)
(* ===================================================================== *)

From CombinatoryLogic Require Import
  Reduction Lambda SKPolynomial SK SKI Iota SKIToSK TuringCompleteness.

Set Implicit Arguments.

Module LambdaToSK.

Module L := UntypedLambda.
Module P := SKPolynomial.

(* First compile open lambda terms to S-K applicative polynomials. *)
Fixpoint compile {V : Type} (source : L.term V) : P.term V :=
  match source with
  | L.var x => P.var x
  | L.app lhs rhs => P.app (compile lhs) (compile rhs)
  | L.lam body => P.abstract (compile body)
  end.

Theorem compile_map : forall (A B : Type) (f : A -> B) source,
  compile (L.map f source) = P.map f (compile source).
Proof.
  intros A B f source.
  revert B f.
  induction source as [V x | V lhs IHlhs rhs IHrhs | V body IHbody];
    intros B f; cbn [compile L.map].
  - reflexivity.
  - now rewrite IHlhs, IHrhs.
  - rewrite IHbody.
    change
      (P.abstract (P.map (P.option_map f) (compile body)) =
       P.map f (P.abstract (compile body))).
    apply P.abstract_map.
Qed.

(* Compilation is a homomorphism for simultaneous substitution.  The    *)
(* occurrence-aware definition of [P.abstract] is what makes the lambda  *)
(* case an equality rather than only an operational equivalence.         *)
Theorem compile_bind : forall (A B : Type) (sigma : A -> L.term B) source,
  compile (L.bind sigma source) =
  P.bind (fun x => compile (sigma x)) (compile source).
Proof.
  intros A B sigma source.
  revert B sigma.
  induction source as [V x | V lhs IHlhs rhs IHrhs | V body IHbody];
    intros B sigma; cbn [compile L.bind].
  - reflexivity.
  - now rewrite IHlhs, IHrhs.
  - rewrite IHbody.
    rewrite <- (P.abstract_natural
      (fun x => compile (sigma x)) (compile body)).
    f_equal.
    apply P.bind_ext.
    intros [x | ]; cbn [L.liftSubst P.liftSubst].
    + apply compile_map.
    + reflexivity.
Qed.

Theorem compile_subst0 : forall (V : Type)
    (argument : L.term V) (body : L.term (option V)),
  compile (L.subst0 argument body) =
  P.subst0 (compile argument) (compile body).
Proof.
  intros V argument body.
  unfold L.subst0, P.subst0.
  rewrite compile_bind.
  apply P.bind_ext.
  intros [x | ]; reflexivity.
Qed.

Theorem compile_step_positive : forall (V : Type)
    (source target : L.term V),
  L.step source target ->
  P.progresses (compile source) (compile target).
Proof.
  intros V source target hstep.
  induction hstep as
    [body argument | lhs lhs' rhs hstep IH | lhs rhs rhs' hstep IH].
  - cbn [compile].
    rewrite compile_subst0.
    apply P.abstract_correct_positive.
  - cbn [compile].
    now apply P.progresses_app_left.
  - cbn [compile].
    now apply P.progresses_app_right.
Qed.

Theorem compile_step : forall (V : Type) (source target : L.term V),
  L.step source target -> P.reaches (compile source) (compile target).
Proof.
  intros V source target hstep.
  apply Reduction.plus_to_star.
  exact (compile_step_positive hstep).
Qed.

Theorem compile_steps : forall (V : Type) (source target : L.term V),
  L.reaches source target -> P.reaches (compile source) (compile target).
Proof.
  intros V source target hsteps.
  induction hsteps as [source | source middle target hstep hsteps IH].
  - apply P.reaches_refl.
  - eapply P.reaches_trans.
    + exact (compile_step hstep).
    + exact IH.
Qed.

Theorem compile_progresses : forall (V : Type)
    (source target : L.term V),
  L.progresses source target ->
  P.progresses (compile source) (compile target).
Proof.
  intros V source target hprogress.
  destruct hprogress as [source middle target hstep hsteps].
  unfold P.progresses, P.reaches in *.
  eapply Reduction.plus_star_trans.
  - exact (compile_step_positive hstep).
  - exact (compile_steps hsteps).
Qed.

(* A closed polynomial contains no [var] node, so it closes structurally  *)
(* to an ordinary pure S-K term.                                         *)
Fixpoint close (source : P.term Empty_set) : SK.term :=
  match source with
  | P.var impossible => match impossible with end
  | P.konst => SK.konst
  | P.scomb => SK.scomb
  | P.app lhs rhs => SK.app (close lhs) (close rhs)
  end.

Theorem close_app : forall lhs rhs,
  close (P.app lhs rhs) = SK.app (close lhs) (close rhs).
Proof. reflexivity. Qed.

Theorem close_step_positive : forall source target,
  P.step source target -> SK.progresses (close source) (close target).
Proof.
  intros source target hstep.
  induction hstep as
    [x y | x y z | x x' y hstep IH | x y y' hstep IH].
  - cbn [close].
    apply Reduction.plus_one.
    apply SK.step_konst.
  - cbn [close].
    apply Reduction.plus_one.
    apply SK.step_scomb.
  - cbn [close].
    now apply SK.progresses_app_left.
  - cbn [close].
    now apply SK.progresses_app_right.
Qed.

Theorem close_step : forall source target,
  P.step source target -> SK.reaches (close source) (close target).
Proof.
  intros source target hstep.
  apply Reduction.plus_to_star.
  exact (close_step_positive hstep).
Qed.

Theorem close_steps : forall source target,
  P.reaches source target -> SK.reaches (close source) (close target).
Proof.
  intros source target hsteps.
  induction hsteps as [source | source middle target hstep hsteps IH].
  - apply SK.reaches_refl.
  - eapply SK.reaches_trans.
    + exact (close_step hstep).
    + exact IH.
Qed.

Theorem close_progresses : forall source target,
  P.progresses source target -> SK.progresses (close source) (close target).
Proof.
  intros source target hprogress.
  destruct hprogress as [source middle target hstep hsteps].
  unfold SK.progresses, SK.reaches in *.
  eapply Reduction.plus_star_trans.
  - exact (close_step_positive hstep).
  - exact (close_steps hsteps).
Qed.

Definition compileClosed (source : L.term Empty_set) : SK.term :=
  close (compile source).

Theorem compileClosed_app : forall lhs rhs,
  compileClosed (L.app lhs rhs) =
  SK.app (compileClosed lhs) (compileClosed rhs).
Proof. reflexivity. Qed.

Theorem compileClosed_step_positive : forall source target,
  L.step source target ->
  SK.progresses (compileClosed source) (compileClosed target).
Proof.
  intros source target hstep.
  apply close_progresses.
  exact (compile_step_positive hstep).
Qed.

Theorem compileClosed_steps : forall source target,
  L.reaches source target ->
  SK.reaches (compileClosed source) (compileClosed target).
Proof.
  intros source target hsteps.
  apply close_steps.
  exact (compile_steps hsteps).
Qed.

Theorem compileClosed_progresses : forall source target,
  L.progresses source target ->
  SK.progresses (compileClosed source) (compileClosed target).
Proof.
  intros source target hprogress.
  apply close_progresses.
  exact (compile_progresses hprogress).
Qed.

Theorem compiled_lambda_omega_positive_cycle :
  SK.progresses (compileClosed L.omega) (compileClosed L.omega).
Proof.
  apply compileClosed_progresses.
  apply L.omega_positive_cycle.
Qed.

(* A reusable positive, compositional compiler package.  Besides           *)
(* reflexive-transitive simulation it records exact application structure  *)
(* and a nonempty target derivation for every individual beta contraction. *)
Record CompositionalPositiveSimulation (A : Type)
    (targetApp : A -> A -> A)
    (targetReaches targetProgresses : A -> A -> Prop) : Type := {
  lambdaEncode : L.term Empty_set -> A;
  lambdaEncode_app : forall lhs rhs,
    lambdaEncode (L.app lhs rhs) =
    targetApp (lambdaEncode lhs) (lambdaEncode rhs);
  lambdaEncode_step_positive : forall source target,
    L.step source target ->
    targetProgresses (lambdaEncode source) (lambdaEncode target);
  lambdaEncode_steps : forall source target,
    L.reaches source target ->
      targetReaches (lambdaEncode source) (lambdaEncode target)
}.

Arguments CompositionalPositiveSimulation A
  targetApp targetReaches targetProgresses : clear implicits.

Definition WeakLambdaSimulation (A : Type)
    (targetApp : A -> A -> A)
    (targetReaches targetProgresses : A -> A -> Prop) : Prop :=
  exists encode : L.term Empty_set -> A,
    (forall lhs rhs,
      encode (L.app lhs rhs) = targetApp (encode lhs) (encode rhs)) /\
    (forall source target,
      L.step source target ->
      targetProgresses (encode source) (encode target)) /\
    (forall source target,
      L.reaches source target ->
      targetReaches (encode source) (encode target)).

Arguments WeakLambdaSimulation A
  targetApp targetReaches targetProgresses : clear implicits.

Theorem compositional_positive_is_weak_lambda_simulation :
  forall (A : Type) targetApp targetReaches targetProgresses,
  CompositionalPositiveSimulation
    A targetApp targetReaches targetProgresses ->
  WeakLambdaSimulation A targetApp targetReaches targetProgresses.
Proof.
  intros A targetApp targetReaches targetProgresses compiler.
  exists (lambdaEncode compiler).
  split.
  - apply lambdaEncode_app.
  - split.
    + apply lambdaEncode_step_positive.
    + apply lambdaEncode_steps.
Qed.

Definition skLambdaCompiler :
    CompositionalPositiveSimulation
      SK.term SK.app SK.reaches SK.progresses :=
  {| lambdaEncode := compileClosed;
     lambdaEncode_app := compileClosed_app;
     lambdaEncode_step_positive := compileClosed_step_positive;
     lambdaEncode_steps := compileClosed_steps |}.

(* Here and below, "Turing complete" names the conventional boundary: the *)
(* fixed target syntax compositionally and positively simulates closed     *)
(* weak untyped lambda calculus.                                           *)
Theorem sk_turing_complete :
  WeakLambdaSimulation SK.term SK.app SK.reaches SK.progresses.
Proof.
  apply compositional_positive_is_weak_lambda_simulation.
  exact skLambdaCompiler.
Qed.

Definition compileClosedSKI (source : L.term Empty_set) : SKI.term :=
  SKIToSK.include (compileClosed source).

Theorem compileClosedSKI_app : forall lhs rhs,
  compileClosedSKI (L.app lhs rhs) =
  SKI.app (compileClosedSKI lhs) (compileClosedSKI rhs).
Proof. reflexivity. Qed.

Theorem compileClosedSKI_step_positive : forall source target,
  L.step source target ->
  SKI.progresses (compileClosedSKI source) (compileClosedSKI target).
Proof.
  intros source target hstep.
  apply SKIToSK.include_progresses.
  exact (compileClosed_step_positive hstep).
Qed.

Theorem compileClosedSKI_steps : forall source target,
  L.reaches source target ->
  SKI.reaches (compileClosedSKI source) (compileClosedSKI target).
Proof.
  intros source target hsteps.
  apply SKIToSK.include_steps.
  exact (compileClosed_steps hsteps).
Qed.

Theorem compileClosedSKI_progresses : forall source target,
  L.progresses source target ->
  SKI.progresses (compileClosedSKI source) (compileClosedSKI target).
Proof.
  intros source target hprogress.
  apply SKIToSK.include_progresses.
  exact (compileClosed_progresses hprogress).
Qed.

Definition skiLambdaCompiler :
    CompositionalPositiveSimulation
      SKI.term SKI.app SKI.reaches SKI.progresses :=
  {| lambdaEncode := compileClosedSKI;
     lambdaEncode_app := compileClosedSKI_app;
     lambdaEncode_step_positive := compileClosedSKI_step_positive;
     lambdaEncode_steps := compileClosedSKI_steps |}.

Theorem ski_turing_complete :
  WeakLambdaSimulation SKI.term SKI.app SKI.reaches SKI.progresses.
Proof.
  apply compositional_positive_is_weak_lambda_simulation.
  exact skiLambdaCompiler.
Qed.

Theorem compiled_ski_lambda_omega_positive_cycle :
  SKI.progresses
    (compileClosedSKI L.omega) (compileClosedSKI L.omega).
Proof.
  apply compileClosedSKI_progresses.
  apply L.omega_positive_cycle.
Qed.

Definition compileClosedIota (source : L.term Empty_set) : Iota.term :=
  IotaTuringCompleteness.compile (compileClosedSKI source).

Theorem compileClosedIota_app : forall lhs rhs,
  compileClosedIota (L.app lhs rhs) =
  Iota.app (compileClosedIota lhs) (compileClosedIota rhs).
Proof. reflexivity. Qed.

Theorem compileClosedIota_step_positive : forall source target,
  L.step source target ->
  Iota.progresses (compileClosedIota source) (compileClosedIota target).
Proof.
  intros source target hstep.
  apply IotaTuringCompleteness.compile_progresses.
  apply SKIToSK.include_progresses.
  exact (compileClosed_step_positive hstep).
Qed.

Theorem compileClosedIota_steps : forall source target,
  L.reaches source target ->
  Iota.reaches (compileClosedIota source) (compileClosedIota target).
Proof.
  intros source target hsteps.
  apply IotaTuringCompleteness.compile_steps.
  apply SKIToSK.include_steps.
  exact (compileClosed_steps hsteps).
Qed.

Theorem compileClosedIota_progresses : forall source target,
  L.progresses source target ->
  Iota.progresses (compileClosedIota source) (compileClosedIota target).
Proof.
  intros source target hprogress.
  apply IotaTuringCompleteness.compile_progresses.
  apply SKIToSK.include_progresses.
  exact (compileClosed_progresses hprogress).
Qed.

Definition iotaLambdaCompiler :
    CompositionalPositiveSimulation
      Iota.term Iota.app Iota.reaches Iota.progresses :=
  {| lambdaEncode := compileClosedIota;
     lambdaEncode_app := compileClosedIota_app;
     lambdaEncode_step_positive := compileClosedIota_step_positive;
     lambdaEncode_steps := compileClosedIota_steps |}.

Theorem iota_turing_complete :
  WeakLambdaSimulation Iota.term Iota.app Iota.reaches Iota.progresses.
Proof.
  apply compositional_positive_is_weak_lambda_simulation.
  exact iotaLambdaCompiler.
Qed.

Theorem compiled_iota_lambda_omega_positive_cycle :
  Iota.progresses
    (compileClosedIota L.omega) (compileClosedIota L.omega).
Proof.
  apply compileClosedIota_progresses.
  apply L.omega_positive_cycle.
Qed.

End LambdaToSK.
