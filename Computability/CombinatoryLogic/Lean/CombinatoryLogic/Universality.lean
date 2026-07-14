import CombinatoryLogic.Compiler
import CombinatoryLogic.SKIToSK
import CombinatoryLogic.LambdaToSK

/-!
# Compositional universality witnesses

The occurs-aware bracket compiler makes pure SK operationally universal for
closed weak lambda terms.  The verified SK inclusion and SKI-to-iota compiler
transport the same positive simulation to SKI and pure iota.
-/

namespace CombinatoryLogic.Universality

open LambdaToSK.Compiler

/-- Closed weak lambda terms compiled first to SK and then included into SKI. -/
def compileLambdaToSKI (term : Lambda.Term 0) : SKI.Term :=
  SKIToSK.embed (compileClosed term)

@[simp] theorem compileLambdaToSKI_app (function argument : Lambda.Term 0) :
    compileLambdaToSKI (.app function argument) =
      .app (compileLambdaToSKI function) (compileLambdaToSKI argument) := rfl

/-- Every weak beta step compiles to a nonempty SKI reduction. -/
theorem lambda_step_to_ski {source target : Lambda.Term 0} (h : source.Step target) :
    SKI.Term.StepsPlus (compileLambdaToSKI source) (compileLambdaToSKI target) :=
  SKIToSK.embed_stepsPlus_simulation (step_simulation h Fin.elim0)

/-- Every finite weak-beta reduction compiles to a finite SKI reduction. -/
theorem lambda_steps_to_ski {source target : Lambda.Term 0} (h : source.Steps target) :
    SKI.Term.Steps (compileLambdaToSKI source) (compileLambdaToSKI target) :=
  SKIToSK.embed_steps_simulation (steps_simulation h Fin.elim0)

/-- Pure SKI is operationally universal relative to closed weak lambda calculus. -/
def ski_turing_complete : WeakLambdaSimulation SKI.Term SKI.Term.StepsPlus where
  app := .app
  encode := compileLambdaToSKI
  encode_app := compileLambdaToSKI_app
  simulatesStep := lambda_step_to_ski

/-- Closed weak lambda terms compiled through SK and SKI into pure iota syntax. -/
def compileLambdaToIota (term : Lambda.Term 0) : Iota.Term :=
  Compiler.compile (compileLambdaToSKI term)

@[simp] theorem compileLambdaToIota_app (function argument : Lambda.Term 0) :
    compileLambdaToIota (.app function argument) =
      .app (compileLambdaToIota function) (compileLambdaToIota argument) := rfl

/-- Every weak beta step compiles to a nonempty pure-iota runtime reduction. -/
theorem lambda_step_to_iota {source target : Lambda.Term 0} (h : source.Step target) :
    Iota.ReachesPlus (compileLambdaToIota source) (compileLambdaToIota target) :=
  Compiler.stepsPlus_simulation (lambda_step_to_ski h)

/-- Every finite weak-beta reduction compiles to a finite pure-iota runtime reduction. -/
theorem lambda_steps_to_iota {source target : Lambda.Term 0} (h : source.Steps target) :
    Iota.Reaches (compileLambdaToIota source) (compileLambdaToIota target) :=
  Compiler.steps_simulation (lambda_steps_to_ski h)

/-- Pure iota is operationally universal relative to closed weak lambda calculus. -/
def iota_turing_complete : WeakLambdaSimulation Iota.Term Iota.ReachesPlus where
  app := .app
  encode := compileLambdaToIota
  encode_app := compileLambdaToIota_app
  simulatesStep := lambda_step_to_iota

/-- The lambda omega cycle transports to a nonempty SKI cycle. -/
theorem lambda_omega_ski_cycle :
    SKI.Term.StepsPlus
      (compileLambdaToSKI Lambda.Term.omega) (compileLambdaToSKI Lambda.Term.omega) :=
  lambda_step_to_ski (.beta (.app (.var 0) (.var 0)) Lambda.Term.omegaKernel)

/-- The lambda omega cycle transports to a nonempty pure-iota runtime cycle. -/
theorem lambda_omega_iota_cycle :
    Iota.ReachesPlus
      (compileLambdaToIota Lambda.Term.omega) (compileLambdaToIota Lambda.Term.omega) :=
  lambda_step_to_iota (.beta (.app (.var 0) (.var 0)) Lambda.Term.omegaKernel)

end CombinatoryLogic.Universality
