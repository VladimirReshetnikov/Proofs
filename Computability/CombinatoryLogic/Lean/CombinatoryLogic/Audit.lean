import CombinatoryLogic.Compiler
import CombinatoryLogic.SKIToSK
import CombinatoryLogic.LambdaToSK
import CombinatoryLogic.Universality
import CombinatoryLogic.IotaToLambda
import CombinatoryLogic.StrongLambda

/-!
# Assumption audit for the iota compiler

These commands keep the public theorem surface and its kernel assumptions
visible in ordinary build logs.
-/

open CombinatoryLogic

#check Lambda.Term.liftSubst_zero
#check Lambda.Term.liftSubst_succ
#check Lambda.Term.liftSubst_one
#check Lambda.Term.liftSubst_two
#check Lambda.Term.StrongStep
#check Lambda.Term.step_toStrongStep
#check Lambda.Term.church
#check Lambda.Term.church_strongNormalizes
#check Lambda.Term.church_injective
#check Compiler.compile
#check Compiler.compile_injective
#check Compiler.compile_size_linear
#check Compiler.step_simulation
#check Compiler.steps_simulation
#check Compiler.stepsPlus_simulation
#check Compiler.faithful_ski_embedding
#check Compiler.compiled_omega_cycle
#check SKIToSK.compile_not_injective
#check SKIToSK.step_simulation
#check SKIToSK.steps_simulation
#check SKIToSK.stepsPlus_simulation
#check SKIToSK.compile_size_linear
#check SKIToSK.sk_simulates_ski
#check SKIToSK.embed_injective
#check SKIToSK.embed_steps_simulation
#check SKIToSK.compiled_omega_cycle
#check LambdaToSK.Polynomial.abstract_bind_lift
#check LambdaToSK.Polynomial.abstract_correct
#check LambdaToSK.Compiler.compile_bind
#check LambdaToSK.Compiler.step_simulation
#check LambdaToSK.Compiler.steps_simulation
#check LambdaToSK.Compiler.stepsPlus_simulation
#check LambdaToSK.Compiler.sk_turing_complete
#check LambdaToSK.Compiler.sk_simulates_weak_lambda
#check LambdaToSK.Compiler.compiled_omega_cycle
#check Universality.ski_turing_complete
#check Universality.iota_turing_complete
#check Universality.lambda_step_to_ski
#check Universality.lambda_steps_to_ski
#check Universality.lambda_step_to_iota
#check Universality.lambda_steps_to_iota
#check Universality.lambda_omega_ski_cycle
#check Universality.lambda_omega_iota_cycle
#check IotaToLambda.rename_encodeRuntimeAt
#check IotaToLambda.bind_encodeRuntimeAt
#check IotaToLambda.encodeRuntimeAt_app
#check IotaToLambda.encodeRuntime_app
#check IotaToLambda.iota_head_step
#check IotaToLambda.k_head_first
#check IotaToLambda.k_head_second
#check IotaToLambda.s_head_first
#check IotaToLambda.s_head_second
#check IotaToLambda.s_head_third
#check IotaToLambda.k_head
#check IotaToLambda.s_head
#check IotaToLambda.runtime_step_simulation
#check IotaToLambda.runtime_steps_simulation
#check IotaToLambda.runtime_stepsPlus_simulation
#check IotaToLambda.encodeRuntime_step_positive
#check IotaToLambda.encodeRuntime_steps
#check IotaToLambda.encodeRuntime_progresses
#check IotaToLambda.encodeRuntime_embed
#check IotaToLambda.encodePure
#check IotaToLambda.encode_embed
#check IotaToLambda.encodeRuntimeAt_injective
#check IotaToLambda.encodeRuntime_injective
#check IotaToLambda.encode_app
#check IotaToLambda.encode_injective
#check IotaToLambda.reaches_simulation
#check IotaToLambda.reachesPlus_simulation
#check IotaToLambda.encodePure_app
#check IotaToLambda.encodePure_injective
#check IotaToLambda.encodePure_reaches
#check IotaToLambda.encodePure_progresses
#check IotaToLambda.FaithfulIotaLambdaEmbedding
#check IotaToLambda.faithful_iota_embedding
#check IotaToLambda.faithful_iota_lambda_embedding

#print axioms Compiler.compile_injective
#print axioms Lambda.Term.liftSubst_zero
#print axioms Lambda.Term.liftSubst_succ
#print axioms Lambda.Term.liftSubst_one
#print axioms Lambda.Term.liftSubst_two
#print axioms Lambda.Term.step_toStrongStep
#print axioms Lambda.Term.church_injective
#print axioms Compiler.compile_size_linear
#print axioms Compiler.step_simulation
#print axioms Compiler.steps_simulation
#print axioms Compiler.stepsPlus_simulation
#print axioms Compiler.faithful_ski_embedding
#print axioms Compiler.compiled_omega_cycle
#print axioms SKIToSK.compile_not_injective
#print axioms SKIToSK.step_simulation
#print axioms SKIToSK.steps_simulation
#print axioms SKIToSK.stepsPlus_simulation
#print axioms SKIToSK.compile_size_linear
#print axioms SKIToSK.sk_simulates_ski
#print axioms SKIToSK.embed_injective
#print axioms SKIToSK.embed_steps_simulation
#print axioms SKIToSK.compiled_omega_cycle
#print axioms LambdaToSK.Polynomial.abstract_bind_lift
#print axioms LambdaToSK.Polynomial.abstract_correct
#print axioms LambdaToSK.Compiler.compile_bind
#print axioms LambdaToSK.Compiler.step_simulation
#print axioms LambdaToSK.Compiler.steps_simulation
#print axioms LambdaToSK.Compiler.stepsPlus_simulation
#print axioms LambdaToSK.Compiler.sk_turing_complete
#print axioms LambdaToSK.Compiler.sk_simulates_weak_lambda
#print axioms LambdaToSK.Compiler.compiled_omega_cycle
#print axioms Universality.ski_turing_complete
#print axioms Universality.iota_turing_complete
#print axioms Universality.lambda_step_to_ski
#print axioms Universality.lambda_steps_to_ski
#print axioms Universality.lambda_step_to_iota
#print axioms Universality.lambda_steps_to_iota
#print axioms Universality.lambda_omega_ski_cycle
#print axioms Universality.lambda_omega_iota_cycle
#print axioms IotaToLambda.rename_encodeRuntimeAt
#print axioms IotaToLambda.bind_encodeRuntimeAt
#print axioms IotaToLambda.encodeRuntimeAt_app
#print axioms IotaToLambda.encodeRuntime_app
#print axioms IotaToLambda.iota_head_step
#print axioms IotaToLambda.k_head_first
#print axioms IotaToLambda.k_head_second
#print axioms IotaToLambda.s_head_first
#print axioms IotaToLambda.s_head_second
#print axioms IotaToLambda.s_head_third
#print axioms IotaToLambda.k_head
#print axioms IotaToLambda.s_head
#print axioms IotaToLambda.runtime_step_simulation
#print axioms IotaToLambda.runtime_steps_simulation
#print axioms IotaToLambda.runtime_stepsPlus_simulation
#print axioms IotaToLambda.encodeRuntime_step_positive
#print axioms IotaToLambda.encodeRuntime_steps
#print axioms IotaToLambda.encodeRuntime_progresses
#print axioms IotaToLambda.encodeRuntime_embed
#print axioms IotaToLambda.encode_embed
#print axioms IotaToLambda.encodeRuntimeAt_injective
#print axioms IotaToLambda.encodeRuntime_injective
#print axioms IotaToLambda.encode_app
#print axioms IotaToLambda.encode_injective
#print axioms IotaToLambda.reaches_simulation
#print axioms IotaToLambda.reachesPlus_simulation
#print axioms IotaToLambda.encodePure_app
#print axioms IotaToLambda.encodePure_injective
#print axioms IotaToLambda.encodePure_reaches
#print axioms IotaToLambda.encodePure_progresses
#print axioms IotaToLambda.faithful_iota_embedding
#print axioms IotaToLambda.faithful_iota_lambda_embedding
