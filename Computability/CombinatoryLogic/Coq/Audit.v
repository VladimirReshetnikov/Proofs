From CombinatoryLogic Require Import
  Reduction Lambda StrongLambda SKPolynomial SKI SK Iota SKIToSK
  TuringCompleteness LambdaToSK IotaToLambda.

Check StrongUntypedLambda.strong_step.
Check StrongUntypedLambda.step_to_strong_step.
Check StrongUntypedLambda.strong_normal_iff_shape.
Check StrongUntypedLambda.church.
Check StrongUntypedLambda.church_strong_normalizes.
Check StrongUntypedLambda.church_injective.

Check UntypedLambda.map_ext.
Check UntypedLambda.map_comp.
Check UntypedLambda.bind_ext.
Check UntypedLambda.bind_var.
Check UntypedLambda.bind_map.
Check UntypedLambda.map_bind.
Check UntypedLambda.subst0_map_some.

Check IotaToLambda.lambdaIota_correct_positive.
Check IotaToLambda.lambdaK_correct_positive.
Check IotaToLambda.lambdaS_correct_positive.
Check IotaToLambda.encodeRuntime_app.
Check IotaToLambda.encodeRuntime_step_positive.
Check IotaToLambda.encodeRuntime_step.
Check IotaToLambda.encodeRuntime_steps.
Check IotaToLambda.encodeRuntime_progresses.
Check IotaToLambda.encodeRuntime_injective.
Check IotaToLambda.encodePure_app.
Check IotaToLambda.encode_embed.
Check IotaToLambda.encodePure_injective.
Check IotaToLambda.encodePure_reaches.
Check IotaToLambda.encodePure_progresses.
Check IotaToLambda.FaithfulIotaLambdaEmbedding.
Check IotaToLambda.faithful_iota_lambda_embedding.

Check UntypedLambda.omega_positive_cycle.
Check SKPolynomial.abstract_correct.
Check SKPolynomial.abstract_correct_positive.
Check SKPolynomial.abstract_natural.
Check SKPolynomial.abstract_map.
Check LambdaToSK.compile_map.
Check LambdaToSK.compile_bind.
Check LambdaToSK.compile_subst0.
Check LambdaToSK.compile_step_positive.
Check LambdaToSK.compile_steps.
Check LambdaToSK.compile_progresses.
Check LambdaToSK.compileClosed_app.
Check LambdaToSK.compileClosed_step_positive.
Check LambdaToSK.compileClosed_steps.
Check LambdaToSK.compileClosed_progresses.
Check LambdaToSK.compiled_lambda_omega_positive_cycle.
Check LambdaToSK.compileClosedSKI_progresses.
Check LambdaToSK.compiled_ski_lambda_omega_positive_cycle.
Check LambdaToSK.compileClosedIota_progresses.
Check LambdaToSK.CompositionalPositiveSimulation.
Check LambdaToSK.WeakLambdaSimulation.
Check LambdaToSK.skLambdaCompiler.
Check LambdaToSK.skiLambdaCompiler.
Check LambdaToSK.iotaLambdaCompiler.
Check LambdaToSK.sk_turing_complete.
Check LambdaToSK.ski_turing_complete.
Check LambdaToSK.iota_turing_complete.
Check LambdaToSK.compiled_iota_lambda_omega_positive_cycle.

Check SK.ident_correct.
Check SK.ident_correct_positive.
Check SK.omega_positive_cycle.
Check SKIToSK.compile_step_positive.
Check SKIToSK.compile_steps.
Check SKIToSK.compile_progresses.
Check SKIToSK.compile_size_linear.
Check SKIToSK.compile_ident_collision.
Check SKIToSK.compile_not_injective.
Check SKIToSK.include_injective.
Check SKIToSK.include_step_positive.
Check SKIToSK.include_steps.
Check SKIToSK.include_progresses.
Check SKIToSK.include_size.
Check SKIToSK.compile_include.
Check SKIToSK.compiled_ski_omega_positive_cycle.
Check SKIToSK.included_sk_omega_positive_cycle.

Check Iota.embed_pure.
Check Iota.pure_iff_embedded.
Check Iota.embed_injective.
Check Iota.identCode_correct.
Check Iota.identCode_correct_positive.
Check Iota.konstCode_unfolds.
Check Iota.konstCode_correct.
Check Iota.konstCode_correct_positive.
Check Iota.scombCode_unfolds.
Check Iota.scombCode_correct.
Check Iota.scombCode_correct_positive.
Check SKI.omega_positive_cycle.
Check IotaTuringCompleteness.compile_runtime_pure.
Check IotaTuringCompleteness.compile_injective.
Check IotaTuringCompleteness.compile_size_linear.
Check IotaTuringCompleteness.compile_step.
Check IotaTuringCompleteness.compile_step_positive.
Check IotaTuringCompleteness.compile_steps.
Check IotaTuringCompleteness.compile_progresses.
Check IotaTuringCompleteness.compiled_omega_positive_cycle.
Check IotaTuringCompleteness.FaithfulSKIEmbedding.
Check IotaTuringCompleteness.SKIEmbeddable.
Check IotaTuringCompleteness.iota_faithfully_embeds_ski.
Check IotaTuringCompleteness.faithful_ski_embedding.

Print Assumptions IotaTuringCompleteness.faithful_ski_embedding.
Print Assumptions IotaTuringCompleteness.compiled_omega_positive_cycle.
Print Assumptions SKIToSK.compile_progresses.
Print Assumptions SKIToSK.include_progresses.
Print Assumptions LambdaToSK.sk_turing_complete.
Print Assumptions LambdaToSK.ski_turing_complete.
Print Assumptions LambdaToSK.iota_turing_complete.
Print Assumptions LambdaToSK.compileClosedSKI_progresses.
Print Assumptions LambdaToSK.compileClosedIota_progresses.
Print Assumptions LambdaToSK.compiled_iota_lambda_omega_positive_cycle.
Print Assumptions IotaToLambda.lambdaIota_correct_positive.
Print Assumptions IotaToLambda.lambdaK_correct_positive.
Print Assumptions IotaToLambda.lambdaS_correct_positive.
Print Assumptions IotaToLambda.encodeRuntime_step_positive.
Print Assumptions IotaToLambda.encodeRuntime_injective.
Print Assumptions IotaToLambda.faithful_iota_lambda_embedding.
Print Assumptions StrongUntypedLambda.strong_normal_iff_shape.
Print Assumptions StrongUntypedLambda.church_injective.
