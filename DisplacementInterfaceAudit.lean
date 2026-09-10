import AllResults

/-!
# Phase 1 displacement-interface audit

The printed types below are the canonical manuscript-facing endpoints of the displacement chain.
The companion shell check rejects any residual `Wasserstein2LawMeasurable` premise in these types.
-/

#check SequentialLearning.measurable_posteriorDisplacementENN_closed
#check SequentialLearning.posteriorDisplacement_memLp_two_closed
#check SequentialLearning.integral_posteriorDisplacement_sq_le_closed
#check SequentialLearning.frechet_posterior_displacement_bound_closed
#check SequentialLearning.frechet_predictable_displacement_envelope_closed
#check SequentialLearning.frechet_break_even_criterion_closed
