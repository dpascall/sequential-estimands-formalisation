import SequentialLearning.FlagSpaceCouplingLift

/-!
# Boolean flag-space Wasserstein interface audit

The exact equality must remain unconditional at the public boundary.  The
constructive checks also record that the lift projects to the supplied
coupling and preserves its cost exactly.
-/

#check SequentialLearning.FlagSpace.liftCoupling_map_values
#check SequentialLearning.FlagSpace.transportL2Cost_liftCoupling
#check SequentialLearning.FlagSpace.wasserstein2_eq_project
