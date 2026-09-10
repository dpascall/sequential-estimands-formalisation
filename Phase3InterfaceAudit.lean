import SequentialLearning.Impossibility

/-!
# Phase 3 interface audit

The printed types are checked mechanically by `scripts/check_phase3_interfaces.sh`.
The final interfaces must expose the canonical taxonomy and concrete finite
observation model without requiring a caller-supplied constraint family or
flag-coupling lift.
-/

#check SequentialLearning.NoisyObservationModel.card_latentState
#check SequentialLearning.NoisyObservationModel.posteriorVarianceOne_eq
#check SequentialLearning.NoisyObservationModel.expectedVarianceTwo_eq
#check SequentialLearning.NoisyObservationModel.both_verdicts
#check SequentialLearning.StructuralWitnesses.witnesses
#check SequentialLearning.StructuralWitnesses.classEventsMeasurable
#check SequentialLearning.Phase3.admissible_flag_process
#check SequentialLearning.Phase3.bothverdicts
#check SequentialLearning.Phase3.impossibility
