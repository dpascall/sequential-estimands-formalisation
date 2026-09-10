import SequentialLearning.SameEstimandImpossibility

/-!
# Same-estimand impossibility interface audit

The repaired boundary exposes one concrete flag-valued estimand per non-fixed
class, canonical RCDs under both observation models, and exact Frechet-
variance, information, and movement verdicts.
-/

#check SequentialLearning.SameEstimandImpossibility.stageLaw_isRCD
#check SequentialLearning.SameEstimandImpossibility.flagged_uninformative_all_stages
#check SequentialLearning.SameEstimandImpossibility.flagged_uninformative_all_transitions
#check SequentialLearning.SameEstimandImpossibility.flagged_noisy_verdict
#check SequentialLearning.SameEstimandImpossibility.flagged_information_term
#check SequentialLearning.SameEstimandImpossibility.flagged_movement_term
#check SequentialLearning.SameEstimandImpossibility.bothverdicts
#check SequentialLearning.SameEstimandImpossibility.impossibility
