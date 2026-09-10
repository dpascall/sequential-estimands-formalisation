import SequentialLearning.TaxonomyProcessResults

/-!
# Increasing-loss interface audit

These checks print the exact manuscript-facing generic and class-indexed
types. Their compilation is a regression test that global measurability of
`g` is not required.
-/

#check SequentialLearning.conditional_increasing_loss_order_nonnegative
#check SequentialLearning.conditional_increasing_loss_supermartingale_nonnegative
#check SequentialLearning.HypotheticalSequentialEstimand.StructuralPresentation.monotoneClass_conditional_increasing_loss_supermartingale
