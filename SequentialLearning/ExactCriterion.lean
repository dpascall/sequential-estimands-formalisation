import Mathlib.Algebra.Order.Group.Basic

/-!
# Exact one-step learning criterion: algebraic core

This file formalises the exact rearrangement at the centre of Theorem
`maincriterion`.  The probability-theoretic construction of the four
conditional-risk quantities will be added separately; here they are elements
of an arbitrary linearly ordered additive commutative group, which is stronger
than specialising the calculation to real-valued random variables pointwise.
-/

namespace SequentialLearning

section ExactCriterion

variable {A : Type*} [AddCommGroup A]

/-- Information gain about the stage-`n` target. -/
def informationGain (Vn expectedOldRisk : A) : A :=
  Vn - expectedOldRisk

/-- Change in risk caused by replacing the old target with the new target. -/
def estimandMovement (expectedNewRisk expectedOldRisk : A) : A :=
  expectedNewRisk - expectedOldRisk

/-- The exact decomposition `Vₙ - E[Vₙ₊₁] = Jₙ - Sₙ`. -/
theorem exact_one_step_identity
    (Vn expectedOldRisk expectedNewRisk : A) :
    Vn - expectedNewRisk =
      informationGain Vn expectedOldRisk -
        estimandMovement expectedNewRisk expectedOldRisk := by
  simpa only [informationGain, estimandMovement] using
    (sub_sub_sub_cancel_right Vn expectedNewRisk expectedOldRisk).symm

variable [LinearOrder A] [IsOrderedAddMonoid A]

/-- Posterior risk decreases exactly when information gain dominates movement. -/
theorem exact_learning_iff
    (Vn expectedOldRisk expectedNewRisk : A) :
    expectedNewRisk ≤ Vn ↔
      informationGain Vn expectedOldRisk ≥
        estimandMovement expectedNewRisk expectedOldRisk := by
  simpa only [informationGain, estimandMovement, ge_iff_le] using
    (sub_le_sub_iff_right expectedOldRisk :
      expectedNewRisk - expectedOldRisk ≤ Vn - expectedOldRisk ↔
        expectedNewRisk ≤ Vn).symm

/-- The manuscript formulation with `J` and `S` introduced by equations. -/
theorem exact_one_step_learning_criterion
    (Vn expectedOldRisk expectedNewRisk J S : A)
    (hJ : J = Vn - expectedOldRisk)
    (hS : S = expectedNewRisk - expectedOldRisk) :
    (Vn - expectedNewRisk = J - S) ∧
      (expectedNewRisk ≤ Vn ↔ J ≥ S) := by
  subst J
  subst S
  exact ⟨exact_one_step_identity _ _ _, exact_learning_iff _ _ _⟩

end ExactCriterion

end SequentialLearning
