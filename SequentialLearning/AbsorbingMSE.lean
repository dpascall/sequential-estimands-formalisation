import SequentialLearning.MSEHierarchy
import Mathlib.Probability.Notation

/-!
# Mean squared error in absorbing classes

This file formalises Corollary `mseabsorbing`.  The proof is split into the
event identity supplied by absorption, its transport through conditional
expectation, and the resulting sharpening of the general MSE hierarchy.
-/

namespace SequentialLearning

open Filter MeasureTheory Set
open scoped ENNReal MeasureTheory ProbabilityTheory

noncomputable section

section AbsorbingMSE

variable {Ω H : Type*} {m0 : MeasurableSpace Ω}
  [NormedAddCommGroup H]

/-- On the realised path, the persistence event agrees almost surely with
zero current-to-limit discrepancy.  Membership in the persistence event
implies equality pointwise by its definition; absorbing-class coverage gives
the reverse implication almost surely. -/
theorem persistence_event_iff_zero_discrepancy
    (μ : Measure[m0] Ω) (KLimit KCurrent : Ω → H) (E : Set Ω)
    (hPersistence : ∀ ω, ω ∈ E → KCurrent ω = KLimit ω)
    (hAbsorbing : ∀ᵐ ω ∂μ, KCurrent ω = KLimit ω → ω ∈ E) :
    ∀ᵐ ω ∂μ, ω ∈ E ↔ limitDiscrepancy KLimit KCurrent ω = 0 := by
  filter_upwards [hAbsorbing] with ω hAbsorbingω
  constructor
  · intro hE
    simp [limitDiscrepancy, hPersistence ω hE]
  · intro hZero
    have hDifference : KLimit ω - KCurrent ω = 0 := norm_eq_zero.mp hZero
    exact hAbsorbingω (sub_eq_zero.mp hDifference).symm

/-- The indicator of positive current-to-limit discrepancy agrees almost
surely with the indicator of non-absorption.  The first hypothesis is the
definitional direction of persistence; the second is the absorbing-class
coverage condition on the realised path. -/
theorem discrepancy_nonzero_indicator_eq_not_absorbed
    (μ : Measure[m0] Ω) (KLimit KCurrent : Ω → H) (E : Set Ω)
    (hPersistence : ∀ ω, ω ∈ E → KCurrent ω = KLimit ω)
    (hAbsorbing : ∀ᵐ ω ∂μ, KCurrent ω = KLimit ω → ω ∈ E) :
    (fun ω => if 0 < limitDiscrepancy KLimit KCurrent ω then 1 else 0) =ᵐ[μ]
      Eᶜ.indicator (fun _ => (1 : ℝ)) := by
  have hEvent := persistence_event_iff_zero_discrepancy
    μ KLimit KCurrent E hPersistence hAbsorbing
  filter_upwards [hEvent] with ω hEventω
  by_cases hPositive : 0 < limitDiscrepancy KLimit KCurrent ω
  · have hNotAbsorbed : ω ∉ E := by
      intro hE
      exact (ne_of_gt hPositive) (hEventω.mp hE)
    simp [hPositive, hNotAbsorbed]
  · have hDiscrepancyZero : limitDiscrepancy KLimit KCurrent ω = 0 := by
      exact le_antisymm (le_of_not_gt hPositive)
        (norm_nonneg (KLimit ω - KCurrent ω))
    have hE : ω ∈ E := hEventω.mpr hDiscrepancyZero
    simp [hPositive, hE]

/-- In an absorbing class the posterior tail probability at zero discrepancy
is the posterior probability that absorption has not occurred. -/
theorem absorbing_discrepancy_tail_eq_conditional_probability
    (μ : Measure[m0] Ω) (m : MeasurableSpace Ω)
    (KLimit KCurrent : Ω → H) (E : Set Ω)
    (hPersistence : ∀ ω, ω ∈ E → KCurrent ω = KLimit ω)
    (hAbsorbing : ∀ᵐ ω ∂μ, KCurrent ω = KLimit ω → ω ∈ E) :
    discrepancyTailAtZero μ m KLimit KCurrent =ᵐ[μ] (μ⟦Eᶜ | m⟧) := by
  exact condExp_congr_ae
    (discrepancy_nonzero_indicator_eq_not_absorbed μ KLimit KCurrent E
      hPersistence hAbsorbing)

/-- Absorption rewrites the anonymous discrepancy-tail factor in the middle
MSE bound as the posterior probability of the non-absorbed branch. -/
theorem absorbing_classes_mse_bound
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ m0)
    (KLimit KCurrent : Ω → H) (E : Set Ω)
    (hKLimitMeas : StronglyMeasurable[m0] KLimit)
    (hKCurrentMeas : StronglyMeasurable[m0] KCurrent)
    (hKLimit : MemLp KLimit 2 μ) (hKCurrent : MemLp KCurrent 2 μ)
    (hPersistence : ∀ ω, ω ∈ E → KCurrent ω = KLimit ω)
    (hAbsorbing : ∀ᵐ ω ∂μ, KCurrent ω = KLimit ω → ω ∈ E) :
    ∀ᵐ ω ∂μ,
      posteriorMSE μ m KLimit KCurrent ω ≤
        posteriorVariance μ m KLimit ω +
          (μ⟦Eᶜ | m⟧) ω *
            conditionalSquaredDiscrepancy μ m KLimit KCurrent ω := by
  have hHierarchy := mean_squared_error_hierarchy μ m hm KLimit KCurrent
    hKLimitMeas hKCurrentMeas hKLimit hKCurrent
  have hTail := absorbing_discrepancy_tail_eq_conditional_probability
    μ m KLimit KCurrent E hPersistence hAbsorbing
  filter_upwards [hHierarchy, hTail] with ω hHierarchyω hTailω
  have hMiddle := hHierarchyω.2.1
  change
    posteriorMSE μ m KLimit KCurrent ω ≤
      posteriorVariance μ m KLimit ω +
        discrepancyTailAtZero μ m KLimit KCurrent ω *
          conditionalSquaredDiscrepancy μ m KLimit KCurrent ω at hMiddle
  rw [hTailω] at hMiddle
  exact hMiddle

end AbsorbingMSE

end

end SequentialLearning
