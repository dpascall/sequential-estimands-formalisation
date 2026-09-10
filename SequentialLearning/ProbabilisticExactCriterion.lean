import SequentialLearning.ExactCriterion
import SequentialLearning.FrechetRefinement

/-!
# Complete probabilistic exact one-step learning criterion

This file connects the algebraic core in `ExactCriterion.lean` to the
RCD-based posterior Frechet variance developed in
`FrechetRiskWellPosedness.lean` and `FrechetRefinement.lean`.
-/

namespace SequentialLearning

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal MeasureTheory ProbabilityTheory

noncomputable section

section ProbabilisticExactCriterion

variable {Omega S : Type*} {mOmega : MeasurableSpace Omega}
  [PseudoMetricSpace S] [MeasurableSpace S] [Nonempty S]
  [OpensMeasurableSpace S] [TopologicalSpace.SeparableSpace S]

/-- `V_n`: posterior Frechet variance of the current target under the current
information state. -/
def currentPosteriorFrechetVariance
    (mSmall : MeasurableSpace Omega)
    (kappaOldSmall :
      Kernel[mSmall, (inferInstance : MeasurableSpace S)] Omega S) :
    Omega → ℝ :=
  posteriorFrechetVarianceReal mSmall kappaOldSmall

/-- `U_{n+1}`: posterior Frechet variance of the old target after the
information refinement. -/
def refinedOldPosteriorFrechetVariance
    (mLarge : MeasurableSpace Omega)
    (kappaOldLarge :
      Kernel[mLarge, (inferInstance : MeasurableSpace S)] Omega S) :
    Omega → ℝ :=
  posteriorFrechetVarianceReal mLarge kappaOldLarge

/-- `V_{n+1}`: posterior Frechet variance of the new target after the
information refinement. -/
def refinedNewPosteriorFrechetVariance
    (mLarge : MeasurableSpace Omega)
    (kappaNewLarge :
      Kernel[mLarge, (inferInstance : MeasurableSpace S)] Omega S) :
    Omega → ℝ :=
  posteriorFrechetVarianceReal mLarge kappaNewLarge

/-- `J_n^(d)`: information gained about the old target. -/
def frechetInformationGain
    (mu : Measure[mOmega] Omega)
    (mSmall mLarge : MeasurableSpace Omega)
    (kappaOldSmall :
      Kernel[mSmall, (inferInstance : MeasurableSpace S)] Omega S)
    (kappaOldLarge :
      Kernel[mLarge, (inferInstance : MeasurableSpace S)] Omega S) :
    Omega → ℝ :=
  fun omega => informationGain
    (currentPosteriorFrechetVariance mSmall kappaOldSmall omega)
    (mu[refinedOldPosteriorFrechetVariance mLarge kappaOldLarge |
      mSmall] omega)

/-- `S_n^(d)`: the current-information conditional expectation of the
change in posterior variance caused by replacing the old target with the new
target. -/
def frechetEstimandMovement
    (mu : Measure[mOmega] Omega)
    (mSmall mLarge : MeasurableSpace Omega)
    (kappaOldLarge :
      Kernel[mLarge, (inferInstance : MeasurableSpace S)] Omega S)
    (kappaNewLarge :
      Kernel[mLarge, (inferInstance : MeasurableSpace S)] Omega S) :
    Omega → ℝ :=
  mu[(fun omega =>
    refinedNewPosteriorFrechetVariance mLarge kappaNewLarge omega -
      refinedOldPosteriorFrechetVariance mLarge kappaOldLarge omega) |
    mSmall]

omit [Nonempty S] [OpensMeasurableSpace S]
  [TopologicalSpace.SeparableSpace S] in
/-- The information term is definitionally the Frechet refinement gain for
the old target. -/
theorem frechetInformationGain_eq_refinementGain
    (mu : Measure[mOmega] Omega)
    (mSmall mLarge : MeasurableSpace Omega)
    (kappaOldSmall :
      Kernel[mSmall, (inferInstance : MeasurableSpace S)] Omega S)
    (kappaOldLarge :
      Kernel[mLarge, (inferInstance : MeasurableSpace S)] Omega S) :
    frechetInformationGain mu mSmall mLarge
      kappaOldSmall kappaOldLarge =
    frechetRefinementGain mu mSmall mLarge
      kappaOldSmall kappaOldLarge := by
  rfl

/-- The three posterior variance variables are measurable in their respective
information states and integrable. -/
theorem oneStepPosteriorFrechetVariances_wellPosed
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (mSmall mLarge : MeasurableSpace Omega)
    (hSmallLarge : mSmall ≤ mLarge) (hLargeAmbient : mLarge ≤ mOmega)
    (KOld KNew : Omega → S)
    (hKOld : Measurable[mOmega] KOld)
    (hKNew : Measurable[mOmega] KNew)
    (kappaOldSmall :
      Kernel[mSmall, (inferInstance : MeasurableSpace S)] Omega S)
    (kappaOldLarge kappaNewLarge :
      Kernel[mLarge, (inferInstance : MeasurableSpace S)] Omega S)
    [IsMarkovKernel kappaOldSmall] [IsMarkovKernel kappaOldLarge]
    [IsMarkovKernel kappaNewLarge]
    (hkappaOldSmall : IsRegularConditionalLaw mu mSmall
      (hSmallLarge.trans hLargeAmbient) KOld kappaOldSmall)
    (hkappaOldLarge : IsRegularConditionalLaw mu mLarge
      hLargeAmbient KOld kappaOldLarge)
    (hkappaNewLarge : IsRegularConditionalLaw mu mLarge
      hLargeAmbient KNew kappaNewLarge)
    (s0 t0 : S)
    (hMomentOld : Integrable (fun omega => dist (KOld omega) s0 ^ 2) mu)
    (hMomentNew : Integrable (fun omega => dist (KNew omega) t0 ^ 2) mu) :
    (StronglyMeasurable[mSmall]
        (currentPosteriorFrechetVariance mSmall kappaOldSmall) ∧
      Integrable
        (currentPosteriorFrechetVariance mSmall kappaOldSmall) mu) ∧
    (StronglyMeasurable[mLarge]
        (refinedOldPosteriorFrechetVariance mLarge kappaOldLarge) ∧
      Integrable
        (refinedOldPosteriorFrechetVariance mLarge kappaOldLarge) mu) ∧
    (StronglyMeasurable[mLarge]
        (refinedNewPosteriorFrechetVariance mLarge kappaNewLarge) ∧
      Integrable
        (refinedNewPosteriorFrechetVariance mLarge kappaNewLarge) mu) := by
  have hOldSmallBundle := posteriorFrechet_finite_and_integrable
    mu mSmall (hSmallLarge.trans hLargeAmbient) KOld hKOld
      kappaOldSmall hkappaOldSmall s0 hMomentOld
  have hOldLargeBundle := posteriorFrechet_finite_and_integrable
    mu mLarge hLargeAmbient KOld hKOld
      kappaOldLarge hkappaOldLarge s0 hMomentOld
  have hNewLargeBundle := posteriorFrechet_finite_and_integrable
    mu mLarge hLargeAmbient KNew hKNew
      kappaNewLarge hkappaNewLarge t0 hMomentNew
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact stronglyMeasurable_posteriorFrechetVarianceReal
      mSmall kappaOldSmall
  · change Integrable
      (fun omega => (frechetVariance (kappaOldSmall omega)).toReal) mu
    exact hOldSmallBundle.2.2.2
  · exact stronglyMeasurable_posteriorFrechetVarianceReal
      mLarge kappaOldLarge
  · change Integrable
      (fun omega => (frechetVariance (kappaOldLarge omega)).toReal) mu
    exact hOldLargeBundle.2.2.2
  · exact stronglyMeasurable_posteriorFrechetVarianceReal
      mLarge kappaNewLarge
  · change Integrable
      (fun omega => (frechetVariance (kappaNewLarge omega)).toReal) mu
    exact hNewLargeBundle.2.2.2

omit [Nonempty S] [OpensMeasurableSpace S]
  [TopologicalSpace.SeparableSpace S] in
/-- Conditional-expectation linearity identifies the manuscript's movement
term with the difference of the two predictable refined variances. -/
theorem frechetEstimandMovement_ae_eq
    (mu : Measure[mOmega] Omega)
    (mSmall mLarge : MeasurableSpace Omega)
    (kappaOldLarge kappaNewLarge :
      Kernel[mLarge, (inferInstance : MeasurableSpace S)] Omega S)
    (hOldIntegrable : Integrable
      (refinedOldPosteriorFrechetVariance mLarge kappaOldLarge) mu)
    (hNewIntegrable : Integrable
      (refinedNewPosteriorFrechetVariance mLarge kappaNewLarge) mu) :
    frechetEstimandMovement mu mSmall mLarge
        kappaOldLarge kappaNewLarge =ᵐ[mu]
      fun omega => estimandMovement
        (mu[refinedNewPosteriorFrechetVariance mLarge kappaNewLarge |
          mSmall] omega)
        (mu[refinedOldPosteriorFrechetVariance mLarge kappaOldLarge |
          mSmall] omega) := by
  change mu[(refinedNewPosteriorFrechetVariance mLarge kappaNewLarge -
      refinedOldPosteriorFrechetVariance mLarge kappaOldLarge) | mSmall]
    =ᵐ[mu]
      mu[refinedNewPosteriorFrechetVariance mLarge kappaNewLarge |
          mSmall] -
        mu[refinedOldPosteriorFrechetVariance mLarge kappaOldLarge |
          mSmall]
  exact condExp_sub hNewIntegrable hOldIntegrable mSmall

omit [Nonempty S] [OpensMeasurableSpace S]
  [TopologicalSpace.SeparableSpace S] in
/-- The information term is independent almost surely of the selected RCD
versions for the old target. -/
theorem frechetInformationGain_versions_ae_eq
    [MeasurableSpace.CountablyGenerated S]
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (mSmall mLarge : MeasurableSpace Omega)
    (hSmallLarge : mSmall ≤ mLarge) (hLargeAmbient : mLarge ≤ mOmega)
    (KOld : Omega → S)
    (kappaOldSmall etaOldSmall :
      Kernel[mSmall, (inferInstance : MeasurableSpace S)] Omega S)
    (kappaOldLarge etaOldLarge :
      Kernel[mLarge, (inferInstance : MeasurableSpace S)] Omega S)
    [IsMarkovKernel kappaOldSmall] [IsMarkovKernel etaOldSmall]
    [IsMarkovKernel kappaOldLarge] [IsMarkovKernel etaOldLarge]
    (hkappaOldSmall : IsRegularConditionalLaw mu mSmall
      (hSmallLarge.trans hLargeAmbient) KOld kappaOldSmall)
    (hetaOldSmall : IsRegularConditionalLaw mu mSmall
      (hSmallLarge.trans hLargeAmbient) KOld etaOldSmall)
    (hkappaOldLarge : IsRegularConditionalLaw mu mLarge
      hLargeAmbient KOld kappaOldLarge)
    (hetaOldLarge : IsRegularConditionalLaw mu mLarge
      hLargeAmbient KOld etaOldLarge) :
    frechetInformationGain mu mSmall mLarge
        kappaOldSmall kappaOldLarge =ᵐ[mu]
      frechetInformationGain mu mSmall mLarge
        etaOldSmall etaOldLarge := by
  simpa only [frechetInformationGain_eq_refinementGain] using
    frechetRefinementGain_ae_eq
      mu mSmall mLarge hSmallLarge hLargeAmbient KOld
        kappaOldSmall etaOldSmall kappaOldLarge etaOldLarge
        hkappaOldSmall hetaOldSmall hkappaOldLarge hetaOldLarge

omit [Nonempty S] [OpensMeasurableSpace S]
  [TopologicalSpace.SeparableSpace S] in
/-- The movement term is independent almost surely of the selected fine-state
RCD versions for both the old and new targets. -/
theorem frechetEstimandMovement_versions_ae_eq
    [MeasurableSpace.CountablyGenerated S]
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (mSmall mLarge : MeasurableSpace Omega)
    (hLargeAmbient : mLarge ≤ mOmega)
    (KOld KNew : Omega → S)
    (kappaOldLarge etaOldLarge kappaNewLarge etaNewLarge :
      Kernel[mLarge, (inferInstance : MeasurableSpace S)] Omega S)
    [IsMarkovKernel kappaOldLarge] [IsMarkovKernel etaOldLarge]
    [IsMarkovKernel kappaNewLarge] [IsMarkovKernel etaNewLarge]
    (hkappaOldLarge : IsRegularConditionalLaw mu mLarge
      hLargeAmbient KOld kappaOldLarge)
    (hetaOldLarge : IsRegularConditionalLaw mu mLarge
      hLargeAmbient KOld etaOldLarge)
    (hkappaNewLarge : IsRegularConditionalLaw mu mLarge
      hLargeAmbient KNew kappaNewLarge)
    (hetaNewLarge : IsRegularConditionalLaw mu mLarge
      hLargeAmbient KNew etaNewLarge) :
    frechetEstimandMovement mu mSmall mLarge
        kappaOldLarge kappaNewLarge =ᵐ[mu]
      frechetEstimandMovement mu mSmall mLarge
        etaOldLarge etaNewLarge := by
  have hOldENN := posteriorFrechetVariance_ae_eq
    mu mLarge hLargeAmbient KOld kappaOldLarge etaOldLarge
      hkappaOldLarge hetaOldLarge
  have hNewENN := posteriorFrechetVariance_ae_eq
    mu mLarge hLargeAmbient KNew kappaNewLarge etaNewLarge
      hkappaNewLarge hetaNewLarge
  have hOldReal :
      refinedOldPosteriorFrechetVariance mLarge kappaOldLarge =ᵐ[mu]
        refinedOldPosteriorFrechetVariance mLarge etaOldLarge := by
    filter_upwards [hOldENN] with omega homega
    simp only [refinedOldPosteriorFrechetVariance,
      posteriorFrechetVarianceReal]
    rw [homega]
  have hNewReal :
      refinedNewPosteriorFrechetVariance mLarge kappaNewLarge =ᵐ[mu]
        refinedNewPosteriorFrechetVariance mLarge etaNewLarge := by
    filter_upwards [hNewENN] with omega homega
    simp only [refinedNewPosteriorFrechetVariance,
      posteriorFrechetVarianceReal]
    rw [homega]
  have hDifference :
      refinedNewPosteriorFrechetVariance mLarge kappaNewLarge -
          refinedOldPosteriorFrechetVariance mLarge kappaOldLarge =ᵐ[mu]
        refinedNewPosteriorFrechetVariance mLarge etaNewLarge -
          refinedOldPosteriorFrechetVariance mLarge etaOldLarge :=
    hNewReal.sub hOldReal
  change mu[(refinedNewPosteriorFrechetVariance mLarge kappaNewLarge -
      refinedOldPosteriorFrechetVariance mLarge kappaOldLarge) | mSmall]
      =ᵐ[mu]
    mu[(refinedNewPosteriorFrechetVariance mLarge etaNewLarge -
      refinedOldPosteriorFrechetVariance mLarge etaOldLarge) | mSmall]
  exact condExp_congr_ae hDifference

/-- Complete probabilistic exact one-step learning criterion. -/
theorem probabilistic_exact_one_step_learning_criterion
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (mSmall mLarge : MeasurableSpace Omega)
    (hSmallLarge : mSmall ≤ mLarge) (hLargeAmbient : mLarge ≤ mOmega)
    (KOld KNew : Omega → S)
    (hKOld : Measurable[mOmega] KOld)
    (hKNew : Measurable[mOmega] KNew)
    (kappaOldSmall :
      Kernel[mSmall, (inferInstance : MeasurableSpace S)] Omega S)
    (kappaOldLarge kappaNewLarge :
      Kernel[mLarge, (inferInstance : MeasurableSpace S)] Omega S)
    [IsMarkovKernel kappaOldSmall] [IsMarkovKernel kappaOldLarge]
    [IsMarkovKernel kappaNewLarge]
    (hkappaOldSmall : IsRegularConditionalLaw mu mSmall
      (hSmallLarge.trans hLargeAmbient) KOld kappaOldSmall)
    (hkappaOldLarge : IsRegularConditionalLaw mu mLarge
      hLargeAmbient KOld kappaOldLarge)
    (hkappaNewLarge : IsRegularConditionalLaw mu mLarge
      hLargeAmbient KNew kappaNewLarge)
    (s0 t0 : S)
    (hMomentOld : Integrable (fun omega => dist (KOld omega) s0 ^ 2) mu)
    (hMomentNew : Integrable (fun omega => dist (KNew omega) t0 ^ 2) mu) :
    (StronglyMeasurable[mSmall]
        (frechetInformationGain mu mSmall mLarge
          kappaOldSmall kappaOldLarge) ∧
      Integrable
        (frechetInformationGain mu mSmall mLarge
          kappaOldSmall kappaOldLarge) mu) ∧
    (StronglyMeasurable[mSmall]
        (frechetEstimandMovement mu mSmall mLarge
          kappaOldLarge kappaNewLarge) ∧
      Integrable
        (frechetEstimandMovement mu mSmall mLarge
          kappaOldLarge kappaNewLarge) mu) ∧
    (frechetInformationGain mu mSmall mLarge
        kappaOldSmall kappaOldLarge =
      frechetRefinementGain mu mSmall mLarge
        kappaOldSmall kappaOldLarge) ∧
    (0 ≤ᵐ[mu]
      frechetInformationGain mu mSmall mLarge
        kappaOldSmall kappaOldLarge) ∧
    ((fun omega =>
      currentPosteriorFrechetVariance mSmall kappaOldSmall omega -
        mu[refinedNewPosteriorFrechetVariance mLarge kappaNewLarge |
          mSmall] omega) =ᵐ[mu]
      fun omega =>
        frechetInformationGain mu mSmall mLarge
            kappaOldSmall kappaOldLarge omega -
          frechetEstimandMovement mu mSmall mLarge
            kappaOldLarge kappaNewLarge omega) ∧
    ((mu[refinedNewPosteriorFrechetVariance mLarge kappaNewLarge |
        mSmall] ≤ᵐ[mu]
      currentPosteriorFrechetVariance mSmall kappaOldSmall) ↔
      (frechetEstimandMovement mu mSmall mLarge
          kappaOldLarge kappaNewLarge ≤ᵐ[mu]
        frechetInformationGain mu mSmall mLarge
          kappaOldSmall kappaOldLarge)) := by
  have hVariances := oneStepPosteriorFrechetVariances_wellPosed
    mu mSmall mLarge hSmallLarge hLargeAmbient KOld KNew hKOld hKNew
      kappaOldSmall kappaOldLarge kappaNewLarge hkappaOldSmall
      hkappaOldLarge hkappaNewLarge s0 t0 hMomentOld hMomentNew
  have hVCurrentMeasurable := hVariances.1.1
  have hVCurrentIntegrable := hVariances.1.2
  have hUIntegrable := hVariances.2.1.2
  have hVNewIntegrable := hVariances.2.2.2

  have hJMeasurable : StronglyMeasurable[mSmall]
      (frechetInformationGain mu mSmall mLarge
        kappaOldSmall kappaOldLarge) := by
    exact hVCurrentMeasurable.sub stronglyMeasurable_condExp
  have hJIntegrable : Integrable
      (frechetInformationGain mu mSmall mLarge
        kappaOldSmall kappaOldLarge) mu := by
    exact hVCurrentIntegrable.sub integrable_condExp
  have hSMeasurable : StronglyMeasurable[mSmall]
      (frechetEstimandMovement mu mSmall mLarge
        kappaOldLarge kappaNewLarge) := by
    exact stronglyMeasurable_condExp
  have hSIntegrable : Integrable
      (frechetEstimandMovement mu mSmall mLarge
        kappaOldLarge kappaNewLarge) mu := by
    exact integrable_condExp

  have hJIdentification :
      frechetInformationGain mu mSmall mLarge
          kappaOldSmall kappaOldLarge =
        frechetRefinementGain mu mSmall mLarge
          kappaOldSmall kappaOldLarge :=
    frechetInformationGain_eq_refinementGain
      mu mSmall mLarge kappaOldSmall kappaOldLarge
  have hGainWellPosed := frechetRefinementGain_wellPosed
    mu mSmall mLarge hSmallLarge hLargeAmbient KOld hKOld
      kappaOldSmall kappaOldLarge hkappaOldSmall hkappaOldLarge
      s0 hMomentOld
  have hJNonnegative : 0 ≤ᵐ[mu]
      frechetInformationGain mu mSmall mLarge
        kappaOldSmall kappaOldLarge := by
    rw [hJIdentification]
    exact hGainWellPosed.2.2

  have hSRepresentation := frechetEstimandMovement_ae_eq
    mu mSmall mLarge kappaOldLarge kappaNewLarge
      hUIntegrable hVNewIntegrable
  have hIdentity :
      (fun omega =>
        currentPosteriorFrechetVariance mSmall kappaOldSmall omega -
          mu[refinedNewPosteriorFrechetVariance mLarge kappaNewLarge |
            mSmall] omega) =ᵐ[mu]
        fun omega =>
          frechetInformationGain mu mSmall mLarge
              kappaOldSmall kappaOldLarge omega -
            frechetEstimandMovement mu mSmall mLarge
              kappaOldLarge kappaNewLarge omega := by
    filter_upwards [hSRepresentation] with omega hSomega
    rw [hSomega]
    exact exact_one_step_identity
      (currentPosteriorFrechetVariance mSmall kappaOldSmall omega)
      (mu[refinedOldPosteriorFrechetVariance mLarge kappaOldLarge |
        mSmall] omega)
      (mu[refinedNewPosteriorFrechetVariance mLarge kappaNewLarge |
        mSmall] omega)

  have hCriterion :
      (mu[refinedNewPosteriorFrechetVariance mLarge kappaNewLarge |
          mSmall] ≤ᵐ[mu]
        currentPosteriorFrechetVariance mSmall kappaOldSmall) ↔
        (frechetEstimandMovement mu mSmall mLarge
            kappaOldLarge kappaNewLarge ≤ᵐ[mu]
          frechetInformationGain mu mSmall mLarge
            kappaOldSmall kappaOldLarge) := by
    constructor
    · intro hLearning
      filter_upwards [hLearning, hSRepresentation] with
          omega hLearningOmega hSOmega
      rw [hSOmega]
      exact (exact_learning_iff
        (currentPosteriorFrechetVariance mSmall kappaOldSmall omega)
        (mu[refinedOldPosteriorFrechetVariance mLarge kappaOldLarge |
          mSmall] omega)
        (mu[refinedNewPosteriorFrechetVariance mLarge kappaNewLarge |
          mSmall] omega)).1 hLearningOmega
    · intro hDominance
      filter_upwards [hDominance, hSRepresentation] with
          omega hDominanceOmega hSOmega
      rw [hSOmega] at hDominanceOmega
      exact (exact_learning_iff
        (currentPosteriorFrechetVariance mSmall kappaOldSmall omega)
        (mu[refinedOldPosteriorFrechetVariance mLarge kappaOldLarge |
          mSmall] omega)
        (mu[refinedNewPosteriorFrechetVariance mLarge kappaNewLarge |
          mSmall] omega)).2 hDominanceOmega

  exact ⟨⟨hJMeasurable, hJIntegrable⟩,
    ⟨hSMeasurable, hSIntegrable⟩,
    hJIdentification, hJNonnegative, hIdentity, hCriterion⟩

end ProbabilisticExactCriterion

end

end SequentialLearning
