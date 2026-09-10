import SequentialLearning.BreakEvenCriterion
import SequentialLearning.FrechetPosteriorDisplacementBound
import SequentialLearning.ProbabilisticExactCriterion

/-!
# Frechet predictable displacement envelope

This file upgrades the scalar and Hilbert wrappers in
`PredictableDisplacementEnvelope` and `BreakEvenCriterion` to the manuscript's
full pseudometric/RCD setting.  A single joint conditional law of the old and
new estimands supplies both fine-state marginal variances and their posterior
Wasserstein displacement.
-/

namespace SequentialLearning

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

noncomputable section

section FrechetPredictableDisplacementEnvelope

variable {Omega S : Type*} {mOmega : MeasurableSpace Omega}
  [PseudoMetricSpace S] [MeasurableSpace S] [Nonempty S]
  [OpensMeasurableSpace S] [TopologicalSpace.SeparableSpace S]

/-- The manuscript's predictable displacement envelope in its full
pseudometric/RCD form.

The first marginal of `rho` is the fine-state conditional law of `KOld`, the
second is that of `KNew`, and `posteriorDisplacement rho` is the completed-space
posterior Wasserstein displacement between them. -/
theorem frechet_predictable_displacement_envelope
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (mSmall mLarge : MeasurableSpace Omega)
    (hSmallLarge : mSmall ≤ mLarge) (hLargeAmbient : mLarge ≤ mOmega)
    (KOld KNew : Omega → S)
    (hKOld : Measurable[mOmega] KOld)
    (hKNew : Measurable[mOmega] KNew)
    (kappaOldSmall :
      Kernel[mSmall, (inferInstance : MeasurableSpace S)] Omega S)
    [IsMarkovKernel kappaOldSmall]
    (hkappaOldSmall : IsRegularConditionalLaw mu mSmall
      (hSmallLarge.trans hLargeAmbient) KOld kappaOldSmall)
    (rho : Kernel[mLarge,
      (inferInstance : MeasurableSpace (S × S))] Omega (S × S))
    [IsMarkovKernel rho]
    (hrho : IsRegularConditionalLaw mu mLarge hLargeAmbient
      (fun omega => (KOld omega, KNew omega)) rho)
    (s0 t0 : S)
    (hMomentOld : Integrable (fun omega => dist (KOld omega) s0 ^ 2) mu)
    (hMomentNew : Integrable (fun omega => dist (KNew omega) t0 ^ 2) mu)
    (hW : Wasserstein2LawMeasurable (PseudometricCompletion S)) :
    StronglyMeasurable[mSmall]
        (predictableDisplacementRMS mu mSmall (posteriorDisplacement rho)) ∧
    MemLp (posteriorDisplacement rho) 2 mu ∧
    ((fun omega =>
        mu[refinedOldPosteriorFrechetVariance mLarge (Kernel.fst rho) |
          mSmall] omega) =
      fun omega =>
        currentPosteriorFrechetVariance mSmall kappaOldSmall omega -
          frechetInformationGain mu mSmall mLarge
            kappaOldSmall (Kernel.fst rho) omega) ∧
    (mu[refinedNewPosteriorFrechetVariance mLarge (Kernel.snd rho) |
        mSmall] ≤ᵐ[mu]
      fun omega =>
        (Real.sqrt
            (mu[refinedOldPosteriorFrechetVariance mLarge (Kernel.fst rho) |
              mSmall] omega) +
          predictableDisplacementRMS mu mSmall
            (posteriorDisplacement rho) omega) ^ 2) ∧
    (mu[refinedNewPosteriorFrechetVariance mLarge (Kernel.snd rho) |
        mSmall] ≤ᵐ[mu]
      fun omega =>
        (Real.sqrt
            (currentPosteriorFrechetVariance mSmall kappaOldSmall omega -
              frechetInformationGain mu mSmall mLarge
                kappaOldSmall (Kernel.fst rho) omega) +
          predictableDisplacementRMS mu mSmall
            (posteriorDisplacement rho) omega) ^ 2) := by
  have hOldLargeRCD := regularConditionalLaw_fst_of_pair
    mu mLarge hLargeAmbient KOld KNew hKOld hKNew rho hrho
  have hNewLargeRCD := regularConditionalLaw_snd_of_pair
    mu mLarge hLargeAmbient KOld KNew hKOld hKNew rho hrho
  have hMomentNewAtOld :
      Integrable (fun omega => dist (KNew omega) s0 ^ 2) mu :=
    integrable_squaredDistance_of_reference
      mu KNew hKNew t0 hMomentNew s0
  have hPairMoment :
      Integrable (fun omega => dist (KOld omega) (KNew omega) ^ 2) mu :=
    integrable_pairSquaredDistance_of_reference
      mu KOld KNew hKOld hKNew s0 hMomentOld hMomentNewAtOld
  have hDelta : MemLp (posteriorDisplacement rho) 2 mu :=
    posteriorDisplacement_memLp_two
      mu mLarge hLargeAmbient KOld KNew hKOld hKNew rho hrho hW hPairMoment
  have hVariances := oneStepPosteriorFrechetVariances_wellPosed
    mu mSmall mLarge hSmallLarge hLargeAmbient KOld KNew hKOld hKNew
      kappaOldSmall (Kernel.fst rho) (Kernel.snd rho)
      hkappaOldSmall hOldLargeRCD hNewLargeRCD s0 t0
      hMomentOld hMomentNew
  have hDisplacement := frechet_posterior_displacement_bound
    mu mSmall mLarge hLargeAmbient KOld KNew hKOld hKNew rho hrho
      s0 hMomentOld hMomentNewAtOld hW
  have hOldNonnegative :
      0 ≤ᵐ[mu]
        refinedOldPosteriorFrechetVariance mLarge (Kernel.fst rho) :=
    Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg
  have hNewNonnegative :
      0 ≤ᵐ[mu]
        refinedNewPosteriorFrechetVariance mLarge (Kernel.snd rho) :=
    Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg
  have hEnvelope := predictable_displacement_envelope
    mu mSmall
      (refinedOldPosteriorFrechetVariance mLarge (Kernel.fst rho))
      (refinedNewPosteriorFrechetVariance mLarge (Kernel.snd rho))
      (posteriorDisplacement rho)
      hOldNonnegative hNewNonnegative hDisplacement.1
      hVariances.2.1.2 hVariances.2.2.2 hDelta
  have hAIdentity :
      (fun omega =>
          mu[refinedOldPosteriorFrechetVariance mLarge (Kernel.fst rho) |
            mSmall] omega) =
        fun omega =>
          currentPosteriorFrechetVariance mSmall kappaOldSmall omega -
            frechetInformationGain mu mSmall mLarge
              kappaOldSmall (Kernel.fst rho) omega := by
    funext omega
    simp only [frechetInformationGain, informationGain]
    ring
  have hEnvelopeInformation :
      mu[refinedNewPosteriorFrechetVariance mLarge (Kernel.snd rho) |
          mSmall] ≤ᵐ[mu]
        fun omega =>
          (Real.sqrt
              (currentPosteriorFrechetVariance mSmall kappaOldSmall omega -
                frechetInformationGain mu mSmall mLarge
                  kappaOldSmall (Kernel.fst rho) omega) +
            predictableDisplacementRMS mu mSmall
              (posteriorDisplacement rho) omega) ^ 2 := by
    filter_upwards [hEnvelope] with omega hEnvelopeOmega
    rw [← congr_fun hAIdentity omega]
    exact hEnvelopeOmega
  exact
    ⟨stronglyMeasurable_predictableDisplacementRMS
        mu mSmall (posteriorDisplacement rho),
      hDelta, hAIdentity, hEnvelope, hEnvelopeInformation⟩

/-- The full Fréchet/RCD break-even criterion.  The displayed threshold is
measurable and nonnegative, and controlling predictable posterior displacement
by this threshold guarantees one-step posterior-variance learning. -/
theorem frechet_break_even_criterion
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (mSmall mLarge : MeasurableSpace Omega)
    (hSmallLarge : mSmall ≤ mLarge) (hLargeAmbient : mLarge ≤ mOmega)
    (KOld KNew : Omega → S)
    (hKOld : Measurable[mOmega] KOld)
    (hKNew : Measurable[mOmega] KNew)
    (kappaOldSmall :
      Kernel[mSmall, (inferInstance : MeasurableSpace S)] Omega S)
    [IsMarkovKernel kappaOldSmall]
    (hkappaOldSmall : IsRegularConditionalLaw mu mSmall
      (hSmallLarge.trans hLargeAmbient) KOld kappaOldSmall)
    (rho : Kernel[mLarge,
      (inferInstance : MeasurableSpace (S × S))] Omega (S × S))
    [IsMarkovKernel rho]
    (hrho : IsRegularConditionalLaw mu mLarge hLargeAmbient
      (fun omega => (KOld omega, KNew omega)) rho)
    (s0 t0 : S)
    (hMomentOld : Integrable (fun omega => dist (KOld omega) s0 ^ 2) mu)
    (hMomentNew : Integrable (fun omega => dist (KNew omega) t0 ^ 2) mu)
    (hW : Wasserstein2LawMeasurable (PseudometricCompletion S)) :
    StronglyMeasurable[mSmall]
        (predictableDisplacementRMS mu mSmall (posteriorDisplacement rho)) ∧
    StronglyMeasurable[mSmall]
        (breakEvenThreshold
          (currentPosteriorFrechetVariance mSmall kappaOldSmall)
          (frechetInformationGain mu mSmall mLarge
            kappaOldSmall (Kernel.fst rho))) ∧
    (0 ≤ᵐ[mu]
      frechetInformationGain mu mSmall mLarge
        kappaOldSmall (Kernel.fst rho)) ∧
    (frechetInformationGain mu mSmall mLarge
        kappaOldSmall (Kernel.fst rho) ≤ᵐ[mu]
      currentPosteriorFrechetVariance mSmall kappaOldSmall) ∧
    (0 ≤ᵐ[mu]
      breakEvenThreshold
        (currentPosteriorFrechetVariance mSmall kappaOldSmall)
        (frechetInformationGain mu mSmall mLarge
          kappaOldSmall (Kernel.fst rho))) ∧
    ((predictableDisplacementRMS mu mSmall (posteriorDisplacement rho) ≤ᵐ[mu]
        breakEvenThreshold
          (currentPosteriorFrechetVariance mSmall kappaOldSmall)
          (frechetInformationGain mu mSmall mLarge
            kappaOldSmall (Kernel.fst rho))) →
      mu[refinedNewPosteriorFrechetVariance mLarge (Kernel.snd rho) |
          mSmall] ≤ᵐ[mu]
        currentPosteriorFrechetVariance mSmall kappaOldSmall) := by
  let VCurrent : Omega → ℝ :=
    currentPosteriorFrechetVariance mSmall kappaOldSmall
  let J : Omega → ℝ :=
    frechetInformationGain mu mSmall mLarge
      kappaOldSmall (Kernel.fst rho)
  let A : Omega → ℝ := fun omega => VCurrent omega - J omega
  let D : Omega → ℝ :=
    predictableDisplacementRMS mu mSmall (posteriorDisplacement rho)
  have hOldLargeRCD := regularConditionalLaw_fst_of_pair
    mu mLarge hLargeAmbient KOld KNew hKOld hKNew rho hrho
  have hEnvelopeResult := frechet_predictable_displacement_envelope
    mu mSmall mLarge hSmallLarge hLargeAmbient KOld KNew hKOld hKNew
      kappaOldSmall hkappaOldSmall rho hrho s0 t0
      hMomentOld hMomentNew hW
  have hAIdentity := hEnvelopeResult.2.2.1
  have hEnvelope :
      mu[refinedNewPosteriorFrechetVariance mLarge (Kernel.snd rho) |
          mSmall] ≤ᵐ[mu]
        fun omega => (Real.sqrt (A omega) + D omega) ^ 2 := by
    simpa only [A, VCurrent, J, D] using hEnvelopeResult.2.2.2.2
  have hVCurrentNonnegative : 0 ≤ᵐ[mu] VCurrent :=
    Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg
  have hOldLargeNonnegative :
      0 ≤ᵐ[mu]
        refinedOldPosteriorFrechetVariance mLarge (Kernel.fst rho) :=
    Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg
  have hOldPredictableNonnegative :
      0 ≤ᵐ[mu]
        mu[refinedOldPosteriorFrechetVariance mLarge (Kernel.fst rho) |
          mSmall] :=
    condExp_nonneg hOldLargeNonnegative
  have hANonnegative : 0 ≤ᵐ[mu] A := by
    filter_upwards [hOldPredictableNonnegative] with omega hOldOmega
    change 0 ≤ VCurrent omega - J omega
    rw [← congr_fun hAIdentity omega]
    exact hOldOmega
  have hDNonnegative : 0 ≤ᵐ[mu] D := by
    filter_upwards with omega
    exact Real.sqrt_nonneg _
  have hGainWellPosed := frechetRefinementGain_wellPosed
    mu mSmall mLarge hSmallLarge hLargeAmbient KOld hKOld
      kappaOldSmall (Kernel.fst rho) hkappaOldSmall hOldLargeRCD
      s0 hMomentOld
  have hJNonnegative : 0 ≤ᵐ[mu] J := by
    simpa only [J, frechetInformationGain_eq_refinementGain] using
      hGainWellPosed.2.2
  have hJLeV : J ≤ᵐ[mu] VCurrent := by
    filter_upwards [hANonnegative] with omega hAOmega
    change 0 ≤ VCurrent omega - J omega at hAOmega
    linarith
  have hThresholdNonnegative :
      0 ≤ᵐ[mu] breakEvenThreshold VCurrent J := by
    filter_upwards [hJNonnegative] with omega hJOmega
    simp only [Pi.zero_apply] at hJOmega
    dsimp only [breakEvenThreshold]
    exact sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
  have hVCurrentMeasurable : StronglyMeasurable[mSmall] VCurrent := by
    exact stronglyMeasurable_posteriorFrechetVarianceReal
      mSmall kappaOldSmall
  have hJMeasurable : StronglyMeasurable[mSmall] J := by
    simpa only [J, frechetInformationGain_eq_refinementGain] using
      hGainWellPosed.1
  have hThresholdMeasurable :
      StronglyMeasurable[mSmall] (breakEvenThreshold VCurrent J) :=
    stronglyMeasurable_breakEvenThreshold
      mSmall VCurrent J hVCurrentMeasurable hJMeasurable
  have hImplication :
      (D ≤ᵐ[mu] breakEvenThreshold VCurrent J) →
        mu[refinedNewPosteriorFrechetVariance mLarge (Kernel.snd rho) |
            mSmall] ≤ᵐ[mu] VCurrent := by
    intro hBreakEven
    have hBreakEvenA : D ≤ᵐ[mu]
        fun omega => Real.sqrt (VCurrent omega) - Real.sqrt (A omega) := by
      change D ≤ᵐ[mu]
        (fun omega =>
          Real.sqrt (VCurrent omega) - Real.sqrt (VCurrent omega - J omega))
        at hBreakEven
      simpa only [A] using hBreakEven
    exact break_even_of_envelope mu
      (mu[refinedNewPosteriorFrechetVariance mLarge (Kernel.snd rho) |
        mSmall]) A VCurrent D
      hANonnegative hVCurrentNonnegative hDNonnegative hEnvelope hBreakEvenA
  simpa only [VCurrent, J, D] using
    ⟨hEnvelopeResult.1, hThresholdMeasurable, hJNonnegative, hJLeV,
      hThresholdNonnegative, hImplication⟩

end FrechetPredictableDisplacementEnvelope

end

end SequentialLearning
