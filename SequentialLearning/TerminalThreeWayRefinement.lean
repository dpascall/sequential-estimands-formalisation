import SequentialLearning.FrechetRefinement
import SequentialLearning.ThreeWayRefinement

/-!
# Three-way refinement for the terminal target

This file specialises the scalar three-way refinement algebra to posterior
Frechet variances of one fixed terminal target `KLimit`.  The three nested
information states represent current observations, limiting observational
information, and a further enlargement such as an oracle disclosure.
-/

namespace SequentialLearning

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal MeasureTheory ProbabilityTheory

noncomputable section

section TerminalThreeWayRefinement

variable {Omega S : Type*} {mOmega : MeasurableSpace Omega}
  [PseudoMetricSpace S] [MeasurableSpace S] [Nonempty S]
  [OpensMeasurableSpace S] [TopologicalSpace.SeparableSpace S]

/-- Uncertainty about the terminal target reducible by passing from the
current information state to the limiting observational information state. -/
def terminalReducibleGain
    (mu : Measure[mOmega] Omega)
    (mCurrent mObservedLimit : MeasurableSpace Omega)
    (kappaCurrent :
      Kernel[mCurrent, (inferInstance : MeasurableSpace S)] Omega S)
    (kappaObservedLimit :
      Kernel[mObservedLimit, (inferInstance : MeasurableSpace S)] Omega S) :
    Omega → ℝ :=
  frechetRefinementGain mu mCurrent mObservedLimit
    kappaCurrent kappaObservedLimit

/-- Uncertainty resolved by a further information enlargement, viewed from
the current information state. -/
def terminalEnlargementGain
    (mu : Measure[mOmega] Omega)
    (mCurrent mObservedLimit mEnlarged : MeasurableSpace Omega)
    (kappaObservedLimit :
      Kernel[mObservedLimit, (inferInstance : MeasurableSpace S)] Omega S)
    (kappaEnlarged :
      Kernel[mEnlarged, (inferInstance : MeasurableSpace S)] Omega S) :
    Omega → ℝ :=
  mu[frechetRefinementGain mu mObservedLimit mEnlarged
    kappaObservedLimit kappaEnlarged | mCurrent]

/-- Posterior uncertainty remaining after the enlargement, viewed from the
current information state. -/
def terminalResidualRisk
    (mu : Measure[mOmega] Omega)
    (mCurrent mEnlarged : MeasurableSpace Omega)
    (kappaEnlarged :
      Kernel[mEnlarged, (inferInstance : MeasurableSpace S)] Omega S) :
    Omega → ℝ :=
  mu[posteriorFrechetVarianceReal mEnlarged kappaEnlarged | mCurrent]

/-- The direct current-to-enlarged gain decomposes into the
current-to-observational-limit gain plus the enlargement gain projected back
to current information. -/
theorem terminalRefinementGain_cocycle
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (mCurrent mObservedLimit mEnlarged : MeasurableSpace Omega)
    (hCurrentLimit : mCurrent ≤ mObservedLimit)
    (hLimitEnlarged : mObservedLimit ≤ mEnlarged)
    (hEnlargedAmbient : mEnlarged ≤ mOmega)
    (KLimit : Omega → S) (hKLimit : Measurable[mOmega] KLimit)
    (kappaCurrent :
      Kernel[mCurrent, (inferInstance : MeasurableSpace S)] Omega S)
    (kappaObservedLimit :
      Kernel[mObservedLimit, (inferInstance : MeasurableSpace S)] Omega S)
    (kappaEnlarged :
      Kernel[mEnlarged, (inferInstance : MeasurableSpace S)] Omega S)
    [IsMarkovKernel kappaCurrent]
    [IsMarkovKernel kappaObservedLimit]
    [IsMarkovKernel kappaEnlarged]
    (_hkappaCurrent : IsRegularConditionalLaw mu mCurrent
      (hCurrentLimit.trans (hLimitEnlarged.trans hEnlargedAmbient))
      KLimit kappaCurrent)
    (hkappaObservedLimit : IsRegularConditionalLaw mu mObservedLimit
      (hLimitEnlarged.trans hEnlargedAmbient) KLimit kappaObservedLimit)
    (hkappaEnlarged : IsRegularConditionalLaw mu mEnlarged
      hEnlargedAmbient KLimit kappaEnlarged)
    (s0 : S)
    (hMoment : Integrable
      (fun omega => dist (KLimit omega) s0 ^ 2) mu) :
    frechetRefinementGain mu mCurrent mEnlarged
        kappaCurrent kappaEnlarged =ᵐ[mu]
      fun omega =>
        terminalReducibleGain mu mCurrent mObservedLimit
            kappaCurrent kappaObservedLimit omega +
          terminalEnlargementGain mu mCurrent mObservedLimit mEnlarged
            kappaObservedLimit kappaEnlarged omega := by
  have hMiddleBundle := posteriorFrechet_finite_and_integrable
    mu mObservedLimit (hLimitEnlarged.trans hEnlargedAmbient)
      KLimit hKLimit kappaObservedLimit hkappaObservedLimit s0 hMoment
  have hFineBundle := posteriorFrechet_finite_and_integrable
    mu mEnlarged hEnlargedAmbient KLimit hKLimit
      kappaEnlarged hkappaEnlarged s0 hMoment
  have hMiddleIntegrable : Integrable
      (posteriorFrechetVarianceReal mObservedLimit
        kappaObservedLimit) mu := by
    change Integrable
      (fun omega =>
        (frechetVariance (kappaObservedLimit omega)).toReal) mu
    exact hMiddleBundle.2.2.2
  have hFineIntegrable : Integrable
      (posteriorFrechetVarianceReal mEnlarged kappaEnlarged) mu := by
    change Integrable
      (fun omega => (frechetVariance (kappaEnlarged omega)).toReal) mu
    exact hFineBundle.2.2.2
  simpa only [terminalReducibleGain, terminalEnlargementGain,
    frechetRefinementGain] using
      refinementGain_cocycle mu mCurrent mObservedLimit mEnlarged
        hCurrentLimit hLimitEnlarged hEnlargedAmbient
        (posteriorFrechetVarianceReal mCurrent kappaCurrent)
        (posteriorFrechetVarianceReal mObservedLimit kappaObservedLimit)
        (posteriorFrechetVarianceReal mEnlarged kappaEnlarged)
        hMiddleIntegrable hFineIntegrable

/-- The three terms in the terminal-target decomposition are measurable in
the current information state, integrable, and nonnegative almost surely. -/
theorem terminalThreeWayTerms_wellPosed
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (mCurrent mObservedLimit mEnlarged : MeasurableSpace Omega)
    (hCurrentLimit : mCurrent ≤ mObservedLimit)
    (hLimitEnlarged : mObservedLimit ≤ mEnlarged)
    (hEnlargedAmbient : mEnlarged ≤ mOmega)
    (KLimit : Omega → S) (hKLimit : Measurable[mOmega] KLimit)
    (kappaCurrent :
      Kernel[mCurrent, (inferInstance : MeasurableSpace S)] Omega S)
    (kappaObservedLimit :
      Kernel[mObservedLimit, (inferInstance : MeasurableSpace S)] Omega S)
    (kappaEnlarged :
      Kernel[mEnlarged, (inferInstance : MeasurableSpace S)] Omega S)
    [IsMarkovKernel kappaCurrent]
    [IsMarkovKernel kappaObservedLimit]
    [IsMarkovKernel kappaEnlarged]
    (hkappaCurrent : IsRegularConditionalLaw mu mCurrent
      (hCurrentLimit.trans (hLimitEnlarged.trans hEnlargedAmbient))
      KLimit kappaCurrent)
    (hkappaObservedLimit : IsRegularConditionalLaw mu mObservedLimit
      (hLimitEnlarged.trans hEnlargedAmbient) KLimit kappaObservedLimit)
    (hkappaEnlarged : IsRegularConditionalLaw mu mEnlarged
      hEnlargedAmbient KLimit kappaEnlarged)
    (s0 : S)
    (hMoment : Integrable
      (fun omega => dist (KLimit omega) s0 ^ 2) mu) :
    (StronglyMeasurable[mCurrent]
        (terminalReducibleGain mu mCurrent mObservedLimit
          kappaCurrent kappaObservedLimit) ∧
      Integrable
        (terminalReducibleGain mu mCurrent mObservedLimit
          kappaCurrent kappaObservedLimit) mu ∧
      0 ≤ᵐ[mu]
        terminalReducibleGain mu mCurrent mObservedLimit
          kappaCurrent kappaObservedLimit) ∧
    (StronglyMeasurable[mCurrent]
        (terminalEnlargementGain mu mCurrent mObservedLimit mEnlarged
          kappaObservedLimit kappaEnlarged) ∧
      Integrable
        (terminalEnlargementGain mu mCurrent mObservedLimit mEnlarged
          kappaObservedLimit kappaEnlarged) mu ∧
      0 ≤ᵐ[mu]
        terminalEnlargementGain mu mCurrent mObservedLimit mEnlarged
          kappaObservedLimit kappaEnlarged) ∧
    (StronglyMeasurable[mCurrent]
        (terminalResidualRisk mu mCurrent mEnlarged kappaEnlarged) ∧
      Integrable
        (terminalResidualRisk mu mCurrent mEnlarged kappaEnlarged) mu ∧
      0 ≤ᵐ[mu]
        terminalResidualRisk mu mCurrent mEnlarged kappaEnlarged) := by
  have hGainCurrentLimit := frechetRefinementGain_wellPosed
    mu mCurrent mObservedLimit hCurrentLimit
      (hLimitEnlarged.trans hEnlargedAmbient) KLimit hKLimit
      kappaCurrent kappaObservedLimit hkappaCurrent
      hkappaObservedLimit s0 hMoment
  have hGainLimitEnlarged := frechetRefinementGain_wellPosed
    mu mObservedLimit mEnlarged hLimitEnlarged hEnlargedAmbient
      KLimit hKLimit kappaObservedLimit kappaEnlarged
      hkappaObservedLimit hkappaEnlarged s0 hMoment
  have hFineBundle := posteriorFrechet_finite_and_integrable
    mu mEnlarged hEnlargedAmbient KLimit hKLimit
      kappaEnlarged hkappaEnlarged s0 hMoment
  have hFineIntegrable : Integrable
      (posteriorFrechetVarianceReal mEnlarged kappaEnlarged) mu := by
    change Integrable
      (fun omega => (frechetVariance (kappaEnlarged omega)).toReal) mu
    exact hFineBundle.2.2.2
  have hFineNonnegative : 0 ≤ᵐ[mu]
      posteriorFrechetVarianceReal mEnlarged kappaEnlarged := by
    filter_upwards with omega
    exact ENNReal.toReal_nonneg
  refine ⟨⟨hGainCurrentLimit.1, hGainCurrentLimit.2.1,
      hGainCurrentLimit.2.2⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · exact stronglyMeasurable_condExp
  · exact integrable_condExp
  · exact condExp_nonneg hGainLimitEnlarged.2.2
  · exact stronglyMeasurable_condExp
  · exact integrable_condExp
  · exact condExp_nonneg hFineNonnegative

/-- Terminal-target three-way refinement:

`current variance = reducible observational gain
  + enlargement-resolvable gain + residual enlarged variance`,

with all three summands nonnegative almost surely. -/
theorem terminalThreeWay_refinement
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (mCurrent mObservedLimit mEnlarged : MeasurableSpace Omega)
    (hCurrentLimit : mCurrent ≤ mObservedLimit)
    (hLimitEnlarged : mObservedLimit ≤ mEnlarged)
    (hEnlargedAmbient : mEnlarged ≤ mOmega)
    (KLimit : Omega → S) (hKLimit : Measurable[mOmega] KLimit)
    (kappaCurrent :
      Kernel[mCurrent, (inferInstance : MeasurableSpace S)] Omega S)
    (kappaObservedLimit :
      Kernel[mObservedLimit, (inferInstance : MeasurableSpace S)] Omega S)
    (kappaEnlarged :
      Kernel[mEnlarged, (inferInstance : MeasurableSpace S)] Omega S)
    [IsMarkovKernel kappaCurrent]
    [IsMarkovKernel kappaObservedLimit]
    [IsMarkovKernel kappaEnlarged]
    (hkappaCurrent : IsRegularConditionalLaw mu mCurrent
      (hCurrentLimit.trans (hLimitEnlarged.trans hEnlargedAmbient))
      KLimit kappaCurrent)
    (hkappaObservedLimit : IsRegularConditionalLaw mu mObservedLimit
      (hLimitEnlarged.trans hEnlargedAmbient) KLimit kappaObservedLimit)
    (hkappaEnlarged : IsRegularConditionalLaw mu mEnlarged
      hEnlargedAmbient KLimit kappaEnlarged)
    (s0 : S)
    (hMoment : Integrable
      (fun omega => dist (KLimit omega) s0 ^ 2) mu) :
    ((posteriorFrechetVarianceReal mCurrent kappaCurrent) =ᵐ[mu]
      fun omega =>
        terminalReducibleGain mu mCurrent mObservedLimit
            kappaCurrent kappaObservedLimit omega +
          terminalEnlargementGain mu mCurrent mObservedLimit mEnlarged
              kappaObservedLimit kappaEnlarged omega +
            terminalResidualRisk mu mCurrent mEnlarged
              kappaEnlarged omega) ∧
    (0 ≤ᵐ[mu]
      terminalReducibleGain mu mCurrent mObservedLimit
        kappaCurrent kappaObservedLimit) ∧
    (0 ≤ᵐ[mu]
      terminalEnlargementGain mu mCurrent mObservedLimit mEnlarged
        kappaObservedLimit kappaEnlarged) ∧
    (0 ≤ᵐ[mu]
      terminalResidualRisk mu mCurrent mEnlarged kappaEnlarged) := by
  have hMiddleBundle := posteriorFrechet_finite_and_integrable
    mu mObservedLimit (hLimitEnlarged.trans hEnlargedAmbient)
      KLimit hKLimit kappaObservedLimit hkappaObservedLimit s0 hMoment
  have hFineBundle := posteriorFrechet_finite_and_integrable
    mu mEnlarged hEnlargedAmbient KLimit hKLimit
      kappaEnlarged hkappaEnlarged s0 hMoment
  have hMiddleIntegrable : Integrable
      (posteriorFrechetVarianceReal mObservedLimit
        kappaObservedLimit) mu := by
    change Integrable
      (fun omega =>
        (frechetVariance (kappaObservedLimit omega)).toReal) mu
    exact hMiddleBundle.2.2.2
  have hFineIntegrable : Integrable
      (posteriorFrechetVarianceReal mEnlarged kappaEnlarged) mu := by
    change Integrable
      (fun omega => (frechetVariance (kappaEnlarged omega)).toReal) mu
    exact hFineBundle.2.2.2
  have hGainCurrentLimit := frechetRefinementGain_wellPosed
    mu mCurrent mObservedLimit hCurrentLimit
      (hLimitEnlarged.trans hEnlargedAmbient) KLimit hKLimit
      kappaCurrent kappaObservedLimit hkappaCurrent
      hkappaObservedLimit s0 hMoment
  have hGainLimitEnlarged := frechetRefinementGain_wellPosed
    mu mObservedLimit mEnlarged hLimitEnlarged hEnlargedAmbient
      KLimit hKLimit kappaObservedLimit kappaEnlarged
      hkappaObservedLimit hkappaEnlarged s0 hMoment
  have hFineNonnegative : 0 ≤ᵐ[mu]
      posteriorFrechetVarianceReal mEnlarged kappaEnlarged := by
    filter_upwards with omega
    exact ENNReal.toReal_nonneg
  simpa only [terminalReducibleGain, terminalEnlargementGain,
    terminalResidualRisk, frechetRefinementGain] using
      three_way_refinement mu mCurrent mObservedLimit mEnlarged
        hCurrentLimit hLimitEnlarged hEnlargedAmbient
        (posteriorFrechetVarianceReal mCurrent kappaCurrent)
        (posteriorFrechetVarianceReal mObservedLimit kappaObservedLimit)
        (posteriorFrechetVarianceReal mEnlarged kappaEnlarged)
        hMiddleIntegrable hFineIntegrable hGainCurrentLimit.2.2
        hGainLimitEnlarged.2.2 hFineNonnegative

end TerminalThreeWayRefinement

end

end SequentialLearning
