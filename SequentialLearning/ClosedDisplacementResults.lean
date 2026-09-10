import SequentialLearning.FrechetPredictableDisplacementEnvelope
import SequentialLearning.PolishWasserstein2Measurability

/-!
# Closed displacement chain

This module discharges the temporary proposition-valued
`Wasserstein2LawMeasurable` input from the manuscript-facing displacement results.  The original
Phase 0 declarations are retained unchanged; the declarations below are their closed Phase 1
interfaces.
-/

namespace SequentialLearning

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

noncomputable section

variable {Omega S : Type*} {mOmega : MeasurableSpace Omega}
  [PseudoMetricSpace S] [MeasurableSpace S] [Nonempty S]
  [OpensMeasurableSpace S] [TopologicalSpace.SeparableSpace S]

/-- The isolated `Wasserstein2LawMeasurable` input holds on the canonical Polish completion. -/
theorem wasserstein2LawMeasurable_pseudometricCompletion :
    Wasserstein2LawMeasurable (PseudometricCompletion S) :=
  wasserstein2LawMeasurable_of_polish

/-- Closed measurability statement for posterior displacement. -/
theorem measurable_posteriorDisplacementENN_closed
    {m : MeasurableSpace Omega}
    (rho : Kernel[m, (inferInstance : MeasurableSpace (S × S))] Omega (S × S))
    [IsMarkovKernel rho] :
    Measurable[m] (posteriorDisplacementENN rho) :=
  measurable_posteriorDisplacementENN rho
    wasserstein2LawMeasurable_pseudometricCompletion

/-- Closed square-integrability conclusion in Result 16(iii). -/
theorem posteriorDisplacement_memLp_two_closed
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (m : MeasurableSpace Omega) (hm : m ≤ mOmega)
    (X Y : Omega → S) (hX : Measurable[mOmega] X)
    (hY : Measurable[mOmega] Y)
    (rho : Kernel[m, (inferInstance : MeasurableSpace (S × S))]
      Omega (S × S)) [IsMarkovKernel rho]
    (hrho : IsRegularConditionalLaw mu m hm
      (fun omega ↦ (X omega, Y omega)) rho)
    (hMoment : Integrable (fun omega ↦ dist (X omega) (Y omega) ^ 2) mu) :
    MemLp (posteriorDisplacement rho) 2 mu :=
  posteriorDisplacement_memLp_two mu m hm X Y hX hY rho hrho
    wasserstein2LawMeasurable_pseudometricCompletion hMoment

/-- Closed unconditional squared-displacement inequality in Result 16(iii). -/
theorem integral_posteriorDisplacement_sq_le_closed
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (m : MeasurableSpace Omega) (hm : m ≤ mOmega)
    (X Y : Omega → S) (hX : Measurable[mOmega] X)
    (hY : Measurable[mOmega] Y)
    (rho : Kernel[m, (inferInstance : MeasurableSpace (S × S))]
      Omega (S × S)) [IsMarkovKernel rho]
    (hrho : IsRegularConditionalLaw mu m hm
      (fun omega ↦ (X omega, Y omega)) rho)
    (hMoment : Integrable (fun omega ↦ dist (X omega) (Y omega) ^ 2) mu) :
    ∫ omega, posteriorDisplacement rho omega ^ 2 ∂mu ≤
      ∫ omega, dist (X omega) (Y omega) ^ 2 ∂mu :=
  integral_posteriorDisplacement_sq_le mu m hm X Y hX hY rho hrho
    wasserstein2LawMeasurable_pseudometricCompletion hMoment

/-- Result 17 with no auxiliary `hW` premise. -/
theorem frechet_posterior_displacement_bound_closed
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (mSmall mLarge : MeasurableSpace Omega)
    (hmLarge : mLarge ≤ mOmega)
    (X Y : Omega → S) (hX : Measurable[mOmega] X)
    (hY : Measurable[mOmega] Y)
    (rho : Kernel[mLarge,
      (inferInstance : MeasurableSpace (S × S))] Omega (S × S))
    [IsMarkovKernel rho]
    (hrho : IsRegularConditionalLaw mu mLarge hmLarge
      (fun omega ↦ (X omega, Y omega)) rho)
    (s0 : S)
    (hXMoment : Integrable (fun omega ↦ dist (X omega) s0 ^ 2) mu)
    (hYMoment : Integrable (fun omega ↦ dist (Y omega) s0 ^ 2) mu) :
    let U : Omega → ℝ := fun omega ↦
      (frechetVariance ((Kernel.fst rho) omega)).toReal
    let V : Omega → ℝ := fun omega ↦
      (frechetVariance ((Kernel.snd rho) omega)).toReal
    let Delta : Omega → ℝ := posteriorDisplacement rho
    (∀ᵐ omega ∂mu,
      |Real.sqrt (V omega) - Real.sqrt (U omega)| ≤ Delta omega) ∧
    (∀ᵐ omega ∂mu,
      V omega - U omega ≤
        Delta omega * (Delta omega + 2 * Real.sqrt (U omega))) ∧
    (displacementMovementTerm mu mSmall U V ≤ᵐ[mu]
      mu[(fun omega ↦
        Delta omega ^ 2 + 2 * Delta omega * Real.sqrt (U omega)) |
          mSmall]) :=
  frechet_posterior_displacement_bound mu mSmall mLarge hmLarge X Y hX hY rho hrho
    s0 hXMoment hYMoment wasserstein2LawMeasurable_pseudometricCompletion

/-- The predictable displacement envelope with no auxiliary `hW` premise. -/
theorem frechet_predictable_displacement_envelope_closed
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
      (fun omega ↦ (KOld omega, KNew omega)) rho)
    (s0 t0 : S)
    (hMomentOld : Integrable (fun omega ↦ dist (KOld omega) s0 ^ 2) mu)
    (hMomentNew : Integrable (fun omega ↦ dist (KNew omega) t0 ^ 2) mu) :
    StronglyMeasurable[mSmall]
        (predictableDisplacementRMS mu mSmall (posteriorDisplacement rho)) ∧
    MemLp (posteriorDisplacement rho) 2 mu ∧
    ((fun omega ↦
        mu[refinedOldPosteriorFrechetVariance mLarge (Kernel.fst rho) |
          mSmall] omega) =
      fun omega ↦
        currentPosteriorFrechetVariance mSmall kappaOldSmall omega -
          frechetInformationGain mu mSmall mLarge
            kappaOldSmall (Kernel.fst rho) omega) ∧
    (mu[refinedNewPosteriorFrechetVariance mLarge (Kernel.snd rho) |
        mSmall] ≤ᵐ[mu]
      fun omega ↦
        (Real.sqrt
            (mu[refinedOldPosteriorFrechetVariance mLarge (Kernel.fst rho) |
              mSmall] omega) +
          predictableDisplacementRMS mu mSmall
            (posteriorDisplacement rho) omega) ^ 2) ∧
    (mu[refinedNewPosteriorFrechetVariance mLarge (Kernel.snd rho) |
        mSmall] ≤ᵐ[mu]
      fun omega ↦
        (Real.sqrt
            (currentPosteriorFrechetVariance mSmall kappaOldSmall omega -
              frechetInformationGain mu mSmall mLarge
                kappaOldSmall (Kernel.fst rho) omega) +
          predictableDisplacementRMS mu mSmall
            (posteriorDisplacement rho) omega) ^ 2) :=
  frechet_predictable_displacement_envelope mu mSmall mLarge hSmallLarge hLargeAmbient
    KOld KNew hKOld hKNew kappaOldSmall hkappaOldSmall rho hrho s0 t0 hMomentOld hMomentNew
    wasserstein2LawMeasurable_pseudometricCompletion

/-- The full Fréchet/RCD break-even criterion with no auxiliary `hW` premise. -/
theorem frechet_break_even_criterion_closed
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
      (fun omega ↦ (KOld omega, KNew omega)) rho)
    (s0 t0 : S)
    (hMomentOld : Integrable (fun omega ↦ dist (KOld omega) s0 ^ 2) mu)
    (hMomentNew : Integrable (fun omega ↦ dist (KNew omega) t0 ^ 2) mu) :
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
        currentPosteriorFrechetVariance mSmall kappaOldSmall) :=
  frechet_break_even_criterion mu mSmall mLarge hSmallLarge hLargeAmbient
    KOld KNew hKOld hKNew kappaOldSmall hkappaOldSmall rho hrho s0 t0 hMomentOld hMomentNew
    wasserstein2LawMeasurable_pseudometricCompletion

end

end SequentialLearning
