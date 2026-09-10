import SequentialLearning.PredictableDisplacementEnvelope
import Mathlib.Tactic.Ring

/-!
# Break-even criterion

This file formalises the corollary obtained by forcing the predictable
displacement envelope below the current posterior variance.
-/

namespace SequentialLearning

open Filter MeasureTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

noncomputable section

section BreakEvenCriterion

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- The predictable displacement threshold
`sqrt(V) - sqrt(V - J)`. -/
def breakEvenThreshold (V J : Ω → ℝ) : Ω → ℝ :=
  fun ω => Real.sqrt (V ω) - Real.sqrt (V ω - J ω)

/-- The break-even threshold is measurable whenever `V` and `J` are
measurable at the current information state. -/
theorem stronglyMeasurable_breakEvenThreshold
    (m : MeasurableSpace Ω) (V J : Ω → ℝ)
    (hV : StronglyMeasurable[m] V)
    (hJ : StronglyMeasurable[m] J) :
    StronglyMeasurable[m] (breakEvenThreshold V J) := by
  exact
    (Real.continuous_sqrt.comp_stronglyMeasurable hV).sub
      (Real.continuous_sqrt.comp_stronglyMeasurable (hV.sub hJ))

/-- The displayed threshold is the exact break-even point for the envelope
itself. This equivalence does not say that the envelope is equal to the true
future risk. -/
theorem envelope_below_current_iff
    (oldPredictableRisk currentRisk displacement : ℝ)
    (_hOldNonnegative : 0 ≤ oldPredictableRisk)
    (hCurrentNonnegative : 0 ≤ currentRisk)
    (hDisplacementNonnegative : 0 ≤ displacement) :
    (Real.sqrt oldPredictableRisk + displacement) ^ 2 ≤ currentRisk ↔
      displacement ≤
        Real.sqrt currentRisk - Real.sqrt oldPredictableRisk := by
  have hRootSumNonnegative :
      0 ≤ Real.sqrt oldPredictableRisk + displacement :=
    add_nonneg (Real.sqrt_nonneg _) hDisplacementNonnegative
  constructor
  · intro hEnvelope
    have hRoot :
        Real.sqrt oldPredictableRisk + displacement ≤
          Real.sqrt currentRisk :=
      (Real.le_sqrt hRootSumNonnegative hCurrentNonnegative).mpr hEnvelope
    linarith
  · intro hThreshold
    have hRoot :
        Real.sqrt oldPredictableRisk + displacement ≤
          Real.sqrt currentRisk := by
      linarith
    have hSquare :
        (Real.sqrt oldPredictableRisk + displacement) ^ 2 ≤
          Real.sqrt currentRisk ^ 2 :=
      (sq_le_sq₀ hRootSumNonnegative (Real.sqrt_nonneg _)).mpr hRoot
    simpa only [Real.sq_sqrt hCurrentNonnegative] using hSquare

/-- Algebraic core of the break-even argument. If a non-negative predictable
envelope is no larger than the current root risk, then the future expected
risk is no larger than the current risk. -/
theorem break_even_of_envelope
    (μ : Measure[m0] Ω)
    (expectedNewRisk oldPredictableRisk currentRisk displacement : Ω → ℝ)
    (hOldNonnegative : 0 ≤ᵐ[μ] oldPredictableRisk)
    (hCurrentNonnegative : 0 ≤ᵐ[μ] currentRisk)
    (hDisplacementNonnegative : 0 ≤ᵐ[μ] displacement)
    (hEnvelope : expectedNewRisk ≤ᵐ[μ]
      fun ω =>
        (Real.sqrt (oldPredictableRisk ω) + displacement ω) ^ 2)
    (hBreakEven : displacement ≤ᵐ[μ]
      fun ω =>
        Real.sqrt (currentRisk ω) -
          Real.sqrt (oldPredictableRisk ω)) :
    expectedNewRisk ≤ᵐ[μ] currentRisk := by
  filter_upwards [hOldNonnegative, hCurrentNonnegative,
      hDisplacementNonnegative, hEnvelope, hBreakEven] with
    ω hOldω hCurrentω hDisplacementω hEnvelopeω hBreakEvenω
  have hRootSum :
      Real.sqrt (oldPredictableRisk ω) + displacement ω ≤
        Real.sqrt (currentRisk ω) := by
    linarith
  have hRootSumNonnegative :
      0 ≤ Real.sqrt (oldPredictableRisk ω) + displacement ω :=
    add_nonneg (Real.sqrt_nonneg _) hDisplacementω
  have hSquared :
      (Real.sqrt (oldPredictableRisk ω) + displacement ω) ^ 2 ≤
        Real.sqrt (currentRisk ω) ^ 2 :=
    (sq_le_sq₀ hRootSumNonnegative (Real.sqrt_nonneg _)).mpr hRootSum
  calc
    expectedNewRisk ω ≤
        (Real.sqrt (oldPredictableRisk ω) + displacement ω) ^ 2 :=
      hEnvelopeω
    _ ≤ Real.sqrt (currentRisk ω) ^ 2 := hSquared
    _ = currentRisk ω := Real.sq_sqrt hCurrentω

/-- Hilbert posterior-variance form of the manuscript's break-even
corollary. In addition to the implication, the theorem verifies that both
sides of its hypothesis are measurable and that
`0 ≤ J ≤ V`, making the threshold a non-negative real quantity. -/
theorem break_even_criterion_for_posteriorVariances
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (mSmall mLarge : MeasurableSpace Ω)
    (hSmallLarge : mSmall ≤ mLarge) (hLargeAmbient : mLarge ≤ m0)
    (KOld KNew : Ω → H)
    (hKOld : MemLp KOld 2 μ) (hKNew : MemLp KNew 2 μ)
    (Δ : Ω → ℝ)
    (hRoot : ∀ᵐ ω ∂μ,
      |Real.sqrt (posteriorVariance μ mLarge KNew ω) -
          Real.sqrt (posteriorVariance μ mLarge KOld ω)| ≤ Δ ω)
    (hDelta : MemLp Δ 2 μ) :
    StronglyMeasurable[mSmall]
        (predictableDisplacementRMS μ mSmall Δ) ∧
    StronglyMeasurable[mSmall]
        (breakEvenThreshold
          (posteriorVariance μ mSmall KOld)
          (hilbertInformationTerm μ mSmall mLarge KOld)) ∧
    (0 ≤ᵐ[μ] hilbertInformationTerm μ mSmall mLarge KOld) ∧
    (hilbertInformationTerm μ mSmall mLarge KOld ≤ᵐ[μ]
      posteriorVariance μ mSmall KOld) ∧
    (0 ≤ᵐ[μ]
      breakEvenThreshold
        (posteriorVariance μ mSmall KOld)
        (hilbertInformationTerm μ mSmall mLarge KOld)) ∧
    ((predictableDisplacementRMS μ mSmall Δ ≤ᵐ[μ]
        breakEvenThreshold
          (posteriorVariance μ mSmall KOld)
          (hilbertInformationTerm μ mSmall mLarge KOld)) →
      μ[posteriorVariance μ mLarge KNew | mSmall] ≤ᵐ[μ]
        posteriorVariance μ mSmall KOld) := by
  let VCurrent : Ω → ℝ := posteriorVariance μ mSmall KOld
  let J : Ω → ℝ := hilbertInformationTerm μ mSmall mLarge KOld
  let A : Ω → ℝ := fun ω => VCurrent ω - J ω
  let D : Ω → ℝ := predictableDisplacementRMS μ mSmall Δ
  have hEnvelopeResult :=
    predictable_displacement_envelope_for_posteriorVariances
      μ mSmall mLarge KOld KNew Δ hRoot hDelta
  have hAIdentity := hEnvelopeResult.2.1
  have hEnvelope :
      μ[posteriorVariance μ mLarge KNew | mSmall] ≤ᵐ[μ]
        fun ω => (Real.sqrt (A ω) + D ω) ^ 2 := by
    simpa only [A, VCurrent, J, D] using hEnvelopeResult.2.2.2
  have hVCurrentNonnegative : 0 ≤ᵐ[μ] VCurrent := by
    simpa only [VCurrent, posteriorVariance] using
      posteriorMSE_nonnegative μ mSmall KOld KOld
  have hOldLargeNonnegative :
      0 ≤ᵐ[μ] posteriorVariance μ mLarge KOld := by
    exact posteriorMSE_nonnegative μ mLarge KOld KOld
  have hOldPredictableNonnegative :
      0 ≤ᵐ[μ] μ[posteriorVariance μ mLarge KOld | mSmall] :=
    condExp_nonneg hOldLargeNonnegative
  have hANonnegative : 0 ≤ᵐ[μ] A := by
    filter_upwards [hOldPredictableNonnegative] with ω hOldω
    change 0 ≤ VCurrent ω - J ω
    rw [← congr_fun hAIdentity ω]
    exact hOldω
  have hDNonnegative : 0 ≤ᵐ[μ] D := by
    filter_upwards with ω
    exact Real.sqrt_nonneg _
  have hHilbertCriterion := hilbert_one_step_learning_criterion μ
    mSmall mLarge hSmallLarge hLargeAmbient KOld KNew hKOld hKNew
  have hInnovationNonnegative :
      0 ≤ᵐ[μ]
        μ[(fun ω =>
          ‖oldTargetInnovation μ mSmall mLarge KOld ω‖ ^ 2) | mSmall] := by
    apply condExp_nonneg
    filter_upwards with ω
    exact sq_nonneg _
  have hJNonnegative : 0 ≤ᵐ[μ] J := by
    filter_upwards [hHilbertCriterion.1, hInnovationNonnegative] with
      ω hJω hInnovationω
    change 0 ≤ hilbertInformationTerm μ mSmall mLarge KOld ω
    rw [hJω]
    exact hInnovationω
  have hJLeV : J ≤ᵐ[μ] VCurrent := by
    filter_upwards [hANonnegative] with ω hAω
    change 0 ≤ VCurrent ω - J ω at hAω
    linarith
  have hThresholdNonnegative :
      0 ≤ᵐ[μ] breakEvenThreshold VCurrent J := by
    filter_upwards [hJNonnegative] with ω hJω
    simp only [Pi.zero_apply] at hJω
    dsimp only [breakEvenThreshold]
    exact sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
  have hVCurrentMeasurable : StronglyMeasurable[mSmall] VCurrent := by
    dsimp only [VCurrent, posteriorVariance, posteriorMSE]
    exact stronglyMeasurable_condExp
  have hJMeasurable : StronglyMeasurable[mSmall] J := by
    change StronglyMeasurable[mSmall]
      (fun ω =>
        posteriorVariance μ mSmall KOld ω -
          μ[posteriorVariance μ mLarge KOld | mSmall] ω)
    exact hVCurrentMeasurable.sub stronglyMeasurable_condExp
  have hThresholdMeasurable :
      StronglyMeasurable[mSmall] (breakEvenThreshold VCurrent J) :=
    stronglyMeasurable_breakEvenThreshold mSmall VCurrent J
      hVCurrentMeasurable hJMeasurable
  have hImplication :
      (D ≤ᵐ[μ] breakEvenThreshold VCurrent J) →
        μ[posteriorVariance μ mLarge KNew | mSmall] ≤ᵐ[μ] VCurrent := by
    intro hBreakEven
    have hBreakEvenA : D ≤ᵐ[μ]
        fun ω => Real.sqrt (VCurrent ω) - Real.sqrt (A ω) := by
      change D ≤ᵐ[μ]
        (fun ω =>
          Real.sqrt (VCurrent ω) - Real.sqrt (VCurrent ω - J ω))
        at hBreakEven
      simpa only [A] using hBreakEven
    exact break_even_of_envelope μ
      (μ[posteriorVariance μ mLarge KNew | mSmall]) A VCurrent D
      hANonnegative hVCurrentNonnegative hDNonnegative hEnvelope hBreakEvenA
  simpa only [VCurrent, J, D] using
    ⟨hEnvelopeResult.1, hThresholdMeasurable, hJNonnegative, hJLeV,
      hThresholdNonnegative, hImplication⟩

end BreakEvenCriterion

end

end SequentialLearning
