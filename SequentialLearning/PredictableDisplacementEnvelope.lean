import SequentialLearning.PosteriorDisplacementBound
import SequentialLearning.DiscrepancyWeighting
import Mathlib.Tactic.Ring

/-!
# Predictable displacement envelope

This file formalises the manuscript's predictable displacement envelope.  It
first derives the non-negative square-root form of conditional
Cauchy--Schwarz, then combines it with the posterior displacement bound.
-/

namespace SequentialLearning

open Filter MeasureTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

noncomputable section

section PredictableDisplacementEnvelope

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- The predictable root-mean-square displacement
`(E[Δ² | m])^(1/2)`. -/
def predictableDisplacementRMS (μ : Measure[m0] Ω)
    (m : MeasurableSpace Ω) (Δ : Ω → ℝ) : Ω → ℝ :=
  fun ω => Real.sqrt (μ[(fun a => Δ a ^ 2) | m] ω)

/-- The predictable displacement is measurable at the smaller information
state. -/
theorem stronglyMeasurable_predictableDisplacementRMS
    (μ : Measure[m0] Ω) (m : MeasurableSpace Ω) (Δ : Ω → ℝ) :
    StronglyMeasurable[m] (predictableDisplacementRMS μ m Δ) := by
  exact Real.continuous_sqrt.comp_stronglyMeasurable stronglyMeasurable_condExp

/-- Conditional Cauchy--Schwarz in the unsquared form appropriate for two
almost-surely non-negative real random variables. -/
theorem conditional_cauchy_schwarz_nonnegative
    (μ : Measure[m0] Ω) (m : MeasurableSpace Ω) (X Y : Ω → ℝ)
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hXNonnegative : 0 ≤ᵐ[μ] X) (hYNonnegative : 0 ≤ᵐ[μ] Y) :
    μ[(fun a => X a * Y a) | m] ≤ᵐ[μ]
      fun ω =>
        Real.sqrt (μ[(fun a => X a ^ 2) | m] ω) *
          Real.sqrt (μ[(fun a => Y a ^ 2) | m] ω) := by
  have hProductNonnegative :
      0 ≤ᵐ[μ] μ[(fun a => X a * Y a) | m] := by
    apply condExp_nonneg
    filter_upwards [hXNonnegative, hYNonnegative] with ω hXω hYω
    exact mul_nonneg hXω hYω
  have hXSquareNonnegative :
      0 ≤ᵐ[μ] μ[(fun a => X a ^ 2) | m] := by
    apply condExp_nonneg
    filter_upwards with ω
    exact sq_nonneg (X ω)
  have hCS := conditional_cauchy_schwarz_real μ m X Y hX hY
  filter_upwards [hProductNonnegative, hXSquareNonnegative, hCS] with
    ω hProductω hXSquareω hCSω
  calc
    μ[(fun a => X a * Y a) | m] ω ≤
        Real.sqrt
          (μ[(fun a => X a ^ 2) | m] ω *
            μ[(fun a => Y a ^ 2) | m] ω) :=
      Real.le_sqrt_of_sq_le hCSω
    _ = Real.sqrt (μ[(fun a => X a ^ 2) | m] ω) *
          Real.sqrt (μ[(fun a => Y a ^ 2) | m] ω) := by
      rw [Real.sqrt_mul hXSquareω]

/-- The predictable displacement envelope in scalar conditional-risk form.
The root-risk estimate is the metric/RCD input from the posterior displacement
lemma; `Δ ∈ L²` supplies all integrability needed for the conditional
Cauchy--Schwarz step. -/
theorem predictable_displacement_envelope
    (μ : Measure[m0] Ω)
    (mSmall : MeasurableSpace Ω)
    (U V Δ : Ω → ℝ)
    (hU : 0 ≤ᵐ[μ] U) (hV : 0 ≤ᵐ[μ] V)
    (hRoot : ∀ᵐ ω ∂μ,
      |Real.sqrt (V ω) - Real.sqrt (U ω)| ≤ Δ ω)
    (hUInt : Integrable U μ) (hVInt : Integrable V μ)
    (hDelta : MemLp Δ 2 μ) :
    μ[V | mSmall] ≤ᵐ[μ]
      fun ω =>
        (Real.sqrt (μ[U | mSmall] ω) +
          predictableDisplacementRMS μ mSmall Δ ω) ^ 2 := by
  let R : Ω → ℝ := fun ω => Real.sqrt (U ω)
  let Q : Ω → ℝ := fun ω => Δ ω * R ω
  let D2 : Ω → ℝ := fun ω => Δ ω ^ 2
  have hRootU : MemLp R 2 μ := by
    exact memLp_two_sqrt_of_nonnegative_integrable μ U hU hUInt
  have hDeltaNonnegative : 0 ≤ᵐ[μ] Δ := by
    filter_upwards [hRoot] with ω hRootω
    exact (abs_nonneg _).trans hRootω
  have hRNonnegative : 0 ≤ᵐ[μ] R := by
    filter_upwards with ω
    exact Real.sqrt_nonneg (U ω)
  have hD2Int : Integrable D2 μ := by
    simpa only [D2] using hDelta.integrable_sq
  have hQInt : Integrable Q μ := by
    exact hDelta.integrable_mul hRootU
  have hBoundInt : Integrable
      (fun ω => Δ ω ^ 2 + 2 * Δ ω * Real.sqrt (U ω)) μ :=
    integrable_displacement_bound_of_memLp_two μ U Δ hDelta hRootU
  have hDisplacement := posterior_displacement_bound μ mSmall U V Δ
    hU hV hRoot hUInt hVInt hBoundInt
  have hCS := conditional_cauchy_schwarz_nonnegative μ mSmall Δ R
    hDelta hRootU hDeltaNonnegative hRNonnegative
  have hRSquare : (fun ω => R ω ^ 2) =ᵐ[μ] U := by
    filter_upwards [hU] with ω hUω
    exact Real.sq_sqrt hUω
  have hRSquareConditional :
      μ[(fun ω => R ω ^ 2) | mSmall] =ᵐ[μ] μ[U | mSmall] :=
    condExp_congr_ae hRSquare
  have hCrossBound :
      μ[Q | mSmall] ≤ᵐ[μ]
        fun ω =>
          Real.sqrt (μ[D2 | mSmall] ω) *
            Real.sqrt (μ[U | mSmall] ω) := by
    filter_upwards [hCS, hRSquareConditional] with ω hCSω hSquareω
    simpa only [Q, D2, R, hSquareω] using hCSω
  have hDifferenceLinear :
      μ[(fun ω => V ω - U ω) | mSmall] =ᵐ[μ]
        fun ω => μ[V | mSmall] ω - μ[U | mSmall] ω :=
    condExp_sub hVInt hUInt mSmall
  have hIntegrandForm :
      (fun ω => Δ ω ^ 2 + 2 * Δ ω * Real.sqrt (U ω)) =
        D2 + (2 : ℝ) • Q := by
    funext ω
    simp only [D2, Q, R, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hBoundLinear :
      μ[(fun ω => Δ ω ^ 2 + 2 * Δ ω * Real.sqrt (U ω)) | mSmall]
        =ᵐ[μ]
      fun ω => μ[D2 | mSmall] ω + 2 * μ[Q | mSmall] ω := by
    rw [hIntegrandForm]
    have hAdd := condExp_add hD2Int (hQInt.smul (2 : ℝ)) mSmall
    have hScale := condExp_smul (μ := μ) (2 : ℝ) Q mSmall
    filter_upwards [hAdd, hScale] with ω hAddω hScaleω
    rw [hAddω]
    simp only [Pi.add_apply]
    rw [hScaleω]
    simp only [Pi.smul_apply, smul_eq_mul]
  have hOldRiskNonnegative : 0 ≤ᵐ[μ] μ[U | mSmall] :=
    condExp_nonneg hU
  have hD2Nonnegative : 0 ≤ᵐ[μ] μ[D2 | mSmall] := by
    apply condExp_nonneg
    filter_upwards with ω
    exact sq_nonneg (Δ ω)
  filter_upwards [hDisplacement.2.2, hDifferenceLinear, hBoundLinear,
      hCrossBound, hOldRiskNonnegative, hD2Nonnegative] with
    ω hDispω hDiffω hBoundω hCrossω hOldω hD2ω
  dsimp only [displacementMovementTerm] at hDispω
  rw [hDiffω, hBoundω] at hDispω
  change μ[V | mSmall] ω ≤
    (Real.sqrt (μ[U | mSmall] ω) +
      Real.sqrt (μ[D2 | mSmall] ω)) ^ 2
  have hOldSqrtSquare :
      Real.sqrt (μ[U | mSmall] ω) ^ 2 = μ[U | mSmall] ω :=
    Real.sq_sqrt hOldω
  have hD2SqrtSquare :
      Real.sqrt (μ[D2 | mSmall] ω) ^ 2 = μ[D2 | mSmall] ω :=
    Real.sq_sqrt hD2ω
  nlinarith

/-- Posterior-variance specialisation, including the manuscript identity
`Aₙ = Vₙ - Jₙ⁽ᵈ⁾` and both equivalent forms of the envelope. -/
theorem predictable_displacement_envelope_for_posteriorVariances
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (μ : Measure[m0] Ω)
    (mSmall mLarge : MeasurableSpace Ω)
    (KOld KNew : Ω → H) (Δ : Ω → ℝ)
    (hRoot : ∀ᵐ ω ∂μ,
      |Real.sqrt (posteriorVariance μ mLarge KNew ω) -
          Real.sqrt (posteriorVariance μ mLarge KOld ω)| ≤ Δ ω)
    (hDelta : MemLp Δ 2 μ) :
    StronglyMeasurable[mSmall]
        (predictableDisplacementRMS μ mSmall Δ) ∧
    ((fun ω =>
        μ[posteriorVariance μ mLarge KOld | mSmall] ω) =
      fun ω =>
        posteriorVariance μ mSmall KOld ω -
          hilbertInformationTerm μ mSmall mLarge KOld ω) ∧
    (μ[posteriorVariance μ mLarge KNew | mSmall] ≤ᵐ[μ]
      fun ω =>
        (Real.sqrt
            (μ[posteriorVariance μ mLarge KOld | mSmall] ω) +
          predictableDisplacementRMS μ mSmall Δ ω) ^ 2) ∧
    (μ[posteriorVariance μ mLarge KNew | mSmall] ≤ᵐ[μ]
      fun ω =>
        (Real.sqrt
            (posteriorVariance μ mSmall KOld ω -
              hilbertInformationTerm μ mSmall mLarge KOld ω) +
          predictableDisplacementRMS μ mSmall Δ ω) ^ 2) := by
  have hOldNonnegative :
      0 ≤ᵐ[μ] posteriorVariance μ mLarge KOld :=
    posteriorMSE_nonnegative μ mLarge KOld KOld
  have hNewNonnegative :
      0 ≤ᵐ[μ] posteriorVariance μ mLarge KNew :=
    posteriorMSE_nonnegative μ mLarge KNew KNew
  have hEnvelope := predictable_displacement_envelope μ mSmall
    (posteriorVariance μ mLarge KOld)
    (posteriorVariance μ mLarge KNew) Δ
    hOldNonnegative hNewNonnegative hRoot
    integrable_condExp integrable_condExp hDelta
  have hAIdentity :
      (fun ω =>
          μ[posteriorVariance μ mLarge KOld | mSmall] ω) =
        fun ω =>
          posteriorVariance μ mSmall KOld ω -
            hilbertInformationTerm μ mSmall mLarge KOld ω := by
    funext ω
    dsimp only [hilbertInformationTerm, informationGain]
    ring
  have hEnvelopeInformation :
      μ[posteriorVariance μ mLarge KNew | mSmall] ≤ᵐ[μ]
        fun ω =>
          (Real.sqrt
              (posteriorVariance μ mSmall KOld ω -
                hilbertInformationTerm μ mSmall mLarge KOld ω) +
            predictableDisplacementRMS μ mSmall Δ ω) ^ 2 := by
    filter_upwards [hEnvelope] with ω hEnvelopeω
    rw [← congr_fun hAIdentity ω]
    exact hEnvelopeω
  exact ⟨stronglyMeasurable_predictableDisplacementRMS μ mSmall Δ,
    hAIdentity, hEnvelope, hEnvelopeInformation⟩

end PredictableDisplacementEnvelope

end

end SequentialLearning
