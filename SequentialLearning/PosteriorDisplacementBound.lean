import SequentialLearning.HilbertLearningCriterion
import Mathlib.Tactic.Ring

/-!
# Posterior displacement bound

This file formalises Proposition `dispbound` from the manuscript once the
posterior-displacement estimate supplied by Lemma `displacement` and Lemma
`psilip` is available. The proof separates the metric/RCD input (the root-risk
bound) from its deterministic squaring and conditional-expectation
consequences.
-/

namespace SequentialLearning

open Filter MeasureTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

noncomputable section

section PosteriorDisplacementBound

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- The stage-`n` movement term written as the conditional expectation of the
larger-information posterior-variance difference. -/
def displacementMovementTerm (μ : Measure[m0] Ω)
    (mSmall : MeasurableSpace Ω) (U V : Ω → ℝ) : Ω → ℝ :=
  μ[(fun ω => V ω - U ω) | mSmall]

/-- Version-management step for the metric input. If the square roots of the
two posterior variances agree almost surely with a posterior spread functional
`ψ`, and `ψ` is Lipschitz along the two posterior laws with displacement `Δ`,
then the root-risk estimate used by the proposition follows. The type `M`
stands for the space of posterior probability measures (for the manuscript,
`𝒫₂(Ŝ)`). -/
theorem posterior_root_bound_from_measure_lipschitz
    {M : Type*}
    (μ : Measure[m0] Ω)
    (oldPosterior newPosterior : Ω → M)
    (ψ : M → ℝ) (U V Δ : Ω → ℝ)
    (hOldVersion : ∀ᵐ ω ∂μ,
      Real.sqrt (U ω) = ψ (oldPosterior ω))
    (hNewVersion : ∀ᵐ ω ∂μ,
      Real.sqrt (V ω) = ψ (newPosterior ω))
    (hLipschitz : ∀ᵐ ω ∂μ,
      |ψ (newPosterior ω) - ψ (oldPosterior ω)| ≤ Δ ω) :
    ∀ᵐ ω ∂μ,
      |Real.sqrt (V ω) - Real.sqrt (U ω)| ≤ Δ ω := by
  filter_upwards [hOldVersion, hNewVersion, hLipschitz] with
    ω hOldω hNewω hLipω
  rw [hOldω, hNewω]
  exact hLipω

/-- Squaring a bound on the difference of posterior standard deviations gives
the manuscript's one-step posterior-variance displacement bound. -/
theorem variance_difference_bound_of_sqrt_bound
    {U V Δ : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hRoot : |Real.sqrt V - Real.sqrt U| ≤ Δ) :
    V - U ≤ Δ * (Δ + 2 * Real.sqrt U) := by
  have hΔ : 0 ≤ Δ := (abs_nonneg _).trans hRoot
  have hRootUpper : Real.sqrt V - Real.sqrt U ≤ Δ :=
    (le_abs_self (Real.sqrt V - Real.sqrt U)).trans hRoot
  have hSqrtLe : Real.sqrt V ≤ Real.sqrt U + Δ := by
    have h := sub_le_iff_le_add.mp hRootUpper
    simpa only [add_comm] using h
  have hLeftNonnegative : 0 ≤ Real.sqrt V := Real.sqrt_nonneg V
  have hRightNonnegative : 0 ≤ Real.sqrt U + Δ :=
    add_nonneg (Real.sqrt_nonneg U) hΔ
  have hSquareLe :
      Real.sqrt V * Real.sqrt V ≤
        (Real.sqrt U + Δ) * (Real.sqrt U + Δ) := by
    calc
      Real.sqrt V * Real.sqrt V ≤
          Real.sqrt V * (Real.sqrt U + Δ) :=
        mul_le_mul_of_nonneg_left hSqrtLe hLeftNonnegative
      _ ≤ (Real.sqrt U + Δ) * (Real.sqrt U + Δ) :=
        mul_le_mul_of_nonneg_right hSqrtLe hRightNonnegative
  have hVarianceLe : V ≤ (Real.sqrt U + Δ) ^ 2 := by
    calc
      V = Real.sqrt V * Real.sqrt V := (Real.mul_self_sqrt hV).symm
      _ ≤ (Real.sqrt U + Δ) * (Real.sqrt U + Δ) := hSquareLe
      _ = (Real.sqrt U + Δ) ^ 2 := by rw [pow_two]
  calc
    V - U ≤ (Real.sqrt U + Δ) ^ 2 - U :=
      sub_le_sub_right hVarianceLe U
    _ = Δ * (Δ + 2 * Real.sqrt U) := by
      rw [add_sq, Real.sq_sqrt hU]
      ring

/-- The right-hand side of the displacement bound is integrable when both the
displacement and the old posterior standard deviation are in `L²`. -/
theorem integrable_displacement_bound_of_memLp_two
    (μ : Measure[m0] Ω) (U Δ : Ω → ℝ)
    (hΔ : MemLp Δ 2 μ)
    (hRootU : MemLp (fun ω => Real.sqrt (U ω)) 2 μ) :
    Integrable
      (fun ω => Δ ω ^ 2 + 2 * Δ ω * Real.sqrt (U ω)) μ := by
  have hDeltaSquare : Integrable (fun ω => Δ ω * Δ ω) μ :=
    hΔ.integrable_mul hΔ
  have hCross : Integrable (fun ω => Δ ω * Real.sqrt (U ω)) μ :=
    hΔ.integrable_mul hRootU
  have hCrossTwice :
      Integrable (fun ω => 2 * (Δ ω * Real.sqrt (U ω))) μ :=
    hCross.const_mul 2
  have hSum := hDeltaSquare.add hCrossTwice
  apply hSum.congr
  exact Filter.Eventually.of_forall (fun ω => by
    simp only [Pi.add_apply, pow_two, mul_assoc])

/-- A non-negative integrable random variable has an `L²` square root. This
is the step that turns integrability of a posterior variance into the
integrability needed for the cross term in the displacement bound. -/
theorem memLp_two_sqrt_of_nonnegative_integrable
    (μ : Measure[m0] Ω) (U : Ω → ℝ)
    (hU : 0 ≤ᵐ[μ] U) (hUInt : Integrable U μ) :
    MemLp (fun ω => Real.sqrt (U ω)) 2 μ := by
  have hSqrtMeas :
      AEStronglyMeasurable (fun ω => Real.sqrt (U ω)) μ := by
    simpa only [Function.comp_apply] using
      Real.continuous_sqrt.comp_aestronglyMeasurable
        hUInt.aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hSqrtMeas]
  apply hUInt.congr
  filter_upwards [hU] with ω hUω
  exact (Real.sq_sqrt hUω).symm

/-- Conditional version of the posterior displacement bound. The first
hypothesis is precisely the output supplied by the metric/RCD displacement
lemma; the remainder of the proposition follows from deterministic squaring
and monotonicity of conditional expectation. -/
theorem posterior_displacement_bound
    (μ : Measure[m0] Ω)
    (mSmall : MeasurableSpace Ω)
    (U V Δ : Ω → ℝ)
    (hU : 0 ≤ᵐ[μ] U) (hV : 0 ≤ᵐ[μ] V)
    (hRoot : ∀ᵐ ω ∂μ,
      |Real.sqrt (V ω) - Real.sqrt (U ω)| ≤ Δ ω)
    (hUInt : Integrable U μ) (hVInt : Integrable V μ)
    (hBoundInt : Integrable
      (fun ω => Δ ω ^ 2 + 2 * Δ ω * Real.sqrt (U ω)) μ) :
    (∀ᵐ ω ∂μ,
      |Real.sqrt (V ω) - Real.sqrt (U ω)| ≤ Δ ω) ∧
    (∀ᵐ ω ∂μ,
      V ω - U ω ≤
        Δ ω * (Δ ω + 2 * Real.sqrt (U ω))) ∧
    (displacementMovementTerm μ mSmall U V ≤ᵐ[μ]
      μ[(fun ω =>
        Δ ω ^ 2 + 2 * Δ ω * Real.sqrt (U ω)) | mSmall]) := by
  have hPointwise :
      (fun ω => V ω - U ω) ≤ᵐ[μ]
        fun ω => Δ ω ^ 2 + 2 * Δ ω * Real.sqrt (U ω) := by
    filter_upwards [hU, hV, hRoot] with ω hUω hVω hRootω
    have hBound := variance_difference_bound_of_sqrt_bound
      hUω hVω hRootω
    calc
      V ω - U ω ≤ Δ ω * (Δ ω + 2 * Real.sqrt (U ω)) := hBound
      _ = Δ ω ^ 2 + 2 * Δ ω * Real.sqrt (U ω) := by ring
  have hConditional := condExp_mono (m := mSmall)
    (hVInt.sub hUInt) hBoundInt hPointwise
  refine ⟨hRoot, ?_, ?_⟩
  · filter_upwards [hPointwise] with ω hω
    calc
      V ω - U ω ≤ Δ ω ^ 2 + 2 * Δ ω * Real.sqrt (U ω) := hω
      _ = Δ ω * (Δ ω + 2 * Real.sqrt (U ω)) := by ring
  · exact hConditional

/-- Specialisation to the manuscript's posterior variances `Uₙ₊₁` and
`Vₙ₊₁`. Their non-negativity and integrability are consequences of their
conditional squared-loss definitions, so the only substantive input retained
here is the root-risk estimate furnished by posterior displacement. -/
theorem posterior_displacement_bound_for_posteriorVariances
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (μ : Measure[m0] Ω)
    (mSmall mLarge : MeasurableSpace Ω)
    (KOld KNew : Ω → H) (Δ : Ω → ℝ)
    (hRoot : ∀ᵐ ω ∂μ,
      |Real.sqrt (posteriorVariance μ mLarge KNew ω) -
          Real.sqrt (posteriorVariance μ mLarge KOld ω)| ≤ Δ ω)
    (hDelta : MemLp Δ 2 μ) :
    (∀ᵐ ω ∂μ,
      |Real.sqrt (posteriorVariance μ mLarge KNew ω) -
          Real.sqrt (posteriorVariance μ mLarge KOld ω)| ≤ Δ ω) ∧
    (∀ᵐ ω ∂μ,
      posteriorVariance μ mLarge KNew ω -
          posteriorVariance μ mLarge KOld ω ≤
        Δ ω * (Δ ω + 2 *
          Real.sqrt (posteriorVariance μ mLarge KOld ω))) ∧
    (displacementMovementTerm μ mSmall
        (posteriorVariance μ mLarge KOld)
        (posteriorVariance μ mLarge KNew) ≤ᵐ[μ]
      μ[(fun ω =>
        Δ ω ^ 2 + 2 * Δ ω *
          Real.sqrt (posteriorVariance μ mLarge KOld ω)) | mSmall]) := by
  have hOldNonnegative :
      0 ≤ᵐ[μ] posteriorVariance μ mLarge KOld := by
    dsimp only [posteriorVariance, posteriorMSE]
    apply condExp_nonneg
    exact Filter.Eventually.of_forall (fun ω => sq_nonneg _)
  have hNewNonnegative :
      0 ≤ᵐ[μ] posteriorVariance μ mLarge KNew := by
    dsimp only [posteriorVariance, posteriorMSE]
    apply condExp_nonneg
    exact Filter.Eventually.of_forall (fun ω => sq_nonneg _)
  have hOldRoot :
      MemLp
        (fun ω => Real.sqrt (posteriorVariance μ mLarge KOld ω)) 2 μ :=
    memLp_two_sqrt_of_nonnegative_integrable μ
      (posteriorVariance μ mLarge KOld)
      hOldNonnegative integrable_condExp
  have hBoundInt : Integrable
      (fun ω =>
        Δ ω ^ 2 + 2 * Δ ω *
          Real.sqrt (posteriorVariance μ mLarge KOld ω)) μ :=
    integrable_displacement_bound_of_memLp_two μ
      (posteriorVariance μ mLarge KOld) Δ hDelta hOldRoot
  exact posterior_displacement_bound μ mSmall
    (posteriorVariance μ mLarge KOld)
    (posteriorVariance μ mLarge KNew) Δ
    hOldNonnegative hNewNonnegative hRoot
    integrable_condExp integrable_condExp hBoundInt

end PosteriorDisplacementBound

end

end SequentialLearning
