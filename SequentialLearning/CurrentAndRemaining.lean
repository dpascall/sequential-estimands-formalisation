import SequentialLearning.FixedEstimandMSE
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Current target and remaining change

This file formalises Proposition `currentremaining`.  It works in a real
Hilbert space and uses Mathlib's Bochner conditional expectation.  The
square-integrability assumptions are represented by `MemLp · 2 μ`.
-/

namespace SequentialLearning

open Filter MeasureTheory
open scoped ENNReal MeasureTheory ProbabilityTheory RealInnerProductSpace

noncomputable section

section CurrentAndRemaining

variable {Ω H : Type*} {m0 : MeasurableSpace Ω}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A random element centred at its conditional mean. -/
def conditionallyCentered (μ : Measure[m0] Ω) (m : MeasurableSpace Ω)
    (X : Ω → H) : Ω → H :=
  fun ω => X ω - posteriorMean μ m X ω

/-- Real conditional covariance of two Hilbert-valued random elements. -/
def conditionalCovariance (μ : Measure[m0] Ω) (m : MeasurableSpace Ω)
    (X Y : Ω → H) : Ω → ℝ :=
  μ[(fun ω =>
    inner ℝ (conditionallyCentered μ m X ω)
      (conditionallyCentered μ m Y ω)) | m]

/-- Two `L²` random elements have an integrable pointwise real inner
product. -/
theorem integrable_real_inner_of_memLp_two
    (μ : Measure[m0] Ω) (X Y : Ω → H)
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    Integrable (fun ω => inner ℝ (X ω) (Y ω)) μ := by
  have hInner := L2.integrable_inner (𝕜 := ℝ)
    (hX.toLp X) (hY.toLp Y)
  refine hInner.congr ?_
  filter_upwards [hX.coeFn_toLp, hY.coeFn_toLp] with ω hXω hYω
  rw [hXω, hYω]

/-- Conditional polarisation for the squared norm of a sum. -/
theorem conditional_norm_add_sq
    (μ : Measure[m0] Ω) (m : MeasurableSpace Ω)
    (X Y : Ω → H) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    μ[(fun ω => ‖X ω + Y ω‖ ^ 2) | m] =ᵐ[μ]
      fun ω =>
        μ[(fun a => ‖X a‖ ^ 2) | m] ω +
          μ[(fun a => ‖Y a‖ ^ 2) | m] ω +
            2 * μ[(fun a => inner ℝ (X a) (Y a)) | m] ω := by
  let A : Ω → ℝ := fun ω => ‖X ω‖ ^ 2
  let B : Ω → ℝ := fun ω => ‖Y ω‖ ^ 2
  let C : Ω → ℝ := fun ω => inner ℝ (X ω) (Y ω)
  have hA : Integrable A μ := by
    exact (memLp_two_iff_integrable_sq_norm hX.1).mp hX
  have hB : Integrable B μ := by
    exact (memLp_two_iff_integrable_sq_norm hY.1).mp hY
  have hC : Integrable C μ := by
    exact integrable_real_inner_of_memLp_two μ X Y hX hY
  have hNorm : (fun ω => ‖X ω + Y ω‖ ^ 2) =
      (A + B) + (2 : ℝ) • C := by
    funext ω
    simp only [A, B, C, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [norm_add_sq_real]
    ring
  rw [hNorm]
  have hOuter := condExp_add (hA.add hB) (hC.smul (2 : ℝ)) m
  have hAB := condExp_add hA hB m
  have hTwoC := condExp_smul (μ := μ) (2 : ℝ) C m
  filter_upwards [hOuter, hAB, hTwoC] with ω hOuterω hABω hTwoCω
  rw [hOuterω]
  simp only [Pi.add_apply]
  rw [hABω, hTwoCω]
  simp only [A, B, C, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- Exact conditional-variance decomposition into the current target and its
remaining change, together with the exact criterion for the terminal target to
have smaller posterior variance. -/
theorem current_target_and_remaining_change
    [CompleteSpace H] (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (_hm : m ≤ m0)
    (KLimit KCurrent : Ω → H)
    (hKLimit : MemLp KLimit 2 μ) (hKCurrent : MemLp KCurrent 2 μ) :
    let HRemaining := KLimit - KCurrent
    (posteriorVariance μ m KLimit =ᵐ[μ]
      fun ω =>
        posteriorVariance μ m KCurrent ω +
          posteriorVariance μ m HRemaining ω +
            2 * conditionalCovariance μ m KCurrent HRemaining ω) ∧
    (∀ᵐ ω ∂μ,
      posteriorVariance μ m KLimit ω <
          posteriorVariance μ m KCurrent ω ↔
        2 * conditionalCovariance μ m KCurrent HRemaining ω <
          -posteriorVariance μ m HRemaining ω) := by
  dsimp only
  let HRemaining : Ω → H := KLimit - KCurrent
  have hOneTwo : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hKLimitInt : Integrable KLimit μ := hKLimit.integrable hOneTwo
  have hKCurrentInt : Integrable KCurrent μ := hKCurrent.integrable hOneTwo
  have hH : MemLp HRemaining 2 μ := by
    exact hKLimit.sub hKCurrent
  have hCenteredCurrent :
      MemLp (conditionallyCentered μ m KCurrent) 2 μ := by
    change MemLp (KCurrent - posteriorMean μ m KCurrent) 2 μ
    exact hKCurrent.sub (hKCurrent.condExp hOneTwo)
  have hCenteredRemaining :
      MemLp (conditionallyCentered μ m HRemaining) 2 μ := by
    change MemLp (HRemaining - posteriorMean μ m HRemaining) 2 μ
    exact hH.sub (hH.condExp hOneTwo)
  have hCondSub :
      μ[HRemaining | m] =ᵐ[μ] μ[KLimit | m] - μ[KCurrent | m] := by
    simpa only [HRemaining] using
      condExp_sub hKLimitInt hKCurrentInt m
  have hCenteredDecomposition :
      conditionallyCentered μ m KLimit =ᵐ[μ]
        conditionallyCentered μ m KCurrent +
          conditionallyCentered μ m HRemaining := by
    filter_upwards [hCondSub] with ω hCondSubω
    simp only [Pi.sub_apply] at hCondSubω
    change KLimit ω - μ[KLimit | m] ω =
      (KCurrent ω - μ[KCurrent | m] ω) +
        ((KLimit ω - KCurrent ω) - μ[HRemaining | m] ω)
    rw [hCondSubω]
    abel
  have hSquaredDecomposition :
      (fun ω => ‖conditionallyCentered μ m KLimit ω‖ ^ 2) =ᵐ[μ]
        fun ω =>
          ‖conditionallyCentered μ m KCurrent ω +
            conditionallyCentered μ m HRemaining ω‖ ^ 2 := by
    filter_upwards [hCenteredDecomposition] with ω hω
    rw [hω]
    simp only [Pi.add_apply]
  have hVarianceToSum :
      posteriorVariance μ m KLimit =ᵐ[μ]
        μ[(fun ω =>
          ‖conditionallyCentered μ m KCurrent ω +
            conditionallyCentered μ m HRemaining ω‖ ^ 2) | m] := by
    simpa only [posteriorVariance, posteriorMSE, conditionallyCentered,
      posteriorMean] using condExp_congr_ae hSquaredDecomposition
  have hSum := conditional_norm_add_sq μ m
    (conditionallyCentered μ m KCurrent)
    (conditionallyCentered μ m HRemaining)
    hCenteredCurrent hCenteredRemaining
  have hDecomposition :
      posteriorVariance μ m KLimit =ᵐ[μ]
        fun ω =>
          posteriorVariance μ m KCurrent ω +
            posteriorVariance μ m HRemaining ω +
              2 * conditionalCovariance μ m KCurrent HRemaining ω := by
    refine hVarianceToSum.trans ?_
    simpa only [posteriorVariance, posteriorMSE, conditionalCovariance,
      conditionallyCentered, posteriorMean] using hSum
  refine ⟨hDecomposition, ?_⟩
  filter_upwards [hDecomposition] with ω hω
  rw [hω]
  constructor <;> intro hlt <;> linarith

end CurrentAndRemaining

end

end SequentialLearning
