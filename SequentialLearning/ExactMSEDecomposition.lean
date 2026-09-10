import SequentialLearning.CurrentAndRemaining
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Tactic.NormNum

/-!
# Exact terminal-target MSE decomposition

This file formalises Proposition `exactmse`.  The proof makes explicit the
conditional orthogonality used in the manuscript: the conditionally centred
terminal estimand is orthogonal, conditionally on the current information, to
the measurable posterior bias caused by reporting the current estimand.
-/

namespace SequentialLearning

open Filter MeasureTheory
open scoped ENNReal MeasureTheory ProbabilityTheory RealInnerProductSpace

noncomputable section

section ExactMSEDecomposition

variable {Ω H : Type*} {m0 : MeasurableSpace Ω}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Exact decomposition of terminal-target posterior MSE into posterior
variance of the terminal estimand and squared posterior estimand bias.  The
theorem also records the resulting lower bound and its equality condition. -/
theorem exact_mse_decomposition
    [CompleteSpace H] (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ m0)
    (KLimit KCurrent : Ω → H)
    (hKLimit : MemLp KLimit 2 μ) (hKCurrent : MemLp KCurrent 2 μ) :
    (posteriorMSE μ m KLimit KCurrent =ᵐ[μ]
      fun ω =>
        posteriorVariance μ m KLimit ω +
          ‖posteriorMean μ m (KLimit - KCurrent) ω‖ ^ 2) ∧
    (posteriorVariance μ m KLimit ≤ᵐ[μ]
      posteriorMSE μ m KLimit KCurrent) ∧
    ((posteriorMSE μ m KLimit KCurrent =ᵐ[μ]
        posteriorVariance μ m KLimit) ↔
      posteriorMean μ m (KLimit - KCurrent) =ᵐ[μ] 0) := by
  let HRemaining : Ω → H := KLimit - KCurrent
  let C : Ω → H := conditionallyCentered μ m KLimit
  let B : Ω → H := posteriorMean μ m HRemaining
  have hOneTwo : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hKLimitInt : Integrable KLimit μ := hKLimit.integrable hOneTwo
  have hKCurrentInt : Integrable KCurrent μ := hKCurrent.integrable hOneTwo
  have hH : MemLp HRemaining 2 μ := by
    exact hKLimit.sub hKCurrent
  have hB : MemLp B 2 μ := by
    exact hH.condExp hOneTwo
  have hC : MemLp C 2 μ := by
    change MemLp (KLimit - posteriorMean μ m KLimit) 2 μ
    exact hKLimit.sub (hKLimit.condExp hOneTwo)
  have hCInt : Integrable C μ := hC.integrable hOneTwo
  have hBMeas : StronglyMeasurable[m] B := by
    exact stronglyMeasurable_condExp
  have hCondSub :
      μ[HRemaining | m] =ᵐ[μ] μ[KLimit | m] - μ[KCurrent | m] := by
    simpa only [HRemaining] using
      condExp_sub hKLimitInt hKCurrentInt m
  have hCCondExpZero : μ[C | m] =ᵐ[μ] 0 := by
    have hSub :
        μ[KLimit - posteriorMean μ m KLimit | m] =ᵐ[μ]
          μ[KLimit | m] - μ[posteriorMean μ m KLimit | m] := by
      exact condExp_sub hKLimitInt integrable_condExp m
    have hTower :
        μ[posteriorMean μ m KLimit | m] =ᵐ[μ] μ[KLimit | m] := by
      simpa only [posteriorMean] using
        (condExp_condExp_of_le (μ := μ) (f := KLimit)
          (m₁ := m) (m₂ := m) le_rfl hm)
    refine (show μ[C | m] =ᵐ[μ]
      μ[KLimit | m] - μ[posteriorMean μ m KLimit | m] by
        change μ[KLimit - posteriorMean μ m KLimit | m] =ᵐ[μ]
          μ[KLimit | m] - μ[posteriorMean μ m KLimit | m]
        exact hSub).trans ?_
    filter_upwards [hTower] with ω hω
    simp only [Pi.sub_apply, Pi.zero_apply]
    rw [hω]
    simp
  have hCrossInt :
      Integrable (fun ω => inner ℝ (C ω) (B ω)) μ := by
    exact integrable_real_inner_of_memLp_two μ C B hC hB
  have hCrossPull :
      μ[(fun ω => inner ℝ (C ω) (B ω)) | m] =ᵐ[μ]
        fun ω => inner ℝ (μ[C | m] ω) (B ω) := by
    have hPull :=
      condExp_bilin_of_stronglyMeasurable_right
        (B := innerSL ℝ) hBMeas hCrossInt hCInt
    have hInnerInput :
        (fun ω => (innerSL ℝ) (C ω) (B ω)) =
          fun ω => inner ℝ (C ω) (B ω) := by
      funext ω
      rw [innerSL_apply_apply]
    have hInnerOutput :
        (fun ω => (innerSL ℝ) (μ[C | m] ω) (B ω)) =
          fun ω => inner ℝ (μ[C | m] ω) (B ω) := by
      funext ω
      rw [innerSL_apply_apply]
    rw [hInnerInput, hInnerOutput] at hPull
    exact hPull
  have hCrossZero :
      μ[(fun ω => inner ℝ (C ω) (B ω)) | m] =ᵐ[μ] 0 := by
    refine hCrossPull.trans ?_
    filter_upwards [hCCondExpZero] with ω hω
    rw [hω]
    simp
  have hBSqInt : Integrable (fun ω => ‖B ω‖ ^ 2) μ := by
    exact (memLp_two_iff_integrable_sq_norm hB.1).mp hB
  have hBSqCondExp :
      μ[(fun ω => ‖B ω‖ ^ 2) | m] = fun ω => ‖B ω‖ ^ 2 := by
    exact condExp_of_stronglyMeasurable hm (hBMeas.norm.pow 2) hBSqInt
  have hVectorDecomposition :
      (fun ω => KLimit ω - posteriorMean μ m KCurrent ω) =ᵐ[μ]
        fun ω => C ω + B ω := by
    filter_upwards [hCondSub] with ω hω
    change KLimit ω - μ[KCurrent | m] ω =
      (KLimit ω - μ[KLimit | m] ω) + μ[HRemaining | m] ω
    simp only [Pi.sub_apply] at hω
    rw [hω]
    abel
  have hRiskToSum :
      posteriorMSE μ m KLimit KCurrent =ᵐ[μ]
        μ[(fun ω => ‖C ω + B ω‖ ^ 2) | m] := by
    apply condExp_congr_ae
    filter_upwards [hVectorDecomposition] with ω hω
    rw [hω]
  have hPolarisation := conditional_norm_add_sq μ m C B hC hB
  have hExactLocal :
      posteriorMSE μ m KLimit KCurrent =ᵐ[μ]
        fun ω =>
          posteriorVariance μ m KLimit ω + ‖B ω‖ ^ 2 := by
    refine hRiskToSum.trans (hPolarisation.trans ?_)
    filter_upwards [hCrossZero] with ω hCrossω
    rw [hBSqCondExp, hCrossω]
    simp only [Pi.zero_apply, mul_zero, add_zero]
    rfl
  have hExact :
      posteriorMSE μ m KLimit KCurrent =ᵐ[μ]
        fun ω =>
          posteriorVariance μ m KLimit ω +
            ‖posteriorMean μ m (KLimit - KCurrent) ω‖ ^ 2 := by
    simpa only [B, HRemaining] using hExactLocal
  have hLower :
      posteriorVariance μ m KLimit ≤ᵐ[μ]
        posteriorMSE μ m KLimit KCurrent := by
    filter_upwards [hExact] with ω hω
    rw [hω]
    exact le_add_of_nonneg_right (sq_nonneg _)
  refine ⟨hExact, hLower, ?_⟩
  constructor
  · intro hEquality
    filter_upwards [hExactLocal, hEquality] with ω hExactω hEqualityω
    change B ω = 0
    have hSq : ‖B ω‖ ^ 2 = 0 := by
      rw [hExactω] at hEqualityω
      linarith
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hSq)
  · intro hBiasZero
    filter_upwards [hExact, hBiasZero] with ω hExactω hBiasω
    rw [hExactω, hBiasω]
    simp

end ExactMSEDecomposition

end

end SequentialLearning
