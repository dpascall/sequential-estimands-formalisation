import SequentialLearning.DiscrepancyWeighting

/-!
# Mean squared error hierarchy

This file formalises Theorem `msehierarchy`.  The stagewise sandwich and its
supermartingale dynamics are separated so that the role of each hypothesis is
visible in the formal statement.
-/

namespace SequentialLearning

open Filter MeasureTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

noncomputable section

section MSEHierarchy

variable {Ω H : Type*} {m0 : MeasurableSpace Ω}
  [NormedAddCommGroup H]

/-- The four-term MSE hierarchy at one information stage. -/
theorem mean_squared_error_hierarchy
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ m0)
    (KLimit KCurrent : Ω → H)
    (hKLimitMeas : StronglyMeasurable[m0] KLimit)
    (hKCurrentMeas : StronglyMeasurable[m0] KCurrent)
    (hKLimit : MemLp KLimit 2 μ) (hKCurrent : MemLp KCurrent 2 μ) :
    ∀ᵐ ω ∂μ,
      posteriorVariance μ m KLimit ω ≤
          posteriorMSE μ m KLimit KCurrent ω ∧
        posteriorMSE μ m KLimit KCurrent ω ≤
          weightedMSEUpperBound μ m KLimit KCurrent ω ∧
        weightedMSEUpperBound μ m KLimit KCurrent ω ≤
          fullMSEUpperBound μ m KLimit KCurrent ω := by
  have hExact := exact_mse_decomposition μ m hm KLimit KCurrent
    hKLimit hKCurrent
  have hBias := discrepancy_weighting_of_bias μ m KLimit KCurrent
    hKLimitMeas hKCurrentMeas hKLimit hKCurrent
  have hTailLeOne :
      discrepancyTailAtZero μ m KLimit KCurrent ≤ᵐ[μ] 1 := by
    apply condExp_le_nonneg_const (μ := μ) (m := m) zero_le_one
    filter_upwards with ω
    split <;> norm_num
  have hDiscrepancyNonnegative :
      0 ≤ᵐ[μ] conditionalSquaredDiscrepancy μ m KLimit KCurrent := by
    apply condExp_nonneg
    filter_upwards with ω
    exact sq_nonneg _
  filter_upwards [hExact.1, hExact.2.1, hBias, hTailLeOne,
    hDiscrepancyNonnegative] with
      ω hExactω hLowerω hBiasω hTailω hDiscrepancyω
  refine ⟨hLowerω, ?_, ?_⟩
  · rw [hExactω]
    change
      posteriorVariance μ m KLimit ω +
          ‖posteriorMean μ m (KLimit - KCurrent) ω‖ ^ 2 ≤
        posteriorVariance μ m KLimit ω +
          discrepancyTailAtZero μ m KLimit KCurrent ω *
            conditionalSquaredDiscrepancy μ m KLimit KCurrent ω
    linarith
  · change
      posteriorVariance μ m KLimit ω +
          discrepancyTailAtZero μ m KLimit KCurrent ω *
            conditionalSquaredDiscrepancy μ m KLimit KCurrent ω ≤
        posteriorVariance μ m KLimit ω +
          conditionalSquaredDiscrepancy μ m KLimit KCurrent ω
    have hProduct := mul_le_of_le_one_left hDiscrepancyω hTailω
    linarith

/-- Under pointwise monotonicity of the discrepancy paths, their conditional
second moments form a supermartingale. -/
theorem conditional_squared_discrepancy_supermartingale
    (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (KLimit : Ω → H) (K : ℕ → Ω → H)
    (hKLimit : MemLp KLimit 2 μ) (hK : ∀ n, MemLp (K n) 2 μ)
    (hMonotone : ∀ i j, i ≤ j → ∀ ω,
      limitDiscrepancy KLimit (K j) ω ≤
        limitDiscrepancy KLimit (K i) ω) :
    Supermartingale
      (fun n => conditionalSquaredDiscrepancy μ (ℱ n) KLimit (K n)) ℱ μ := by
  let R : ℕ → Ω → ℝ := fun n => limitDiscrepancy KLimit (K n)
  have hR2Int : ∀ n, Integrable (fun ω => R n ω ^ 2) μ := by
    intro n
    have hDifference : MemLp (KLimit - K n) 2 μ := hKLimit.sub (hK n)
    simpa only [R, limitDiscrepancy, Pi.sub_apply] using
      ((memLp_two_iff_integrable_sq_norm hDifference.1).mp hDifference)
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact stronglyMeasurable_condExp
  · intro i j hij
    have hSquares : (fun ω => R j ω ^ 2) ≤ᵐ[μ]
        fun ω => R i ω ^ 2 := by
      filter_upwards with ω
      have hOrder := hMonotone i j hij ω
      change R j ω ≤ R i ω at hOrder
      have hRi : 0 ≤ R i ω := by
        simp [R, limitDiscrepancy]
      have hRj : 0 ≤ R j ω := by
        simp [R, limitDiscrepancy]
      nlinarith
    have hMonotoneCond :
        μ[(fun ω => R j ω ^ 2) | ℱ i] ≤ᵐ[μ]
          μ[(fun ω => R i ω ^ 2) | ℱ i] :=
      condExp_mono (hR2Int j) (hR2Int i) hSquares
    have hTower :
        μ[μ[(fun ω => R j ω ^ 2) | ℱ j] | ℱ i] =ᵐ[μ]
          μ[(fun ω => R j ω ^ 2) | ℱ i] :=
      condExp_condExp_of_le (ℱ.mono hij) (ℱ.le j)
    filter_upwards [hTower, hMonotoneCond] with ω hTowerω hMonotoneω
    simpa only [conditionalSquaredDiscrepancy, R] using
      hTowerω ▸ hMonotoneω
  · intro n
    exact integrable_condExp

/-- Dynamic part of the MSE hierarchy.  Fixed-target learning controls the
lower process, while pointwise monotonicity controls the discrepancy-moment
process; their sum is the full upper process. -/
theorem mean_squared_error_hierarchy_dynamics
    [NormedSpace ℝ H]
    (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (KLimit : Ω → H) (K : ℕ → Ω → H)
    (hKLimit : MemLp KLimit 2 μ) (hK : ∀ n, MemLp (K n) 2 μ)
    (hMonotone : ∀ i j, i ≤ j → ∀ ω,
      limitDiscrepancy KLimit (K j) ω ≤
        limitDiscrepancy KLimit (K i) ω)
    (hFixedTargetLearning :
      Supermartingale
        (fun n => posteriorVariance μ (ℱ n) KLimit) ℱ μ) :
    (∀ n, 0 ≤ᵐ[μ] posteriorVariance μ (ℱ n) KLimit) ∧
      Supermartingale
        (fun n => posteriorVariance μ (ℱ n) KLimit) ℱ μ ∧
    (∀ n, 0 ≤ᵐ[μ]
      conditionalSquaredDiscrepancy μ (ℱ n) KLimit (K n)) ∧
      Supermartingale
        (fun n => conditionalSquaredDiscrepancy μ (ℱ n) KLimit (K n)) ℱ μ ∧
    (∀ n, 0 ≤ᵐ[μ] fullMSEUpperBound μ (ℱ n) KLimit (K n)) ∧
      Supermartingale
        (fun n => fullMSEUpperBound μ (ℱ n) KLimit (K n)) ℱ μ := by
  have hDiscrepancySM :=
    conditional_squared_discrepancy_supermartingale μ ℱ KLimit K
      hKLimit hK hMonotone
  have hVarianceNonnegative :
      ∀ n, 0 ≤ᵐ[μ] posteriorVariance μ (ℱ n) KLimit := by
    intro n
    simpa only [posteriorVariance] using
      posteriorMSE_nonnegative μ (ℱ n) KLimit KLimit
  have hDiscrepancyNonnegative :
      ∀ n, 0 ≤ᵐ[μ]
        conditionalSquaredDiscrepancy μ (ℱ n) KLimit (K n) := by
    intro n
    apply condExp_nonneg
    filter_upwards with ω
    exact sq_nonneg _
  have hFullNonnegative :
      ∀ n, 0 ≤ᵐ[μ] fullMSEUpperBound μ (ℱ n) KLimit (K n) := by
    intro n
    filter_upwards [hVarianceNonnegative n,
      hDiscrepancyNonnegative n] with ω hVarianceω hDiscrepancyω
    exact add_nonneg hVarianceω hDiscrepancyω
  have hFullSM :
      Supermartingale
        (fun n => fullMSEUpperBound μ (ℱ n) KLimit (K n)) ℱ μ := by
    change Supermartingale
      ((fun n => posteriorVariance μ (ℱ n) KLimit) +
        fun n => conditionalSquaredDiscrepancy μ (ℱ n) KLimit (K n)) ℱ μ
    exact hFixedTargetLearning.add hDiscrepancySM
  exact ⟨hVarianceNonnegative, hFixedTargetLearning,
    hDiscrepancyNonnegative, hDiscrepancySM,
    hFullNonnegative, hFullSM⟩

end MSEHierarchy

end

end SequentialLearning
