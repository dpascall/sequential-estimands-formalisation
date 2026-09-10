import SequentialLearning.ExactMSEDecomposition
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Discrepancy weighting of posterior bias

This file formalises Lemma `biasweight`.  The proof avoids selecting a
normalised random direction.  It instead combines the norm form of conditional
Jensen with a scalar conditional Cauchy--Schwarz inequality.
-/

namespace SequentialLearning

open Filter MeasureTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

noncomputable section

section DiscrepancyWeighting

variable {Ω H : Type*} {m0 : MeasurableSpace Ω}

/-- A real quadratic that is non-negative on every rational argument has
non-positive discriminant.  The rational formulation is useful for obtaining
one common full-measure set before passing to all real arguments by density. -/
lemma sq_le_mul_of_quadratic_nonnegative_on_rationals
    (a b c : ℝ) (hc : 0 ≤ c)
    (hq : ∀ q : ℚ,
      0 ≤ a - 2 * (q : ℝ) * b + (q : ℝ) ^ 2 * c) :
    b ^ 2 ≤ a * c := by
  have hAll : ∀ t : ℝ, 0 ≤ a - 2 * t * b + t ^ 2 * c := by
    intro t
    refine Rat.denseRange_cast.induction_on t ?_ hq
    exact isClosed_le continuous_const (by fun_prop)
  rcases eq_or_lt_of_le hc with rfl | hcpos
  · by_cases hb : b = 0
    · simp [hb]
    · have hVertex := hAll ((a + 1) / (2 * b))
      have hIdentity :
          a - 2 * ((a + 1) / (2 * b)) * b +
              ((a + 1) / (2 * b)) ^ 2 * 0 = -1 := by
        field_simp [hb]
        ring
      rw [hIdentity] at hVertex
      linarith
  · have hcne : c ≠ 0 := ne_of_gt hcpos
    have hVertex := hAll (b / c)
    have hMultiplied := mul_nonneg hVertex hc
    have hIdentity :
        (a - 2 * (b / c) * b + (b / c) ^ 2 * c) * c =
          a * c - b ^ 2 := by
      field_simp [hcne]
      ring
    rw [hIdentity] at hMultiplied
    exact sub_nonneg.mp hMultiplied

/-- Scalar conditional Cauchy--Schwarz for two real `L²` random variables.
The proof uses non-negativity of the conditional expectation of
`(X - qY)²` for rational `q`, permitting the exceptional sets to be combined
countably before rational density is invoked pointwise. -/
theorem conditional_cauchy_schwarz_real
    (μ : Measure[m0] Ω) (m : MeasurableSpace Ω) (X Y : Ω → ℝ)
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    ∀ᵐ ω ∂μ,
      μ[(fun a => X a * Y a) | m] ω ^ 2 ≤
        μ[(fun a => X a ^ 2) | m] ω *
          μ[(fun a => Y a ^ 2) | m] ω := by
  let X2 : Ω → ℝ := fun ω => X ω ^ 2
  let XY : Ω → ℝ := fun ω => X ω * Y ω
  let Y2 : Ω → ℝ := fun ω => Y ω ^ 2
  have hX2Int : Integrable X2 μ := by
    simpa only [X2] using hX.integrable_sq
  have hXYInt : Integrable XY μ := by
    change Integrable (X * Y) μ
    exact memLp_one_iff_integrable.mp (hY.mul hX)
  have hY2Int : Integrable Y2 μ := by
    simpa only [Y2] using hY.integrable_sq
  have hY2Nonnegative : 0 ≤ᵐ[μ] μ[Y2 | m] := by
    apply condExp_nonneg
    filter_upwards with ω
    exact sq_nonneg _
  have hRat : ∀ q : ℚ, ∀ᵐ ω ∂μ,
      0 ≤ μ[X2 | m] ω - 2 * (q : ℝ) * μ[XY | m] ω +
        (q : ℝ) ^ 2 * μ[Y2 | m] ω := by
    intro q
    let Q : Ω → ℝ := fun ω => (X ω - (q : ℝ) * Y ω) ^ 2
    have hQNonnegative : 0 ≤ᵐ[μ] μ[Q | m] := by
      apply condExp_nonneg
      filter_upwards with ω
      exact sq_nonneg _
    have hQExpansion :
        Q = X2 + ((q : ℝ) ^ 2) • Y2 + (-2 * (q : ℝ)) • XY := by
      funext ω
      simp only [Q, X2, XY, Y2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hFirstInt : Integrable (X2 + ((q : ℝ) ^ 2) • Y2) μ :=
      hX2Int.add (hY2Int.smul ((q : ℝ) ^ 2))
    have hOuter := condExp_add hFirstInt
      (hXYInt.smul (-2 * (q : ℝ))) m
    have hFirst := condExp_add hX2Int
      (hY2Int.smul ((q : ℝ) ^ 2)) m
    have hYScale := condExp_smul (μ := μ) ((q : ℝ) ^ 2) Y2 m
    have hXYScale := condExp_smul (μ := μ) (-2 * (q : ℝ)) XY m
    rw [hQExpansion] at hQNonnegative
    filter_upwards [hQNonnegative, hOuter, hFirst, hYScale, hXYScale] with
      ω hNonnegative hOuterω hFirstω hYScaleω hXYScaleω
    rw [hOuterω] at hNonnegative
    simp only [Pi.zero_apply, Pi.add_apply] at hNonnegative
    rw [hFirstω] at hNonnegative
    simp only [Pi.add_apply] at hNonnegative
    rw [hYScaleω, hXYScaleω] at hNonnegative
    simp only [Pi.smul_apply, smul_eq_mul] at hNonnegative
    linarith
  rw [← ae_all_iff] at hRat
  filter_upwards [hRat, hY2Nonnegative] with ω hRatω hY2ω
  exact sq_le_mul_of_quadratic_nonnegative_on_rationals
    (μ[X2 | m] ω) (μ[XY | m] ω) (μ[Y2 | m] ω) hY2ω hRatω

/-- Indicator that a normed-space-valued random element is non-zero. -/
def nonzeroIndicator [NormedAddCommGroup H] (X : Ω → H) : Ω → ℝ :=
  fun ω => if 0 < ‖X ω‖ then 1 else 0

/-- The squared norm of a conditional mean is bounded by the conditional
probability of non-vanishing times the conditional second moment.  This is the
Banach-space core of discrepancy weighting. -/
theorem discrepancy_weighting_of_conditional_mean
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (X : Ω → H)
    (hXMeas : StronglyMeasurable[m0] X) (hX : MemLp X 2 μ) :
    ∀ᵐ ω ∂μ,
      ‖μ[X | m] ω‖ ^ 2 ≤
        μ[nonzeroIndicator X | m] ω *
          μ[(fun a => ‖X a‖ ^ 2) | m] ω := by
  let R : Ω → ℝ := fun ω => ‖X ω‖
  let A : Set Ω := {ω | 0 < R ω}
  let I : Ω → ℝ := A.indicator fun _ => 1
  have hRMeas : StronglyMeasurable[m0] R := hXMeas.norm
  have hAMeas : MeasurableSet[m0] A := by
    exact hRMeas.measurable measurableSet_Ioi
  have hR : MemLp R 2 μ := hX.norm
  have hI : MemLp I 2 μ := by
    exact memLp_indicator_const (μ := μ) 2 hAMeas (1 : ℝ)
      (Or.inr (measure_ne_top μ A))
  have hIndicatorX : A.indicator X = X := by
    funext ω
    by_cases hω : ω ∈ A
    · simp [hω]
    · have hNotPos : ¬0 < ‖X ω‖ := by
        change ¬0 < ‖X ω‖ at hω
        exact hω
      have hZero : X ω = 0 := by
        apply norm_eq_zero.mp
        exact le_antisymm (le_of_not_gt hNotPos) (norm_nonneg _)
      simp [hω, hZero]
  have hNormIndicator :
      (fun ω => ‖A.indicator X ω‖) = I * R := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [I, R, hω]
  have hISquare : (fun ω => I ω ^ 2) = I := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [I, hω]
  have hIRNonnegative : 0 ≤ᵐ[μ] I * R := by
    filter_upwards with ω
    by_cases hω : ω ∈ A <;> simp [I, R, hω, norm_nonneg]
  have hCondIRNonnegative : 0 ≤ᵐ[μ] μ[I * R | m] :=
    condExp_nonneg hIRNonnegative
  have hJensen := norm_condExp_le (μ := μ) (m := m) (A.indicator X)
  rw [hNormIndicator, hIndicatorX] at hJensen
  have hJensenSquared : ∀ᵐ ω ∂μ,
      ‖μ[X | m] ω‖ ^ 2 ≤ μ[I * R | m] ω ^ 2 := by
    filter_upwards [hJensen, hCondIRNonnegative] with ω hJensenω hIRω
    nlinarith [norm_nonneg (μ[X | m] ω)]
  have hCS := conditional_cauchy_schwarz_real μ m I R hI hR
  have hCS' : ∀ᵐ ω ∂μ,
      μ[I * R | m] ω ^ 2 ≤
        μ[I | m] ω * μ[(fun a => R a ^ 2) | m] ω := by
    rw [hISquare] at hCS
    exact hCS
  have hIForm : I = nonzeroIndicator X := by
    funext ω
    by_cases hω : ω ∈ A
    · have hPos : 0 < ‖X ω‖ := by
        change 0 < ‖X ω‖ at hω
        exact hω
      simp [I, nonzeroIndicator, hω, hPos]
    · have hNotPos : ¬0 < ‖X ω‖ := by
        change ¬0 < ‖X ω‖ at hω
        exact hω
      simp [I, nonzeroIndicator, hω, hNotPos]
  filter_upwards [hJensenSquared, hCS'] with ω hJensenω hCSω
  rw [hIForm] at hCSω
  exact hJensenω.trans hCSω

/-- Discrepancy weighting of the posterior bias generated by estimating the
current estimand rather than its terminal value. -/
theorem discrepancy_weighting_of_bias
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (KLimit KCurrent : Ω → H)
    (hKLimitMeas : StronglyMeasurable[m0] KLimit)
    (hKCurrentMeas : StronglyMeasurable[m0] KCurrent)
    (hKLimit : MemLp KLimit 2 μ) (hKCurrent : MemLp KCurrent 2 μ) :
    ∀ᵐ ω ∂μ,
      ‖posteriorMean μ m (KLimit - KCurrent) ω‖ ^ 2 ≤
        discrepancyTailAtZero μ m KLimit KCurrent ω *
          conditionalSquaredDiscrepancy μ m KLimit KCurrent ω := by
  have h := discrepancy_weighting_of_conditional_mean μ m
    (KLimit - KCurrent) (hKLimitMeas.sub hKCurrentMeas)
      (hKLimit.sub hKCurrent)
  have hIndicatorForm :
      nonzeroIndicator (KLimit - KCurrent) =
        fun ω => if 0 < ‖KLimit ω - KCurrent ω‖ then 1 else 0 := by
    funext ω
    rfl
  rw [hIndicatorForm] at h
  change ∀ᵐ ω ∂μ,
    ‖μ[KLimit - KCurrent | m] ω‖ ^ 2 ≤
      μ[(fun a => if 0 < ‖KLimit a - KCurrent a‖ then 1 else 0) | m] ω *
        μ[(fun a => ‖KLimit a - KCurrent a‖ ^ 2) | m] ω
  exact h

end DiscrepancyWeighting

end

end SequentialLearning
