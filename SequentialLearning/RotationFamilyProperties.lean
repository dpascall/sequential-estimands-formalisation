import SequentialLearning.HilbertLearningCriterion
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic.Ring

/-!
# Properties of the rotation family

This file formalises the pathwise Hilbert geometry, conditional-variance
formula, and affine one-step identities used by the manuscript's rotation
family.
-/

namespace SequentialLearning

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal MeasureTheory ProbabilityTheory RealInnerProductSpace

noncomputable section

section RotationFamilyProperties

variable {Ω H : Type*} {m0 : MeasurableSpace Ω}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A scalar random variable embedded along a fixed Hilbert-space direction. -/
def alongDirection (X : Ω → ℝ) (e : H) : Ω → H :=
  fun ω => X ω • e

/-- The rotation-family stage estimand. -/
def rotationEstimand (α : ℝ) (Z0 W0 : Ω → ℝ) (eZ eW : H) : Ω → H :=
  fun ω =>
    (Real.cos α * Z0 ω) • eZ + (Real.sin α * W0 ω) • eW

/-- The terminal member of the rotation family. -/
def rotationLimit (Z0 : Ω → ℝ) (eZ : H) : Ω → H :=
  alongDirection Z0 eZ

/-- Deterministic discrepancy associated with a rotation angle. -/
def rotationDiscrepancy (α : ℝ) : ℝ :=
  2 * Real.sin (α / 2)

/-- The squared cosine weight in the variance formula. -/
def rotationGamma (α : ℝ) : ℝ :=
  Real.cos α ^ 2

/-- The affine conditional-variance expression for the rotation family. -/
def rotationVariance (γ v : ℝ) : ℝ :=
  γ + (1 - γ) * v

/-- Conditional variance of a real random variable. -/
def scalarConditionalVariance (μ : Measure[m0] Ω)
    (m : MeasurableSpace Ω) (X : Ω → ℝ) : Ω → ℝ :=
  μ[(fun ω => (X ω - μ[X | m] ω) ^ 2) | m]

omit [CompleteSpace H] in
/-- Pythagoras for arbitrary scalar coefficients of two orthonormal
directions. -/
theorem norm_sq_orthonormal_combination
    (eZ eW : H) (a b : ℝ)
    (hNormZ : ‖eZ‖ = 1) (hNormW : ‖eW‖ = 1)
    (hOrthogonal : inner ℝ eZ eW = 0) :
    ‖a • eZ + b • eW‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [norm_add_sq_real]
  simp only [norm_smul, hNormZ, hNormW, mul_one,
    real_inner_smul_left, inner_smul_right, hOrthogonal,
    mul_zero, add_zero]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]

omit [CompleteSpace H] in
/-- Every rotation-family stage lies on the unit sphere pathwise. -/
theorem rotationEstimand_norm
    (α : ℝ) (Z0 W0 : Ω → ℝ) (eZ eW : H)
    (hNormZ : ‖eZ‖ = 1) (hNormW : ‖eW‖ = 1)
    (hOrthogonal : inner ℝ eZ eW = 0)
    (hZSquare : ∀ ω, Z0 ω ^ 2 = 1)
    (hWSquare : ∀ ω, W0 ω ^ 2 = 1) :
    ∀ ω, ‖rotationEstimand α Z0 W0 eZ eW ω‖ = 1 := by
  intro ω
  have hSquare := norm_sq_orthonormal_combination eZ eW
    (Real.cos α * Z0 ω) (Real.sin α * W0 ω)
    hNormZ hNormW hOrthogonal
  have hNormSquare :
      ‖rotationEstimand α Z0 W0 eZ eW ω‖ ^ 2 = 1 := by
    rw [rotationEstimand]
    rw [hSquare, mul_pow, mul_pow, hZSquare, hWSquare,
      mul_one, mul_one, Real.cos_sq_add_sin_sq]
  nlinarith [norm_nonneg (rotationEstimand α Z0 W0 eZ eW ω)]

omit [CompleteSpace H] in
/-- Squared distance from a stage estimand to the terminal direction. -/
theorem rotationEstimand_sub_limit_norm_sq
    (α : ℝ) (Z0 W0 : Ω → ℝ) (eZ eW : H)
    (hNormZ : ‖eZ‖ = 1) (hNormW : ‖eW‖ = 1)
    (hOrthogonal : inner ℝ eZ eW = 0)
    (hZSquare : ∀ ω, Z0 ω ^ 2 = 1)
    (hWSquare : ∀ ω, W0 ω ^ 2 = 1) :
    ∀ ω,
      ‖rotationEstimand α Z0 W0 eZ eW ω -
          rotationLimit Z0 eZ ω‖ ^ 2 =
        rotationDiscrepancy α ^ 2 := by
  intro ω
  have hDifference :
      rotationEstimand α Z0 W0 eZ eW ω - rotationLimit Z0 eZ ω =
        ((Real.cos α - 1) * Z0 ω) • eZ +
          (Real.sin α * W0 ω) • eW := by
    simp only [rotationEstimand, rotationLimit, alongDirection]
    module
  rw [hDifference,
    norm_sq_orthonormal_combination eZ eW
      ((Real.cos α - 1) * Z0 ω) (Real.sin α * W0 ω)
      hNormZ hNormW hOrthogonal]
  rw [mul_pow, mul_pow, hZSquare, hWSquare, mul_one, mul_one]
  dsimp only [rotationDiscrepancy]
  rw [mul_pow]
  have hTrig := Real.sin_sq_eq_half_sub (α / 2)
  have hDouble : 2 * (α / 2) = α := by ring
  rw [hDouble] at hTrig
  rw [hTrig]
  nlinarith [Real.cos_sq_add_sin_sq α]

omit [CompleteSpace H] in
/-- On the admissible angle interval, the distance itself (not only its
square) is `2 sin(α/2)`. -/
theorem rotationEstimand_sub_limit_norm
    (α : ℝ) (hα : α ∈ Icc 0 (Real.pi / 2))
    (Z0 W0 : Ω → ℝ) (eZ eW : H)
    (hNormZ : ‖eZ‖ = 1) (hNormW : ‖eW‖ = 1)
    (hOrthogonal : inner ℝ eZ eW = 0)
    (hZSquare : ∀ ω, Z0 ω ^ 2 = 1)
    (hWSquare : ∀ ω, W0 ω ^ 2 = 1) :
    ∀ ω,
      ‖rotationEstimand α Z0 W0 eZ eW ω -
          rotationLimit Z0 eZ ω‖ = rotationDiscrepancy α := by
  intro ω
  have hSquare := rotationEstimand_sub_limit_norm_sq α Z0 W0 eZ eW
    hNormZ hNormW hOrthogonal hZSquare hWSquare ω
  have hSinNonnegative : 0 ≤ Real.sin (α / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hα.1])
      (by linarith [hα.2, Real.pi_pos.le])
  have hDiscrepancyNonnegative : 0 ≤ rotationDiscrepancy α := by
    dsimp only [rotationDiscrepancy]
    positivity
  nlinarith [norm_nonneg
    (rotationEstimand α Z0 W0 eZ eW ω - rotationLimit Z0 eZ ω)]

/-- The deterministic discrepancy is strictly increasing on the admissible
angle interval. -/
theorem rotationDiscrepancy_strictMonoOn :
    StrictMonoOn rotationDiscrepancy (Icc 0 (Real.pi / 2)) := by
  intro α hα β hβ hαβ
  have hHalf : α / 2 < β / 2 := by linarith
  have hSin := Real.sin_lt_sin_of_lt_of_le_pi_div_two
    (by linarith [hα.1, Real.pi_pos.le])
    (by linarith [hβ.2, Real.pi_pos.le]) hHalf
  dsimp only [rotationDiscrepancy]
  linarith

/-- The discrepancy maps the admissible angle interval into `[0, sqrt 2]`. -/
theorem rotationDiscrepancy_mapsTo :
    MapsTo rotationDiscrepancy (Icc 0 (Real.pi / 2))
      (Icc 0 (Real.sqrt 2)) := by
  intro α hα
  have hHalfNonnegative : 0 ≤ α / 2 := by linarith [hα.1]
  have hHalfLePi : α / 2 ≤ Real.pi := by
    linarith [hα.2, Real.pi_pos.le]
  have hSinNonnegative : 0 ≤ Real.sin (α / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hHalfNonnegative hHalfLePi
  have hSinUpper : Real.sin (α / 2) ≤ Real.sin (Real.pi / 4) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [hα.1, Real.pi_pos.le])
      (by linarith [Real.pi_pos.le])
      (by linarith [hα.2])
  constructor
  · dsimp only [rotationDiscrepancy]
    linarith
  · dsimp only [rotationDiscrepancy]
    rw [Real.sin_pi_div_four] at hSinUpper
    linarith

/-- Explicit inverse angle for an admissible discrepancy. -/
def angleOfRotationDiscrepancy (r : ℝ) : ℝ :=
  2 * Real.arcsin (r / 2)

/-- The explicit inverse angle lies in the admissible interval. -/
theorem angleOfRotationDiscrepancy_mem_Icc
    {r : ℝ} (hr : r ∈ Icc 0 (Real.sqrt 2)) :
    angleOfRotationDiscrepancy r ∈ Icc 0 (Real.pi / 2) := by
  have hrDivNonnegative : 0 ≤ r / 2 := by linarith [hr.1]
  have hSqrtTwoLtTwo : Real.sqrt 2 < 2 :=
    Real.sqrt_two_lt_three_halves.trans (by norm_num)
  have hrDivLeOne : r / 2 ≤ 1 := by linarith [hr.2]
  have hArcsinNonnegative : 0 ≤ Real.arcsin (r / 2) :=
    Real.arcsin_nonneg.mpr hrDivNonnegative
  have hArgMem : r / 2 ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith
  have hQuarterMem : Real.pi / 4 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos.le]
  have hArcsinUpper : Real.arcsin (r / 2) ≤ Real.pi / 4 := by
    rw [Real.arcsin_le_iff_le_sin hArgMem hQuarterMem]
    rw [Real.sin_pi_div_four]
    linarith [hr.2]
  dsimp only [angleOfRotationDiscrepancy]
  constructor <;> linarith

/-- The explicit inverse recovers the prescribed discrepancy. -/
theorem rotationDiscrepancy_angleOfRotationDiscrepancy
    {r : ℝ} (hr : r ∈ Icc 0 (Real.sqrt 2)) :
    rotationDiscrepancy (angleOfRotationDiscrepancy r) = r := by
  have hrDivLower : -1 ≤ r / 2 := by linarith [hr.1]
  have hSqrtTwoLtTwo : Real.sqrt 2 < 2 :=
    Real.sqrt_two_lt_three_halves.trans (by norm_num)
  have hrDivUpper : r / 2 ≤ 1 := by linarith [hr.2]
  dsimp only [rotationDiscrepancy, angleOfRotationDiscrepancy]
  have hHalf : 2 * Real.arcsin (r / 2) / 2 = Real.arcsin (r / 2) := by
    ring
  rw [hHalf, Real.sin_arcsin hrDivLower hrDivUpper]
  ring

/-- The discrepancy map is a bijection between the two closed intervals in
the manuscript. -/
theorem rotationDiscrepancy_bijOn :
    BijOn rotationDiscrepancy (Icc 0 (Real.pi / 2))
      (Icc 0 (Real.sqrt 2)) := by
  refine ⟨rotationDiscrepancy_mapsTo,
    rotationDiscrepancy_strictMonoOn.injOn, ?_⟩
  intro r hr
  exact ⟨angleOfRotationDiscrepancy r,
    angleOfRotationDiscrepancy_mem_Icc hr,
    rotationDiscrepancy_angleOfRotationDiscrepancy hr⟩

/-- Every deterministic discrepancy sequence has a unique admissible angle
sequence realising it. A terminal zero discrepancy forces a terminal zero
angle. -/
theorem unique_rotation_angle_sequence
    {ι : Type*} (r : ι → ℝ)
    (hr : ∀ i, r i ∈ Icc 0 (Real.sqrt 2)) :
    ∃! α : ι → ℝ,
      (∀ i, α i ∈ Icc 0 (Real.pi / 2)) ∧
        (∀ i, rotationDiscrepancy (α i) = r i) := by
  let α : ι → ℝ := fun i => angleOfRotationDiscrepancy (r i)
  refine ⟨α, ?_, ?_⟩
  · exact ⟨fun i => angleOfRotationDiscrepancy_mem_Icc (hr i),
      fun i => rotationDiscrepancy_angleOfRotationDiscrepancy (hr i)⟩
  · intro β hβ
    funext i
    exact rotationDiscrepancy_strictMonoOn.injOn
      (hβ.1 i) (angleOfRotationDiscrepancy_mem_Icc (hr i))
      (by rw [hβ.2 i,
        rotationDiscrepancy_angleOfRotationDiscrepancy (hr i)])

/-- Zero discrepancy is equivalent to the terminal angle `0`. -/
theorem rotationDiscrepancy_eq_zero_iff
    {α : ℝ} (hα : α ∈ Icc 0 (Real.pi / 2)) :
    rotationDiscrepancy α = 0 ↔ α = 0 := by
  constructor
  · intro h
    apply rotationDiscrepancy_strictMonoOn.injOn hα
      (by constructor <;> linarith [Real.pi_pos.le])
    have hZero : rotationDiscrepancy (0 : ℝ) = 0 := by
      simp [rotationDiscrepancy]
    exact h.trans hZero.symm
  · rintro rfl
    simp [rotationDiscrepancy]

/-- The cosine-squared variance weight strictly decreases as discrepancy
increases. -/
theorem rotationGamma_strictly_decreases_with_discrepancy
    {α β : ℝ} (hα : α ∈ Icc 0 (Real.pi / 2))
    (hβ : β ∈ Icc 0 (Real.pi / 2))
    (hDiscrepancy : rotationDiscrepancy α < rotationDiscrepancy β) :
    rotationGamma β < rotationGamma α := by
  have hAngle : α < β := by
    by_contra hNot
    have hβα : β ≤ α := le_of_not_gt hNot
    rcases hβα.eq_or_lt with hEq | hLt
    · subst β
      exact (lt_irrefl _ hDiscrepancy).elim
    · have := rotationDiscrepancy_strictMonoOn hβ hα hLt
      linarith
  have hCos : Real.cos β < Real.cos α :=
    Real.cos_lt_cos_of_nonneg_of_le_pi_div_two hα.1 hβ.2 hAngle
  have hCosβNonnegative : 0 ≤ Real.cos β :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hβ.1, Real.pi_pos.le], hβ.2⟩
  have hCosαNonnegative : 0 ≤ Real.cos α :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hα.1, Real.pi_pos.le], hα.2⟩
  dsimp only [rotationGamma]
  exact (sq_lt_sq₀ hCosβNonnegative hCosαNonnegative).mpr hCos

/-- Conditional expectation commutes with embedding a scalar random variable
along a fixed Hilbert-space direction. -/
theorem condExp_alongDirection
    (μ : Measure[m0] Ω) (m : MeasurableSpace Ω)
    (X : Ω → ℝ) (e : H) (hX : Integrable X μ) :
    μ[alongDirection X e | m] =ᵐ[μ]
      fun ω => μ[X | m] ω • e := by
  let T : ℝ →L[ℝ] H :=
    ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) e
  have hComm := T.comp_condExp_comm (m := m) hX
  have hTX : T ∘ X = alongDirection X e := by
    funext ω
    simp only [T, alongDirection, Function.comp_apply,
      ContinuousLinearMap.smulRight_apply, one_apply_eq_self]
  have hTCond : T ∘ μ[X | m] = fun ω => μ[X | m] ω • e := by
    funext ω
    simp only [T, Function.comp_apply,
      ContinuousLinearMap.smulRight_apply, one_apply_eq_self]
  rw [hTX] at hComm
  exact hComm.symm.trans (Filter.EventuallyEq.of_eq hTCond)

/-- Conditional mean of a rotation is the same rotation of the two scalar
conditional means. -/
theorem posteriorMean_rotationEstimand
    (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω)
    (α : ℝ) (Z0 W0 : Ω → ℝ) (eZ eW : H)
    (hZ : MemLp Z0 2 μ) (hW : MemLp W0 2 μ) :
    posteriorMean μ m (rotationEstimand α Z0 W0 eZ eW) =ᵐ[μ]
      fun ω =>
        (Real.cos α * μ[Z0 | m] ω) • eZ +
          (Real.sin α * μ[W0 | m] ω) • eW := by
  have hOneTwo : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hZInt : Integrable Z0 μ := hZ.integrable hOneTwo
  have hWInt : Integrable W0 μ := hW.integrable hOneTwo
  let TZ : ℝ →L[ℝ] H :=
    ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) eZ
  let TW : ℝ →L[ℝ] H :=
    ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) eW
  have hZDirInt : Integrable (alongDirection Z0 eZ) μ := by
    change Integrable (fun ω => Z0 ω • eZ) μ
    simpa only [TZ, Function.comp_apply,
      ContinuousLinearMap.smulRight_apply, one_apply_eq_self] using
      TZ.integrable_comp hZInt
  have hWDirInt : Integrable (alongDirection W0 eW) μ := by
    change Integrable (fun ω => W0 ω • eW) μ
    simpa only [TW, Function.comp_apply,
      ContinuousLinearMap.smulRight_apply, one_apply_eq_self] using
      TW.integrable_comp hWInt
  have hForm :
      rotationEstimand α Z0 W0 eZ eW =
        (Real.cos α) • alongDirection Z0 eZ +
          (Real.sin α) • alongDirection W0 eW := by
    funext ω
    simp only [rotationEstimand, alongDirection, Pi.add_apply, Pi.smul_apply]
    rw [smul_smul, smul_smul]
  have hOuter := condExp_add
    (hZDirInt.smul (Real.cos α)) (hWDirInt.smul (Real.sin α)) m
  have hScaleZ := condExp_smul (μ := μ)
    (Real.cos α) (alongDirection Z0 eZ) m
  have hScaleW := condExp_smul (μ := μ)
    (Real.sin α) (alongDirection W0 eW) m
  have hAlongZ := condExp_alongDirection μ m Z0 eZ hZInt
  have hAlongW := condExp_alongDirection μ m W0 eW hWInt
  change μ[rotationEstimand α Z0 W0 eZ eW | m] =ᵐ[μ] _
  rw [hForm]
  filter_upwards [hOuter, hScaleZ, hScaleW, hAlongZ, hAlongW] with
    ω hOuterω hScaleZω hScaleWω hAlongZω hAlongWω
  rw [hOuterω]
  simp only [Pi.add_apply]
  rw [hScaleZω, hScaleWω]
  simp only [Pi.smul_apply]
  rw [hAlongZω, hAlongWω]
  rw [smul_smul, smul_smul]

/-- Orthogonality removes the conditional covariance term: the posterior
variance of a rotation is the cosine-squared weighted scalar variance of
`Z0` plus the sine-squared weighted scalar variance of `W0`. -/
theorem posteriorVariance_rotationEstimand_orthogonal
    (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω)
    (α : ℝ) (Z0 W0 : Ω → ℝ) (eZ eW : H)
    (hNormZ : ‖eZ‖ = 1) (hNormW : ‖eW‖ = 1)
    (hOrthogonal : inner ℝ eZ eW = 0)
    (hZ : MemLp Z0 2 μ) (hW : MemLp W0 2 μ) :
    posteriorVariance μ m (rotationEstimand α Z0 W0 eZ eW) =ᵐ[μ]
      fun ω =>
        Real.cos α ^ 2 * scalarConditionalVariance μ m Z0 ω +
          Real.sin α ^ 2 * scalarConditionalVariance μ m W0 ω := by
  let RZ : Ω → ℝ := fun ω => Z0 ω - μ[Z0 | m] ω
  let RW : Ω → ℝ := fun ω => W0 ω - μ[W0 | m] ω
  have hOneTwo : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hRZ : MemLp RZ 2 μ := by
    exact hZ.sub (hZ.condExp hOneTwo)
  have hRW : MemLp RW 2 μ := by
    exact hW.sub (hW.condExp hOneTwo)
  have hRZSqInt : Integrable (fun ω => RZ ω ^ 2) μ := hRZ.integrable_sq
  have hRWSqInt : Integrable (fun ω => RW ω ^ 2) μ := hRW.integrable_sq
  have hMean := posteriorMean_rotationEstimand μ m α Z0 W0 eZ eW hZ hW
  have hCentered :
      conditionallyCentered μ m (rotationEstimand α Z0 W0 eZ eW) =ᵐ[μ]
        fun ω =>
          (Real.cos α * RZ ω) • eZ +
            (Real.sin α * RW ω) • eW := by
    filter_upwards [hMean] with ω hMeanω
    dsimp only [conditionallyCentered]
    rw [hMeanω]
    simp only [rotationEstimand, RZ, RW]
    module
  have hNormIntegrand :
      (fun ω =>
        ‖conditionallyCentered μ m
          (rotationEstimand α Z0 W0 eZ eW) ω‖ ^ 2) =ᵐ[μ]
      fun ω =>
        Real.cos α ^ 2 * RZ ω ^ 2 +
          Real.sin α ^ 2 * RW ω ^ 2 := by
    filter_upwards [hCentered] with ω hCenteredω
    rw [hCenteredω,
      norm_sq_orthonormal_combination eZ eW
        (Real.cos α * RZ ω) (Real.sin α * RW ω)
        hNormZ hNormW hOrthogonal]
    ring
  have hVarianceCongr :
      posteriorVariance μ m (rotationEstimand α Z0 W0 eZ eW) =ᵐ[μ]
        μ[(fun ω =>
          Real.cos α ^ 2 * RZ ω ^ 2 +
            Real.sin α ^ 2 * RW ω ^ 2) | m] := by
    simpa only [posteriorVariance, posteriorMSE, conditionallyCentered,
      posteriorMean] using condExp_congr_ae hNormIntegrand
  let Z2 : Ω → ℝ := fun ω => RZ ω ^ 2
  let W2 : Ω → ℝ := fun ω => RW ω ^ 2
  have hForm :
      (fun ω =>
        Real.cos α ^ 2 * RZ ω ^ 2 +
          Real.sin α ^ 2 * RW ω ^ 2) =
        (Real.cos α ^ 2) • Z2 + (Real.sin α ^ 2) • W2 := by
    funext ω
    simp only [Z2, W2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hOuter := condExp_add
    (hRZSqInt.smul (Real.cos α ^ 2))
    (hRWSqInt.smul (Real.sin α ^ 2)) m
  have hScaleZ := condExp_smul (μ := μ) (Real.cos α ^ 2) Z2 m
  have hScaleW := condExp_smul (μ := μ) (Real.sin α ^ 2) W2 m
  refine hVarianceCongr.trans ?_
  rw [hForm]
  filter_upwards [hOuter, hScaleZ, hScaleW] with
    ω hOuterω hScaleZω hScaleWω
  rw [hOuterω]
  simp only [Pi.add_apply]
  rw [hScaleZω, hScaleWω]
  simp only [Pi.smul_apply, smul_eq_mul, scalarConditionalVariance,
    Z2, W2, RZ, RW]

/-- A conditionally centred Rademacher variable has conditional variance one. -/
theorem scalarConditionalVariance_rademacher
    (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ m0)
    (Z0 : Ω → ℝ)
    (hCondMean : μ[Z0 | m] =ᵐ[μ] 0)
    (hZSquare : ∀ᵐ ω ∂μ, Z0 ω ^ 2 = 1) :
    scalarConditionalVariance μ m Z0 =ᵐ[μ] fun _ => 1 := by
  have hIntegrand :
      (fun ω => (Z0 ω - μ[Z0 | m] ω) ^ 2) =ᵐ[μ]
        fun _ => (1 : ℝ) := by
    filter_upwards [hCondMean, hZSquare] with ω hMeanω hSquareω
    simp only [Pi.zero_apply] at hMeanω
    rw [hMeanω, sub_zero, hSquareω]
  dsimp only [scalarConditionalVariance]
  refine (condExp_congr_ae hIntegrand).trans ?_
  rw [condExp_const hm (1 : ℝ)]

/-- Conditional-variance formula in the manuscript, assuming the independent
Rademacher coordinate has conditional mean zero. -/
theorem rotation_posteriorVariance_formula
    (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ m0)
    (α : ℝ) (Z0 W0 : Ω → ℝ) (eZ eW : H)
    (hNormZ : ‖eZ‖ = 1) (hNormW : ‖eW‖ = 1)
    (hOrthogonal : inner ℝ eZ eW = 0)
    (hZ : MemLp Z0 2 μ) (hW : MemLp W0 2 μ)
    (hCondMeanZ : μ[Z0 | m] =ᵐ[μ] 0)
    (hZSquare : ∀ᵐ ω ∂μ, Z0 ω ^ 2 = 1) :
    posteriorVariance μ m (rotationEstimand α Z0 W0 eZ eW) =ᵐ[μ]
      fun ω =>
        rotationVariance (rotationGamma α)
          (scalarConditionalVariance μ m W0 ω) := by
  have hOrthogonalVariance :=
    posteriorVariance_rotationEstimand_orthogonal μ m α Z0 W0 eZ eW
      hNormZ hNormW hOrthogonal hZ hW
  have hZVariance := scalarConditionalVariance_rademacher
    μ m hm Z0 hCondMeanZ hZSquare
  filter_upwards [hOrthogonalVariance, hZVariance] with
    ω hVarianceω hZVarianceω
  rw [hVarianceω, hZVarianceω]
  dsimp only [rotationVariance, rotationGamma]
  rw [Real.sin_sq]
  ring

/-- Independence from a larger information state implies the conditional
mean-zero input needed by the variance formula at every smaller state. -/
theorem rotation_posteriorVariance_formula_of_independent
    (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (mZ m mInfinity : MeasurableSpace Ω)
    (hZAmbient : mZ ≤ m0) (hInfinityAmbient : mInfinity ≤ m0)
    (hSmallInfinity : m ≤ mInfinity)
    (α : ℝ) (Z0 W0 : Ω → ℝ) (eZ eW : H)
    (hNormZ : ‖eZ‖ = 1) (hNormW : ‖eW‖ = 1)
    (hOrthogonal : inner ℝ eZ eW = 0)
    (hZ : MemLp Z0 2 μ) (hW : MemLp W0 2 μ)
    (hZMeasurable : StronglyMeasurable[mZ] Z0)
    (hZIndependent : Indep mZ mInfinity μ)
    (hZIntegral : ∫ ω, Z0 ω ∂μ = 0)
    (hZSquare : ∀ᵐ ω ∂μ, Z0 ω ^ 2 = 1) :
    posteriorVariance μ m (rotationEstimand α Z0 W0 eZ eW) =ᵐ[μ]
      fun ω =>
        rotationVariance (rotationGamma α)
          (scalarConditionalVariance μ m W0 ω) := by
  have hmAmbient : m ≤ m0 := hSmallInfinity.trans hInfinityAmbient
  have hZIndependentSmall : Indep mZ m μ := by
    rw [Indep_iff] at hZIndependent ⊢
    intro s t hs ht
    exact hZIndependent s t hs (hSmallInfinity t ht)
  have hCondMeanConst := condExp_indep_eq hZAmbient hmAmbient
    hZMeasurable hZIndependentSmall
  have hCondMeanZero : μ[Z0 | m] =ᵐ[μ] 0 := by
    filter_upwards [hCondMeanConst] with ω hω
    rw [hω, hZIntegral]
    rfl
  exact rotation_posteriorVariance_formula μ m hmAmbient α Z0 W0 eZ eW
    hNormZ hNormW hOrthogonal hZ hW hCondMeanZero hZSquare

/-- Conditional expectation of the affine rotation-variance expression. -/
theorem condExp_rotationVariance
    (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ m0)
    (γ : ℝ) (v : Ω → ℝ) (hv : Integrable v μ) :
    μ[(fun ω => rotationVariance γ (v ω)) | m] =ᵐ[μ]
      fun ω => rotationVariance γ (μ[v | m] ω) := by
  have hForm :
      (fun ω => rotationVariance γ (v ω)) =
        (fun _ => γ) + (1 - γ) • v := by
    funext ω
    simp only [rotationVariance, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hForm]
  have hOuter := condExp_add (integrable_const γ)
    (hv.smul (1 - γ)) m
  have hScale := condExp_smul (μ := μ) (1 - γ) v m
  have hConst : μ[(fun _ : Ω => γ) | m] = fun _ => γ :=
    condExp_const hm γ
  filter_upwards [hOuter, hScale] with ω hOuterω hScaleω
  rw [hOuterω]
  simp only [Pi.add_apply]
  rw [hConst, hScaleω]
  simp only [Pi.smul_apply, smul_eq_mul, rotationVariance]

/-- The one-step variance change is the sum of the angle-change contribution
and the information-refinement contribution. -/
theorem rotation_variance_increment_identity
    (γn γnext vn vbar : ℝ) :
    rotationVariance γnext vbar - rotationVariance γn vn =
      (γnext - γn) * (1 - vbar) +
        (1 - γn) * (vbar - vn) := by
  dsimp only [rotationVariance]
  ring

/-- The old-target information gain in the rotation family. -/
theorem rotation_information_identity
    (γn vn vbar : ℝ) :
    rotationVariance γn vn - rotationVariance γn vbar =
      (1 - γn) * (vn - vbar) := by
  dsimp only [rotationVariance]
  ring

/-- Abstract probabilistic form of both identities in part (iii). Once the
three variance quantities have the affine rotation form, the remaining work
is conditional-expectation linearity followed by deterministic algebra. -/
theorem rotation_one_step_identities
    (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ m0)
    (γn γnext : ℝ) (vn vnext Vn Vnext UoldNext : Ω → ℝ)
    (hvnext : Integrable vnext μ)
    (hVn : Vn =ᵐ[μ] fun ω => rotationVariance γn (vn ω))
    (hVnext : Vnext =ᵐ[μ]
      fun ω => rotationVariance γnext (vnext ω))
    (hUoldNext : UoldNext =ᵐ[μ]
      fun ω => rotationVariance γn (vnext ω)) :
    ((fun ω => μ[Vnext | m] ω - Vn ω) =ᵐ[μ]
      fun ω =>
        (γnext - γn) * (1 - μ[vnext | m] ω) +
          (1 - γn) * (μ[vnext | m] ω - vn ω)) ∧
    ((fun ω => informationGain (Vn ω) (μ[UoldNext | m] ω)) =ᵐ[μ]
      fun ω => (1 - γn) * (vn ω - μ[vnext | m] ω)) := by
  have hCondNextAffine := condExp_rotationVariance μ m hm γnext vnext hvnext
  have hCondOldAffine := condExp_rotationVariance μ m hm γn vnext hvnext
  have hCondVnext : μ[Vnext | m] =ᵐ[μ]
      fun ω => rotationVariance γnext (μ[vnext | m] ω) :=
    (condExp_congr_ae hVnext).trans hCondNextAffine
  have hCondUold : μ[UoldNext | m] =ᵐ[μ]
      fun ω => rotationVariance γn (μ[vnext | m] ω) :=
    (condExp_congr_ae hUoldNext).trans hCondOldAffine
  constructor
  · filter_upwards [hVn, hCondVnext] with ω hVnω hNextω
    rw [hVnω, hNextω]
    exact rotation_variance_increment_identity γn γnext
      (vn ω) (μ[vnext | m] ω)
  · filter_upwards [hVn, hCondUold] with ω hVnω hOldω
    rw [hVnω, hOldω]
    dsimp only [informationGain]
    exact rotation_information_identity γn (vn ω) (μ[vnext | m] ω)

/-- Full stage-`n` and stage-`n+1` specialisation of part (iii), including
the manuscript's `Jₙ⁽ᵈ⁾` rather than an abstract information-gain symbol. -/
theorem rotation_family_one_step_formulas
    (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (mZ mSmall mLarge mInfinity : MeasurableSpace Ω)
    (hZAmbient : mZ ≤ m0) (hInfinityAmbient : mInfinity ≤ m0)
    (hSmallLarge : mSmall ≤ mLarge)
    (hLargeInfinity : mLarge ≤ mInfinity)
    (αn αnext : ℝ) (Z0 W0 : Ω → ℝ) (eZ eW : H)
    (hNormZ : ‖eZ‖ = 1) (hNormW : ‖eW‖ = 1)
    (hOrthogonal : inner ℝ eZ eW = 0)
    (hZ : MemLp Z0 2 μ) (hW : MemLp W0 2 μ)
    (hZMeasurable : StronglyMeasurable[mZ] Z0)
    (hZIndependent : Indep mZ mInfinity μ)
    (hZIntegral : ∫ ω, Z0 ω ∂μ = 0)
    (hZSquare : ∀ᵐ ω ∂μ, Z0 ω ^ 2 = 1) :
    ((fun ω =>
      μ[posteriorVariance μ mLarge
          (rotationEstimand αnext Z0 W0 eZ eW) | mSmall] ω -
        posteriorVariance μ mSmall
          (rotationEstimand αn Z0 W0 eZ eW) ω) =ᵐ[μ]
      fun ω =>
        (rotationGamma αnext - rotationGamma αn) *
            (1 - μ[scalarConditionalVariance μ mLarge W0 | mSmall] ω) +
          (1 - rotationGamma αn) *
            (μ[scalarConditionalVariance μ mLarge W0 | mSmall] ω -
              scalarConditionalVariance μ mSmall W0 ω)) ∧
    (hilbertInformationTerm μ mSmall mLarge
        (rotationEstimand αn Z0 W0 eZ eW) =ᵐ[μ]
      fun ω =>
        (1 - rotationGamma αn) *
          (scalarConditionalVariance μ mSmall W0 ω -
            μ[scalarConditionalVariance μ mLarge W0 | mSmall] ω)) := by
  have hSmallInfinity : mSmall ≤ mInfinity :=
    hSmallLarge.trans hLargeInfinity
  have hmSmall : mSmall ≤ m0 := hSmallInfinity.trans hInfinityAmbient
  have hVn := rotation_posteriorVariance_formula_of_independent μ
    mZ mSmall mInfinity hZAmbient hInfinityAmbient hSmallInfinity
    αn Z0 W0 eZ eW hNormZ hNormW hOrthogonal hZ hW
    hZMeasurable hZIndependent hZIntegral hZSquare
  have hVnext := rotation_posteriorVariance_formula_of_independent μ
    mZ mLarge mInfinity hZAmbient hInfinityAmbient hLargeInfinity
    αnext Z0 W0 eZ eW hNormZ hNormW hOrthogonal hZ hW
    hZMeasurable hZIndependent hZIntegral hZSquare
  have hUoldNext := rotation_posteriorVariance_formula_of_independent μ
    mZ mLarge mInfinity hZAmbient hInfinityAmbient hLargeInfinity
    αn Z0 W0 eZ eW hNormZ hNormW hOrthogonal hZ hW
    hZMeasurable hZIndependent hZIntegral hZSquare
  have hIdentities := rotation_one_step_identities μ mSmall hmSmall
    (rotationGamma αn) (rotationGamma αnext)
    (scalarConditionalVariance μ mSmall W0)
    (scalarConditionalVariance μ mLarge W0)
    (posteriorVariance μ mSmall (rotationEstimand αn Z0 W0 eZ eW))
    (posteriorVariance μ mLarge (rotationEstimand αnext Z0 W0 eZ eW))
    (posteriorVariance μ mLarge (rotationEstimand αn Z0 W0 eZ eW))
    integrable_condExp hVn hVnext hUoldNext
  refine ⟨hIdentities.1, ?_⟩
  change ((fun ω =>
    informationGain
      (posteriorVariance μ mSmall
        (rotationEstimand αn Z0 W0 eZ eW) ω)
      (μ[posteriorVariance μ mLarge
        (rotationEstimand αn Z0 W0 eZ eW) | mSmall] ω)) =ᵐ[μ]
    fun ω =>
      (1 - rotationGamma αn) *
        (scalarConditionalVariance μ mSmall W0 ω -
          μ[scalarConditionalVariance μ mLarge W0 | mSmall] ω))
  exact hIdentities.2

omit [CompleteSpace H] in
/-- At angle zero the stage estimand is exactly the terminal estimand. -/
theorem rotationEstimand_zero
    (Z0 W0 : Ω → ℝ) (eZ eW : H) :
    rotationEstimand 0 Z0 W0 eZ eW = rotationLimit Z0 eZ := by
  funext ω
  simp [rotationEstimand, rotationLimit, alongDirection]

omit [CompleteSpace H] in
/-- Under the pointwise Rademacher and orthonormality assumptions, equality
with the terminal estimand occurs exactly at angle zero. -/
theorem rotationEstimand_eq_limit_iff
    [Nonempty Ω]
    (α : ℝ) (hα : α ∈ Icc 0 (Real.pi / 2))
    (Z0 W0 : Ω → ℝ) (eZ eW : H)
    (hNormZ : ‖eZ‖ = 1) (hNormW : ‖eW‖ = 1)
    (hOrthogonal : inner ℝ eZ eW = 0)
    (hZSquare : ∀ ω, Z0 ω ^ 2 = 1)
    (hWSquare : ∀ ω, W0 ω ^ 2 = 1) :
    rotationEstimand α Z0 W0 eZ eW = rotationLimit Z0 eZ ↔
      α = 0 := by
  constructor
  · intro hEquality
    let ω : Ω := Classical.choice (inferInstance : Nonempty Ω)
    have hNorm :
        ‖rotationEstimand α Z0 W0 eZ eW ω -
            rotationLimit Z0 eZ ω‖ = 0 := by
      rw [hEquality]
      simp
    have hGeometry := rotationEstimand_sub_limit_norm α hα
      Z0 W0 eZ eW hNormZ hNormW hOrthogonal hZSquare hWSquare ω
    apply (rotationDiscrepancy_eq_zero_iff hα).mp
    rw [← hGeometry]
    exact hNorm
  · rintro rfl
    exact rotationEstimand_zero Z0 W0 eZ eW

end RotationFamilyProperties

end

end SequentialLearning
