import SequentialLearning.PosteriorDisplacementInfrastructure
import SequentialLearning.PosteriorDisplacementBound
import Mathlib.Probability.Distributions.Bernoulli

/-!
# Sharpness envelope for posterior displacement

This file starts Result 18.  The universal upper envelope is independent of
the later explicit two-point witness.
-/

namespace SequentialLearning

open MeasureTheory ProbabilityTheory Measure unitInterval
open scoped ENNReal MeasureTheory ProbabilityTheory

noncomputable section

variable {S : Type*} [PseudoMetricSpace S] [MeasurableSpace S] [Nonempty S]
  [OpensMeasurableSpace S] [TopologicalSpace.SeparableSpace S]

/-- Result 18(i): the displacement envelope follows sharply from the
square-root Fréchet-variance Lipschitz bound. -/
theorem frechetVariance_difference_le_displacement_envelope
    (mu nu : ProbabilityMeasure S)
    (hmu : HasFiniteSecondMoment mu.toMeasure)
    (hnu : HasFiniteSecondMoment nu.toMeasure)
    (u delta : ℝ)
    (hu : Real.sqrt (frechetVariance mu.toMeasure).toReal = u)
    (hW : (wasserstein2 mu nu).toReal ≤ delta) :
    (frechetVariance nu.toMeasure).toReal -
        (frechetVariance mu.toMeasure).toReal ≤
      delta * (delta + 2 * u) := by
  have hRootW := sqrt_frechetVariance_abs_sub_le_wasserstein2
    nu mu hnu hmu
  rw [wasserstein2_comm] at hRootW
  have hRoot :
      |Real.sqrt (frechetVariance nu.toMeasure).toReal -
          Real.sqrt (frechetVariance mu.toMeasure).toReal| ≤ delta :=
    hRootW.trans hW
  have h := variance_difference_bound_of_sqrt_bound
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg hRoot
  rw [hu] at h
  exact h

section SymmetricTwoPointWitness

/-- The midpoint of the unit interval, used as the Bernoulli weight in the
sharpness witness. -/
def wassersteinHalfUnit : unitInterval :=
  ⟨1 / 2, by constructor <;> norm_num⟩

@[simp] theorem toNNReal_wassersteinHalfUnit :
    unitInterval.toNNReal wassersteinHalfUnit = (1 / 2 : NNReal) := by
  ext
  norm_num [wassersteinHalfUnit]

@[simp] theorem symm_wassersteinHalfUnit :
    unitInterval.symm wassersteinHalfUnit = wassersteinHalfUnit := by
  apply Subtype.ext
  norm_num [wassersteinHalfUnit, unitInterval.symm]

/-- A probability law placing equal mass on two specified points. -/
def halfBernoulliLaw {T : Type*} [MeasurableSpace T] (x y : T) :
    ProbabilityMeasure T :=
  ⟨Ber(x, y, wassersteinHalfUnit), inferInstance⟩

/-- The symmetric two-point probability law supported on `{-a,a}`. -/
def symmetricTwoPointLaw (a : ℝ) : ProbabilityMeasure ℝ :=
  halfBernoulliLaw (-a) a

private theorem measurable_real_squaredDistanceENN (s : ℝ) :
    Measurable (fun x : ℝ => ENNReal.ofReal (dist x s ^ 2)) := by
  fun_prop

/-- The fixed-centre Fréchet risk of the symmetric two-point law is
`a²+s²`. -/
theorem frechetRisk_symmetricTwoPointLaw (a s : ℝ) :
    frechetRisk (symmetricTwoPointLaw a).toMeasure s =
      ENNReal.ofReal (a ^ 2 + s ^ 2) := by
  rw [frechetRisk_eq_lintegral]
  simp only [symmetricTwoPointLaw, halfBernoulliLaw,
    ProbabilityMeasure.toMeasure, bernoulliMeasure_def,
    lintegral_add_measure, lintegral_smul_measure]
  rw [lintegral_dirac' _ (measurable_real_squaredDistanceENN s),
    lintegral_dirac' _ (measurable_real_squaredDistanceENN s)]
  simp only [toNNReal_wassersteinHalfUnit, symm_wassersteinHalfUnit]
  rw [ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul]
  norm_num
  rw [← mul_add]
  rw [← ENNReal.ofReal_pow (dist_nonneg : 0 ≤ dist (-a) s) 2,
    ← ENNReal.ofReal_pow (dist_nonneg : 0 ≤ dist a s) 2]
  simp only [Real.dist_eq]
  rw [sq_abs, sq_abs]
  rw [← ENNReal.ofReal_add (sq_nonneg (-a - s)) (sq_nonneg (a - s))]
  calc
    (2 : ENNReal)⁻¹ * ENNReal.ofReal ((-a - s) ^ 2 + (a - s) ^ 2) =
        ENNReal.ofReal ((2 : ℝ)⁻¹) *
          ENNReal.ofReal ((-a - s) ^ 2 + (a - s) ^ 2) := by
      congr 1
      rw [ENNReal.ofReal_inv_of_pos (by norm_num : 0 < (2 : ℝ))]
      norm_num
    _ = ENNReal.ofReal
        ((2 : ℝ)⁻¹ * ((-a - s) ^ 2 + (a - s) ^ 2)) := by
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ)⁻¹)]
    _ = ENNReal.ofReal (a ^ 2 + s ^ 2) := by
      congr 1
      ring

/-- The Fréchet variance of the symmetric two-point law is exactly `a²`. -/
theorem frechetVariance_symmetricTwoPointLaw (a : ℝ) :
    frechetVariance (symmetricTwoPointLaw a).toMeasure =
      ENNReal.ofReal (a ^ 2) := by
  rw [frechetVariance]
  apply le_antisymm
  · refine (iInf_le (fun s : ℝ =>
      frechetRisk (symmetricTwoPointLaw a).toMeasure s) 0).trans_eq ?_
    simpa using frechetRisk_symmetricTwoPointLaw a 0
  · refine le_iInf fun s => ?_
    rw [frechetRisk_symmetricTwoPointLaw]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg s])

/-- The coupling matching the negative atoms and the positive atoms. -/
def symmetricTwoPointCoupling (a b : ℝ) :
    TransportCoupling (symmetricTwoPointLaw a) (symmetricTwoPointLaw b) where
  law := halfBernoulliLaw (-a, -b) (a, b)
  fst_eq := by
    apply ProbabilityMeasure.toMeasure_injective
    rw [ProbabilityMeasure.toMeasure_map]
    simp only [halfBernoulliLaw, symmetricTwoPointLaw,
      ProbabilityMeasure.coe_mk]
    exact map_bernoulliMeasure' _ _ measurable_fst _
  snd_eq := by
    apply ProbabilityMeasure.toMeasure_injective
    rw [ProbabilityMeasure.toMeasure_map]
    simp only [halfBernoulliLaw, symmetricTwoPointLaw,
      ProbabilityMeasure.coe_mk]
    exact map_bernoulliMeasure' _ _ measurable_snd _

/-- The matching coupling has squared cost `(b-a)²`. -/
theorem transportL2Cost_symmetricTwoPointCoupling_sq (a b : ℝ) :
    transportL2Cost (symmetricTwoPointCoupling a b) ^ 2 =
      ENNReal.ofReal ((b - a) ^ 2) := by
  rw [transportL2Cost_sq_eq_lintegral]
  simp only [symmetricTwoPointCoupling, halfBernoulliLaw,
    ProbabilityMeasure.toMeasure, bernoulliMeasure_def,
    lintegral_add_measure, lintegral_smul_measure]
  have hCostMeas : Measurable
      (fun xy : ℝ × ℝ => ENNReal.ofReal (dist xy.1 xy.2 ^ 2)) := by
    fun_prop
  rw [lintegral_dirac' _ hCostMeas, lintegral_dirac' _ hCostMeas]
  simp only [toNNReal_wassersteinHalfUnit, symm_wassersteinHalfUnit]
  rw [ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul]
  have hneg : dist (-a) (-b) ^ 2 = (b - a) ^ 2 := by
    simp only [Real.dist_eq]
    rw [sq_abs]
    ring
  have hpos : dist a b ^ 2 = (b - a) ^ 2 := by
    simp only [Real.dist_eq]
    rw [sq_abs]
    ring
  rw [hneg, hpos]
  norm_num
  rw [← two_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
  simp

/-- Exact root cost of the matching coupling. -/
theorem transportL2Cost_symmetricTwoPointCoupling (a b : ℝ) :
    transportL2Cost (symmetricTwoPointCoupling a b) =
      ENNReal.ofReal |b - a| := by
  apply ENNReal.rpow_left_injective (by norm_num : (2 : ℝ) ≠ 0)
  simp only [ENNReal.rpow_two]
  rw [transportL2Cost_symmetricTwoPointCoupling_sq]
  rw [← ENNReal.ofReal_pow (abs_nonneg (b - a)) 2, sq_abs]

theorem symmetricTwoPointLaw_hasFiniteSecondMoment (a : ℝ) :
    HasFiniteSecondMoment (symmetricTwoPointLaw a).toMeasure := by
  refine ⟨0, ?_⟩
  rw [frechetRisk_symmetricTwoPointLaw]
  exact ENNReal.ofReal_lt_top

/-- Result 18(ii): symmetric two-point laws attain the universal displacement
envelope for every nonnegative starting spread and displacement. -/
theorem frechetVariance_displacement_envelope_sharp
    (u delta : ℝ) (hu : 0 ≤ u) (hdelta : 0 ≤ delta) :
    let mu := symmetricTwoPointLaw u
    let nu := symmetricTwoPointLaw (u + delta)
    HasFiniteSecondMoment mu.toMeasure ∧
    HasFiniteSecondMoment nu.toMeasure ∧
    Real.sqrt (frechetVariance mu.toMeasure).toReal = u ∧
    wasserstein2 mu nu = ENNReal.ofReal delta ∧
    (frechetVariance nu.toMeasure).toReal -
        (frechetVariance mu.toMeasure).toReal =
      delta * (delta + 2 * u) := by
  dsimp only
  have hMuFinite := symmetricTwoPointLaw_hasFiniteSecondMoment u
  have hNuFinite := symmetricTwoPointLaw_hasFiniteSecondMoment (u + delta)
  have hRootMu :
      Real.sqrt
        (frechetVariance (symmetricTwoPointLaw u).toMeasure).toReal = u := by
    rw [frechetVariance_symmetricTwoPointLaw,
      ENNReal.toReal_ofReal (sq_nonneg u),
      Real.sqrt_sq_eq_abs, abs_of_nonneg hu]
  have hRootNu :
      Real.sqrt
        (frechetVariance (symmetricTwoPointLaw (u + delta)).toMeasure).toReal =
          u + delta := by
    have hud : 0 ≤ u + delta := add_nonneg hu hdelta
    rw [frechetVariance_symmetricTwoPointLaw,
      ENNReal.toReal_ofReal (sq_nonneg (u + delta)),
      Real.sqrt_sq_eq_abs, abs_of_nonneg hud]
  have hUpper :
      wasserstein2 (symmetricTwoPointLaw u)
          (symmetricTwoPointLaw (u + delta)) ≤ ENNReal.ofReal delta := by
    calc
      wasserstein2 (symmetricTwoPointLaw u)
          (symmetricTwoPointLaw (u + delta)) ≤
          transportL2Cost (symmetricTwoPointCoupling u (u + delta)) :=
        wasserstein2_le_transportL2Cost _
      _ = ENNReal.ofReal |(u + delta) - u| :=
        transportL2Cost_symmetricTwoPointCoupling u (u + delta)
      _ = ENNReal.ofReal delta := by
        rw [show (u + delta) - u = delta by ring, abs_of_nonneg hdelta]
  have hLowerReal : delta ≤
      (wasserstein2 (symmetricTwoPointLaw u)
        (symmetricTwoPointLaw (u + delta))).toReal := by
    have hLip := sqrt_frechetVariance_abs_sub_le_wasserstein2
      (symmetricTwoPointLaw (u + delta)) (symmetricTwoPointLaw u)
      hNuFinite hMuFinite
    rw [wasserstein2_comm, hRootNu, hRootMu] at hLip
    simpa [abs_of_nonneg hdelta] using hLip
  have hW :
      wasserstein2 (symmetricTwoPointLaw u)
          (symmetricTwoPointLaw (u + delta)) = ENNReal.ofReal delta := by
    exact le_antisymm hUpper
      (ENNReal.ofReal_le_of_le_toReal hLowerReal)
  refine ⟨hMuFinite, hNuFinite, hRootMu, hW, ?_⟩
  rw [frechetVariance_symmetricTwoPointLaw,
    frechetVariance_symmetricTwoPointLaw,
    ENNReal.toReal_ofReal (sq_nonneg (u + delta)),
    ENNReal.toReal_ofReal (sq_nonneg u)]
  ring

end SymmetricTwoPointWitness

end

end SequentialLearning
