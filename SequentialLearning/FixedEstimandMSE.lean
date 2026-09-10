import Mathlib.Probability.Martingale.Basic

/-!
# Mean squared error for a fixed estimand

This file formalises Corollary `msefixed`.  The MSE quantities use Mathlib's
Bochner conditional expectation, and the dynamical conclusion uses Mathlib's
actual `Supermartingale` predicate.

The supermartingale property of posterior variance is supplied as the output
of the manuscript's earlier fixed-target learning result.  The theorem here
proves that fixedness collapses the complete MSE hierarchy to that process and
therefore transfers its supermartingale property to the reported-estimand MSE.
-/

namespace SequentialLearning

open Filter MeasureTheory
open scoped MeasureTheory ProbabilityTheory

noncomputable section

section FixedEstimandMSE

variable {Ω H : Type*} {m0 : MeasurableSpace Ω}
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The posterior mean of a Hilbert- or Banach-valued estimand. -/
def posteriorMean (μ : Measure[m0] Ω) (m : MeasurableSpace Ω)
    (K : Ω → H) : Ω → H :=
  μ[K | m]

/-- Conditional MSE of the posterior mean of `KCurrent`, evaluated against
the scientifically relevant terminal target `KLimit`. -/
def posteriorMSE (μ : Measure[m0] Ω) (m : MeasurableSpace Ω)
    (KLimit KCurrent : Ω → H) : Ω → ℝ :=
  μ[(fun ω => ‖KLimit ω - posteriorMean μ m KCurrent ω‖ ^ 2) | m]

/-- Conditional posterior variance of the terminal target, written in the
same squared-error form as `posteriorMSE`. -/
def posteriorVariance (μ : Measure[m0] Ω) (m : MeasurableSpace Ω)
    (KLimit : Ω → H) : Ω → ℝ :=
  posteriorMSE μ m KLimit KLimit

/-- Distance from the current estimand to its terminal value. -/
def limitDiscrepancy (KLimit KCurrent : Ω → H) : Ω → ℝ :=
  fun ω => ‖KLimit ω - KCurrent ω‖

/-- The posterior discrepancy tail at zero, represented as a conditional
expectation of the event indicator. -/
def discrepancyTailAtZero (μ : Measure[m0] Ω) (m : MeasurableSpace Ω)
    (KLimit KCurrent : Ω → H) : Ω → ℝ :=
  μ[(fun ω => if 0 < limitDiscrepancy KLimit KCurrent ω then 1 else 0) | m]

/-- Posterior second moment of the current-to-limit discrepancy. -/
def conditionalSquaredDiscrepancy (μ : Measure[m0] Ω) (m : MeasurableSpace Ω)
    (KLimit KCurrent : Ω → H) : Ω → ℝ :=
  μ[(fun ω => limitDiscrepancy KLimit KCurrent ω ^ 2) | m]

/-- The absorption-weighted middle upper bound in the MSE hierarchy. -/
def weightedMSEUpperBound (μ : Measure[m0] Ω) (m : MeasurableSpace Ω)
    (KLimit KCurrent : Ω → H) : Ω → ℝ :=
  fun ω =>
    posteriorVariance μ m KLimit ω +
      discrepancyTailAtZero μ m KLimit KCurrent ω *
        conditionalSquaredDiscrepancy μ m KLimit KCurrent ω

/-- The unweighted upper process `B_n` in the MSE hierarchy. -/
def fullMSEUpperBound (μ : Measure[m0] Ω) (m : MeasurableSpace Ω)
    (KLimit KCurrent : Ω → H) : Ω → ℝ :=
  fun ω =>
    posteriorVariance μ m KLimit ω +
      conditionalSquaredDiscrepancy μ m KLimit KCurrent ω

/-- Conditional MSE is non-negative, independently of fixedness. -/
theorem posteriorMSE_nonnegative (μ : Measure[m0] Ω) (m : MeasurableSpace Ω)
    (KLimit KCurrent : Ω → H) :
    0 ≤ᵐ[μ] posteriorMSE μ m KLimit KCurrent := by
  apply condExp_nonneg
  filter_upwards with ω
  exact sq_nonneg ‖KLimit ω - posteriorMean μ m KCurrent ω‖

/-- If the stage estimand is exactly the terminal estimand, its discrepancy is
zero and every member of the four-term MSE hierarchy is the same posterior
variance process. -/
theorem fixed_estimand_mse_collapse
    (μ : Measure[m0] Ω) (m : MeasurableSpace Ω)
    (KLimit KCurrent : Ω → H) (hFixed : KCurrent = KLimit) :
    posteriorMSE μ m KLimit KCurrent = posteriorVariance μ m KLimit ∧
      limitDiscrepancy KLimit KCurrent = 0 ∧
      discrepancyTailAtZero μ m KLimit KCurrent = 0 ∧
      conditionalSquaredDiscrepancy μ m KLimit KCurrent = 0 ∧
      weightedMSEUpperBound μ m KLimit KCurrent =
        posteriorVariance μ m KLimit ∧
      fullMSEUpperBound μ m KLimit KCurrent =
        posteriorVariance μ m KLimit := by
  subst KCurrent
  have hR : limitDiscrepancy KLimit KLimit = 0 := by
    funext ω
    simp [limitDiscrepancy]
  have hG : discrepancyTailAtZero μ m KLimit KLimit = 0 := by
    funext ω
    simp [discrepancyTailAtZero, limitDiscrepancy]
  have hD : conditionalSquaredDiscrepancy μ m KLimit KLimit = 0 := by
    funext ω
    simp [conditionalSquaredDiscrepancy, limitDiscrepancy]
  have hW : weightedMSEUpperBound μ m KLimit KLimit =
      posteriorVariance μ m KLimit := by
    funext ω
    simp [weightedMSEUpperBound, hG, hD]
  have hB : fullMSEUpperBound μ m KLimit KLimit =
      posteriorVariance μ m KLimit := by
    funext ω
    simp [fullMSEUpperBound, hD]
  exact ⟨rfl, hR, hG, hD, hW, hB⟩

/-- The supermartingale part of `msefixed`: fixedness identifies the MSE
process with terminal-target posterior variance, so fixed-target learning
transfers directly to MSE. -/
theorem fixed_estimand_mse_supermartingale
    (μ : Measure[m0] Ω)
    (ℱ : Filtration ℕ m0) (KLimit : Ω → H) (K : ℕ → Ω → H)
    (hFixed : ∀ n, K n = KLimit)
    (hFixedTargetLearning :
      Supermartingale (fun n => posteriorVariance μ (ℱ n) KLimit) ℱ μ) :
    Supermartingale (fun n => posteriorMSE μ (ℱ n) KLimit (K n)) ℱ μ := by
  simpa only [hFixed, posteriorVariance] using hFixedTargetLearning

/-- Bundled fixed-estimand corollary: the four quantities coincide at every
stage, and their common MSE process is a non-negative supermartingale. -/
theorem fixed_estimand_mse_corollary
    (μ : Measure[m0] Ω)
    (ℱ : Filtration ℕ m0) (KLimit : Ω → H) (K : ℕ → Ω → H)
    (hFixed : ∀ n, K n = KLimit)
    (hFixedTargetLearning :
      Supermartingale (fun n => posteriorVariance μ (ℱ n) KLimit) ℱ μ) :
    (∀ n,
      posteriorMSE μ (ℱ n) KLimit (K n) =
          posteriorVariance μ (ℱ n) KLimit ∧
        weightedMSEUpperBound μ (ℱ n) KLimit (K n) =
          posteriorVariance μ (ℱ n) KLimit ∧
        fullMSEUpperBound μ (ℱ n) KLimit (K n) =
          posteriorVariance μ (ℱ n) KLimit) ∧
      (∀ n, 0 ≤ᵐ[μ] posteriorMSE μ (ℱ n) KLimit (K n)) ∧
      Supermartingale (fun n => posteriorMSE μ (ℱ n) KLimit (K n)) ℱ μ := by
  refine ⟨?_, ?_, fixed_estimand_mse_supermartingale μ ℱ KLimit K
    hFixed hFixedTargetLearning⟩
  · intro n
    have hCollapse := fixed_estimand_mse_collapse
      μ (ℱ n) KLimit (K n) (hFixed n)
    exact ⟨hCollapse.1, hCollapse.2.2.2.2.1, hCollapse.2.2.2.2.2⟩
  · intro n
    exact posteriorMSE_nonnegative μ (ℱ n) KLimit (K n)

end FixedEstimandMSE

end

end SequentialLearning
