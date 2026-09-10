import SequentialLearning.TailSupermartingale

/-!
# Increasing loss functions of a monotone discrepancy

This file formalises Corollary `tailloss`.  It separates the order argument
from the two routes that supply integrability: boundedness of the loss on the
non-negative half-line, or integrability at the initial discrepancy.
-/

namespace SequentialLearning

open Filter MeasureTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

noncomputable section

section IncreasingLoss

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- Conditional expected transformed discrepancy. -/
def conditionalExpectedLoss (μ : Measure[m0] Ω)
    (m : MeasurableSpace Ω) (R : Ω → ℝ) (g : ℝ → ℝ) : Ω → ℝ :=
  μ[(fun ω => g (R ω)) | m]

/-- A monotone transform preserves an almost-sure order, and conditional
expectation preserves the resulting inequality when both transforms are
integrable. -/
theorem conditional_increasing_loss_order_of_integrable
    (μ : Measure[m0] Ω) (m : MeasurableSpace Ω)
    (ROld RNew : Ω → ℝ) (g : ℝ → ℝ)
    (hg : MonotoneOn g (Set.Ici 0))
    (hOldInt : Integrable (fun ω => g (ROld ω)) μ)
    (hNewInt : Integrable (fun ω => g (RNew ω)) μ)
    (hOldNonnegative : 0 ≤ᵐ[μ] ROld)
    (hNewNonnegative : 0 ≤ᵐ[μ] RNew)
    (hMonotone : RNew ≤ᵐ[μ] ROld) :
    conditionalExpectedLoss μ m RNew g ≤ᵐ[μ]
      conditionalExpectedLoss μ m ROld g := by
  apply condExp_mono hNewInt hOldInt
  filter_upwards [hOldNonnegative, hNewNonnegative, hMonotone] with
    ω hOldω hNewω hOrderω
  exact hg hNewω hOldω hOrderω

/-- A loss bounded on `[0,∞)` is integrable when evaluated at a measurable
non-negative random variable under a probability measure. -/
theorem integrable_increasing_loss_of_bounded_on_nonnegative
    (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (R : Ω → ℝ) (g : ℝ → ℝ)
    (hgMeas : Measurable g) (hR : Measurable[m0] R)
    (hRNonnegative : ∀ ω, 0 ≤ R ω)
    (hBounded : ∃ C : ℝ, ∀ r : ℝ, 0 ≤ r → |g r| ≤ C) :
    Integrable (fun ω => g (R ω)) μ := by
  obtain ⟨C, hC⟩ := hBounded
  apply Integrable.of_bound
    ((hgMeas.comp hR).aestronglyMeasurable) C
  filter_upwards with ω
  change |g (R ω)| ≤ C
  exact hC (R ω) (hRNonnegative ω)

/-- For a non-negative decreasing discrepancy sequence, integrability of the
increasing loss at stage zero propagates to every later stage.  The lower
bound `g(0)` is the ingredient that controls the negative part. -/
theorem integrable_increasing_loss_of_initial
    (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (R : ℕ → Ω → ℝ) (g : ℝ → ℝ)
    (hg : MonotoneOn g (Set.Ici 0)) (hgMeas : Measurable g)
    (hR : ∀ n, Measurable[m0] (R n))
    (hRNonnegative : ∀ n ω, 0 ≤ R n ω)
    (hStep : ∀ n, R (n + 1) ≤ᵐ[μ] R n)
    (hInitial : Integrable (fun ω => g (R 0 ω)) μ) :
    ∀ n, Integrable (fun ω => g (R n ω)) μ := by
  have hPairwise := ae_antitone_nat_of_succ μ R hStep
  intro n
  have hLower :
      (fun _ : Ω => g 0) ≤ᵐ[μ] fun ω => g (R n ω) := by
    filter_upwards with ω
    exact hg (by simp) (hRNonnegative n ω) (hRNonnegative n ω)
  have hUpper :
      (fun ω => g (R n ω)) ≤ᵐ[μ] fun ω => g (R 0 ω) := by
    filter_upwards [hPairwise (Nat.zero_le n)] with ω hOrderω
    exact hg (hRNonnegative n ω) (hRNonnegative 0 ω) hOrderω
  exact integrable_of_le_of_le
    ((hgMeas.comp (hR n)).aestronglyMeasurable)
    hLower hUpper (integrable_const (g 0)) hInitial

/-- Both integrability hypotheses in the manuscript imply integrability of
the transformed discrepancy at every stage. -/
theorem integrable_increasing_loss_all_stages
    (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (R : ℕ → Ω → ℝ) (g : ℝ → ℝ)
    (hg : MonotoneOn g (Set.Ici 0)) (hgMeas : Measurable g)
    (hR : ∀ n, Measurable[m0] (R n))
    (hRNonnegative : ∀ n ω, 0 ≤ R n ω)
    (hStep : ∀ n, R (n + 1) ≤ᵐ[μ] R n)
    (hIntegrability :
      (∃ C : ℝ, ∀ r : ℝ, 0 ≤ r → |g r| ≤ C) ∨
        Integrable (fun ω => g (R 0 ω)) μ) :
    ∀ n, Integrable (fun ω => g (R n ω)) μ := by
  rcases hIntegrability with hBounded | hInitial
  · intro n
    exact integrable_increasing_loss_of_bounded_on_nonnegative
      μ (R n) g hgMeas (hR n) (hRNonnegative n) hBounded
  · exact integrable_increasing_loss_of_initial
      μ R g hg hgMeas hR hRNonnegative hStep hInitial

/-- The increasing-loss corollary at a common information state. -/
theorem conditional_increasing_loss_order
    (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω)
    (R : ℕ → Ω → ℝ) (g : ℝ → ℝ)
    (hg : MonotoneOn g (Set.Ici 0)) (hgMeas : Measurable g)
    (hR : ∀ n, Measurable[m0] (R n))
    (hRNonnegative : ∀ n ω, 0 ≤ R n ω)
    (hStep : ∀ n, R (n + 1) ≤ᵐ[μ] R n)
    (hIntegrability :
      (∃ C : ℝ, ∀ r : ℝ, 0 ≤ r → |g r| ≤ C) ∨
        Integrable (fun ω => g (R 0 ω)) μ) :
    ∀ ⦃n k : ℕ⦄, n ≤ k →
      conditionalExpectedLoss μ m (R k) g ≤ᵐ[μ]
        conditionalExpectedLoss μ m (R n) g := by
  have hInt := integrable_increasing_loss_all_stages
    μ R g hg hgMeas hR hRNonnegative hStep hIntegrability
  have hPairwise := ae_antitone_nat_of_succ μ R hStep
  intro n k hnk
  exact conditional_increasing_loss_order_of_integrable
    μ m (R n) (R k) g hg (hInt n) (hInt k)
      (ae_of_all μ (hRNonnegative n)) (ae_of_all μ (hRNonnegative k))
      (hPairwise hnk)

/-- Two-information-state form used to obtain the dynamic result by the tower
property. -/
theorem conditional_increasing_loss_refinement
    (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (mSmall mLarge : MeasurableSpace Ω)
    (hSmallLarge : mSmall ≤ mLarge) (hLarge : mLarge ≤ m0)
    (ROld RNew : Ω → ℝ) (g : ℝ → ℝ)
    (hg : MonotoneOn g (Set.Ici 0))
    (hOldInt : Integrable (fun ω => g (ROld ω)) μ)
    (hNewInt : Integrable (fun ω => g (RNew ω)) μ)
    (hOldNonnegative : 0 ≤ᵐ[μ] ROld)
    (hNewNonnegative : 0 ≤ᵐ[μ] RNew)
    (hMonotone : RNew ≤ᵐ[μ] ROld) :
    μ[conditionalExpectedLoss μ mLarge RNew g | mSmall] ≤ᵐ[μ]
      conditionalExpectedLoss μ mSmall ROld g := by
  have hConditionalOrder := conditional_increasing_loss_order_of_integrable
    μ mSmall ROld RNew g hg hOldInt hNewInt
      hOldNonnegative hNewNonnegative hMonotone
  have hTower :
      μ[μ[(fun ω => g (RNew ω)) | mLarge] | mSmall] =ᵐ[μ]
        μ[(fun ω => g (RNew ω)) | mSmall] :=
    condExp_condExp_of_le hSmallLarge hLarge
  filter_upwards [hTower, hConditionalOrder] with
    ω hTowerω hOrderω
  change
    μ[μ[(fun ω => g (RNew ω)) | mLarge] | mSmall] ω ≤
      μ[(fun ω => g (ROld ω)) | mSmall] ω
  rw [hTowerω]
  exact hOrderω

/-- Along a filtration, posterior expected increasing loss is a
supermartingale under either of the manuscript's integrability conditions. -/
theorem conditional_increasing_loss_supermartingale
    (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0)
    (R : ℕ → Ω → ℝ) (g : ℝ → ℝ)
    (hg : MonotoneOn g (Set.Ici 0)) (hgMeas : Measurable g)
    (hR : ∀ n, Measurable[m0] (R n))
    (hRNonnegative : ∀ n ω, 0 ≤ R n ω)
    (hStep : ∀ n, R (n + 1) ≤ᵐ[μ] R n)
    (hIntegrability :
      (∃ C : ℝ, ∀ r : ℝ, 0 ≤ r → |g r| ≤ C) ∨
        Integrable (fun ω => g (R 0 ω)) μ) :
    Supermartingale
      (fun n => conditionalExpectedLoss μ (ℱ n) (R n) g) ℱ μ := by
  have hInt := integrable_increasing_loss_all_stages
    μ R g hg hgMeas hR hRNonnegative hStep hIntegrability
  have hPairwise := ae_antitone_nat_of_succ μ R hStep
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact stronglyMeasurable_condExp
  · intro i j hij
    exact conditional_increasing_loss_refinement
      μ (ℱ i) (ℱ j) (ℱ.mono hij) (ℱ.le j)
      (R i) (R j) g hg (hInt i) (hInt j)
      (ae_of_all μ (hRNonnegative i)) (ae_of_all μ (hRNonnegative j))
      (hPairwise hij)
  · intro n
    exact integrable_condExp

/-- Squaring is non-decreasing on the non-negative half-line. -/
theorem sq_monotoneOn_nonnegative :
    MonotoneOn (fun r : ℝ => r ^ 2) (Set.Ici 0) := by
  intro a ha b hb hab
  change 0 ≤ a at ha
  change 0 ≤ b at hb
  nlinarith

/-- The manuscript's principal increasing-loss example: the conditional
second moment of a monotone non-negative discrepancy is a supermartingale. -/
theorem conditional_squared_discrepancy_supermartingale_of_initial
    (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (R : ℕ → Ω → ℝ)
    (hR : ∀ n, Measurable[m0] (R n))
    (hRNonnegative : ∀ n ω, 0 ≤ R n ω)
    (hStep : ∀ n, R (n + 1) ≤ᵐ[μ] R n)
    (hInitial : Integrable (fun ω => R 0 ω ^ 2) μ) :
    Supermartingale
      (fun n => μ[(fun ω => R n ω ^ 2) | ℱ n]) ℱ μ := by
  simpa only [conditionalExpectedLoss] using
    conditional_increasing_loss_supermartingale
      μ ℱ R (fun r : ℝ => r ^ 2) sq_monotoneOn_nonnegative
      (by fun_prop) hR hRNonnegative hStep (Or.inr hInitial)

end IncreasingLoss

end

end SequentialLearning
