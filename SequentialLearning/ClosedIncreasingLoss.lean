import SequentialLearning.IncreasingLoss

/-!
# Increasing losses without a global measurability assumption

The manuscript only assumes that the loss `g : ℝ → ℝ` is non-decreasing on
`[0,∞)`. Since every discrepancy is non-negative, values of `g` on the
negative half-line are irrelevant. Replacing `g` by `r ↦ g (max r 0)` gives a
globally monotone, hence Borel measurable, function which agrees with `g` at
every discrepancy. The wrappers below use that extension internally and
expose exactly the manuscript hypotheses.
-/

namespace SequentialLearning

open Filter MeasureTheory Set
open scoped ENNReal MeasureTheory ProbabilityTheory

noncomputable section

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- Extend a loss from the non-negative half-line by keeping it constant to
the left of zero. -/
def nonnegativeExtension (g : ℝ → ℝ) (r : ℝ) : ℝ :=
  g (max r 0)

/-- Monotonicity on `[0,∞)` makes the constant-left extension globally
monotone. -/
theorem monotone_nonnegativeExtension (g : ℝ → ℝ)
    (hg : MonotoneOn g (Set.Ici 0)) :
    Monotone (nonnegativeExtension g) := by
  intro a b hab
  apply hg
  · exact Set.mem_Ici.mpr (le_max_right a 0)
  · exact Set.mem_Ici.mpr (le_max_right b 0)
  · exact max_le_max hab le_rfl

/-- The extension used by the closed increasing-loss wrappers is Borel
measurable, without any assumption on `g` below zero. -/
theorem measurable_nonnegativeExtension (g : ℝ → ℝ)
    (hg : MonotoneOn g (Set.Ici 0)) :
    Measurable (nonnegativeExtension g) :=
  (monotone_nonnegativeExtension g hg).measurable

/-- Manuscript-level common-information-state increasing-loss order. Global
measurability of `g` is derived internally after replacing its irrelevant
negative-half-line values. -/
theorem conditional_increasing_loss_order_nonnegative
    (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω)
    (R : ℕ → Ω → ℝ) (g : ℝ → ℝ)
    (hg : MonotoneOn g (Set.Ici 0))
    (hR : ∀ n, Measurable[m0] (R n))
    (hRNonnegative : ∀ n ω, 0 ≤ R n ω)
    (hStep : ∀ n, R (n + 1) ≤ᵐ[μ] R n)
    (hIntegrability :
      (∃ C : ℝ, ∀ r : ℝ, 0 ≤ r → |g r| ≤ C) ∨
        Integrable (fun ω => g (R 0 ω)) μ) :
    ∀ ⦃n k : ℕ⦄, n ≤ k →
      conditionalExpectedLoss μ m (R k) g ≤ᵐ[μ]
        conditionalExpectedLoss μ m (R n) g := by
  let gPlus : ℝ → ℝ := nonnegativeExtension g
  have hgPlus : MonotoneOn gPlus (Set.Ici 0) :=
    (monotone_nonnegativeExtension g hg).monotoneOn (Set.Ici 0)
  have hgPlusMeas : Measurable gPlus :=
    measurable_nonnegativeExtension g hg
  have hIntegrabilityPlus :
      (∃ C : ℝ, ∀ r : ℝ, 0 ≤ r → |gPlus r| ≤ C) ∨
        Integrable (fun ω => gPlus (R 0 ω)) μ := by
    rcases hIntegrability with hBounded | hInitial
    · left
      obtain ⟨C, hC⟩ := hBounded
      refine ⟨C, ?_⟩
      intro r hr
      simpa [gPlus, nonnegativeExtension, max_eq_left hr] using hC r hr
    · right
      simpa [gPlus, nonnegativeExtension, hRNonnegative] using hInitial
  have hOrder := conditional_increasing_loss_order
    μ m R gPlus hgPlus hgPlusMeas hR hRNonnegative hStep
      hIntegrabilityPlus
  intro n k hnk
  simpa [conditionalExpectedLoss, gPlus, nonnegativeExtension,
    hRNonnegative] using hOrder hnk

/-- Manuscript-level dynamic increasing-loss result. The process is a
supermartingale assuming only that `g` is non-decreasing on `[0,∞)` and one
of the manuscript's two integrability conditions. -/
theorem conditional_increasing_loss_supermartingale_nonnegative
    (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0)
    (R : ℕ → Ω → ℝ) (g : ℝ → ℝ)
    (hg : MonotoneOn g (Set.Ici 0))
    (hR : ∀ n, Measurable[m0] (R n))
    (hRNonnegative : ∀ n ω, 0 ≤ R n ω)
    (hStep : ∀ n, R (n + 1) ≤ᵐ[μ] R n)
    (hIntegrability :
      (∃ C : ℝ, ∀ r : ℝ, 0 ≤ r → |g r| ≤ C) ∨
        Integrable (fun ω => g (R 0 ω)) μ) :
    Supermartingale
      (fun n => conditionalExpectedLoss μ (ℱ n) (R n) g) ℱ μ := by
  let gPlus : ℝ → ℝ := nonnegativeExtension g
  have hgPlus : MonotoneOn gPlus (Set.Ici 0) :=
    (monotone_nonnegativeExtension g hg).monotoneOn (Set.Ici 0)
  have hgPlusMeas : Measurable gPlus :=
    measurable_nonnegativeExtension g hg
  have hIntegrabilityPlus :
      (∃ C : ℝ, ∀ r : ℝ, 0 ≤ r → |gPlus r| ≤ C) ∨
        Integrable (fun ω => gPlus (R 0 ω)) μ := by
    rcases hIntegrability with hBounded | hInitial
    · left
      obtain ⟨C, hC⟩ := hBounded
      refine ⟨C, ?_⟩
      intro r hr
      simpa [gPlus, nonnegativeExtension, max_eq_left hr] using hC r hr
    · right
      simpa [gPlus, nonnegativeExtension, hRNonnegative] using hInitial
  simpa [conditionalExpectedLoss, gPlus, nonnegativeExtension,
    hRNonnegative] using
    (conditional_increasing_loss_supermartingale
      μ ℱ R gPlus hgPlus hgPlusMeas hR hRNonnegative hStep
        hIntegrabilityPlus)

end

end SequentialLearning
