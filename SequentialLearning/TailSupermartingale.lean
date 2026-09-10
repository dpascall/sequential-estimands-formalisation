import SequentialLearning.ConditionalStochasticDomination
import Mathlib.Probability.Martingale.Basic

/-!
# Tail supermartingale for a monotone discrepancy

This file formalises Corollary `tailsupermart`.  For a fixed threshold, the
result follows directly from indicator monotonicity and the tower property;
no regular conditional distribution is needed.
-/

namespace SequentialLearning

open Filter MeasureTheory Set
open scoped ENNReal MeasureTheory ProbabilityTheory

noncomputable section

section TailSupermartingale

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- Conditional upper-tail probability of a real-valued random variable. -/
def conditionalTailProbability (μ : Measure[m0] Ω)
    (m : MeasurableSpace Ω) (R : Ω → ℝ) (t : ℝ) : Ω → ℝ :=
  μ⟦{ω | t < R ω} | m⟧

/-- The indicator of a tail event is integrable under a probability measure
when the underlying random variable is measurable. -/
theorem integrable_tailIndicator
    (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (R : Ω → ℝ) (t : ℝ) (hR : Measurable[m0] R) :
    Integrable ({ω | t < R ω}.indicator fun _ => (1 : ℝ)) μ := by
  apply Integrable.indicator (integrable_const (1 : ℝ))
  exact hR measurableSet_Ioi

/-- At threshold zero, the general conditional-tail notation agrees exactly
with the discrepancy-tail notation used in the MSE hierarchy. -/
theorem conditionalTailProbability_zero_eq_discrepancyTailAtZero
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (μ : Measure[m0] Ω) (m : MeasurableSpace Ω)
    (KLimit KCurrent : Ω → H) :
    conditionalTailProbability μ m
        (limitDiscrepancy KLimit KCurrent) 0 =
      discrepancyTailAtZero μ m KLimit KCurrent := by
  rfl

/-- General two-information-state tail comparison.  If `RNew ≤ ROld`
almost surely and `mSmall ≤ mLarge`, conditioning the later tail probability
back down to `mSmall` is bounded by the earlier tail probability there. -/
theorem conditional_tail_refinement
    (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (mSmall mLarge : MeasurableSpace Ω)
    (hSmallLarge : mSmall ≤ mLarge) (hLarge : mLarge ≤ m0)
    (ROld RNew : Ω → ℝ) (t : ℝ)
    (hROld : Measurable[m0] ROld)
    (hRNew : Measurable[m0] RNew)
    (hMonotone : RNew ≤ᵐ[μ] ROld) :
    μ[conditionalTailProbability μ mLarge RNew t | mSmall] ≤ᵐ[μ]
      conditionalTailProbability μ mSmall ROld t := by
  let IOld : Ω → ℝ :=
    {ω | t < ROld ω}.indicator fun _ => (1 : ℝ)
  let INew : Ω → ℝ :=
    {ω | t < RNew ω}.indicator fun _ => (1 : ℝ)
  have hIOld : Integrable IOld μ := by
    simpa only [IOld] using integrable_tailIndicator μ ROld t hROld
  have hINew : Integrable INew μ := by
    simpa only [INew] using integrable_tailIndicator μ RNew t hRNew
  have hIndicators : INew ≤ᵐ[μ] IOld := by
    filter_upwards [hMonotone] with ω hOrderω
    by_cases hNewTail : t < RNew ω
    · have hOldTail : t < ROld ω := lt_of_lt_of_le hNewTail hOrderω
      simp [INew, IOld, hNewTail, hOldTail]
    · by_cases hOldTail : t < ROld ω <;>
        simp [INew, IOld, hNewTail, hOldTail]
  have hConditionalOrder :
      μ[INew | mSmall] ≤ᵐ[μ] μ[IOld | mSmall] :=
    condExp_mono hINew hIOld hIndicators
  have hTower :
      μ[μ[INew | mLarge] | mSmall] =ᵐ[μ] μ[INew | mSmall] :=
    condExp_condExp_of_le hSmallLarge hLarge
  filter_upwards [hTower, hConditionalOrder] with
    ω hTowerω hOrderω
  change μ[μ[INew | mLarge] | mSmall] ω ≤ μ[IOld | mSmall] ω
  rw [hTowerω]
  exact hOrderω

/-- Adjacent almost-sure decreases imply the corresponding pairwise order at
all later natural-numbered stages. -/
theorem ae_antitone_nat_of_succ
    (μ : Measure[m0] Ω) (R : ℕ → Ω → ℝ)
    (hStep : ∀ n, R (n + 1) ≤ᵐ[μ] R n) :
    ∀ ⦃n m : ℕ⦄, n ≤ m → R m ≤ᵐ[μ] R n := by
  intro n m hnm
  induction m, hnm using Nat.le_induction with
  | base => exact Filter.EventuallyLE.rfl
  | @succ m hnm ih =>
      exact (hStep m).trans ih

/-- Conditional tail probabilities lie in `[0,1]` almost surely. -/
theorem conditionalTailProbability_mem_Icc
    (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (R : Ω → ℝ) (t : ℝ) :
    0 ≤ᵐ[μ] conditionalTailProbability μ m R t ∧
      conditionalTailProbability μ m R t ≤ᵐ[μ] 1 := by
  constructor
  · apply condExp_nonneg
    filter_upwards with ω
    by_cases hω : t < R ω <;> simp [hω]
  · apply condExp_le_nonneg_const (μ := μ) (m := m) zero_le_one
    filter_upwards with ω
    by_cases hω : t < R ω <;> simp [hω]

/-- For a fixed threshold, the conditional tail probabilities of a monotone
discrepancy sequence form a `[0,1]`-valued supermartingale. -/
theorem conditional_tail_supermartingale
    (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (R : ℕ → Ω → ℝ) (t : ℝ)
    (hR : ∀ n, Measurable[m0] (R n))
    (hStep : ∀ n, R (n + 1) ≤ᵐ[μ] R n) :
    (∀ n, 0 ≤ᵐ[μ] conditionalTailProbability μ (ℱ n) (R n) t ∧
      conditionalTailProbability μ (ℱ n) (R n) t ≤ᵐ[μ] 1) ∧
    Supermartingale
      (fun n => conditionalTailProbability μ (ℱ n) (R n) t) ℱ μ := by
  have hPairwise := ae_antitone_nat_of_succ μ R hStep
  refine ⟨fun n => conditionalTailProbability_mem_Icc μ (ℱ n) (R n) t,
    ?_, ?_, ?_⟩
  · intro n
    exact stronglyMeasurable_condExp
  · intro i j hij
    exact conditional_tail_refinement μ (ℱ i) (ℱ j)
      (ℱ.mono hij) (ℱ.le j) (R i) (R j) t
      (hR i) (hR j) (hPairwise hij)
  · intro n
    exact integrable_condExp

end TailSupermartingale

end

end SequentialLearning
