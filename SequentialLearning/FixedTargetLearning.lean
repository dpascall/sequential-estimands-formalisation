import SequentialLearning.FrechetRefinement
import Mathlib.Probability.Martingale.Basic

/-!
# Fixed-target learning

This file formalises the fixed-target learning corollary.  Along a filtration,
the posterior Frechet variance of one unchanged target is a nonnegative
supermartingale.  The one-step decrease is exactly the Frechet refinement gain
from `FrechetRefinement.lean`.
-/

namespace SequentialLearning

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal MeasureTheory ProbabilityTheory

noncomputable section

section FixedTargetLearning

variable {Omega S : Type*} {mOmega : MeasurableSpace Omega}
  [PseudoMetricSpace S] [MeasurableSpace S] [Nonempty S]
  [OpensMeasurableSpace S] [TopologicalSpace.SeparableSpace S]

/-- The posterior Frechet variance process for one fixed target, represented
at each filtration stage by a selected regular conditional-law kernel. -/
def fixedTargetPosteriorVariance
    (filtration : Filtration ℕ mOmega)
    (kappa : (n : ℕ) →
      Kernel[filtration n, (inferInstance : MeasurableSpace S)] Omega S) :
    ℕ → Omega → ℝ :=
  fun n => posteriorFrechetVarianceReal (filtration n) (kappa n)

omit [Nonempty S] [OpensMeasurableSpace S]
  [TopologicalSpace.SeparableSpace S] in
/-- Two choices of RCD kernels give indistinguishable fixed-target posterior
variance processes: because the time index is countable, all stagewise
version equalities hold on one common full-measure set. -/
theorem fixedTargetPosteriorVariance_ae_eq
    [MeasurableSpace.CountablyGenerated S]
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration ℕ mOmega)
    (K : Omega → S)
    (kappa eta : (n : ℕ) →
      Kernel[filtration n, (inferInstance : MeasurableSpace S)] Omega S)
    [∀ n, IsMarkovKernel (kappa n)] [∀ n, IsMarkovKernel (eta n)]
    (hkappa : ∀ n, IsRegularConditionalLaw mu (filtration n)
      (filtration.le n) K (kappa n))
    (heta : ∀ n, IsRegularConditionalLaw mu (filtration n)
      (filtration.le n) K (eta n)) :
    ∀ᵐ omega ∂mu, ∀ n,
      fixedTargetPosteriorVariance filtration kappa n omega =
        fixedTargetPosteriorVariance filtration eta n omega := by
  rw [ae_all_iff]
  intro n
  have hENN := posteriorFrechetVariance_ae_eq
    mu (filtration n) (filtration.le n) K
      (kappa n) (eta n) (hkappa n) (heta n)
  filter_upwards [hENN] with omega homega
  simp only [fixedTargetPosteriorVariance,
    posteriorFrechetVarianceReal]
  rw [homega]

/-- The refinement gain between any two stages of the fixed-target posterior
variance process.  The manuscript's one-step gain uses `i = n` and
`j = n + 1`. -/
def fixedTargetRefinementGain
    (mu : Measure[mOmega] Omega)
    (filtration : Filtration ℕ mOmega)
    (kappa : (n : ℕ) →
      Kernel[filtration n, (inferInstance : MeasurableSpace S)] Omega S)
    (i j : ℕ) : Omega → ℝ :=
  frechetRefinementGain mu (filtration i) (filtration j)
    (kappa i) (kappa j)

/-- Every stage of the fixed-target posterior variance process is adapted. -/
theorem stronglyAdapted_fixedTargetPosteriorVariance
    (filtration : Filtration ℕ mOmega)
    (kappa : (n : ℕ) →
      Kernel[filtration n, (inferInstance : MeasurableSpace S)] Omega S)
    [∀ n, IsMarkovKernel (kappa n)] :
    StronglyAdapted filtration
      (fixedTargetPosteriorVariance filtration kappa) := by
  intro n
  exact stronglyMeasurable_posteriorFrechetVarianceReal
    (filtration n) (kappa n)

/-- A single reference-centre moment makes every stage of the fixed-target
posterior variance process integrable. -/
theorem integrable_fixedTargetPosteriorVariance
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration ℕ mOmega)
    (K : Omega → S) (hK : Measurable[mOmega] K)
    (kappa : (n : ℕ) →
      Kernel[filtration n, (inferInstance : MeasurableSpace S)] Omega S)
    [∀ n, IsMarkovKernel (kappa n)]
    (hkappa : ∀ n, IsRegularConditionalLaw mu (filtration n)
      (filtration.le n) K (kappa n))
    (s0 : S)
    (hMoment : Integrable (fun omega => dist (K omega) s0 ^ 2) mu)
    (n : ℕ) :
    Integrable (fixedTargetPosteriorVariance filtration kappa n) mu := by
  have hBundle := posteriorFrechet_finite_and_integrable
    mu (filtration n) (filtration.le n) K hK
      (kappa n) (hkappa n) s0 hMoment
  change Integrable
    (fun omega => (frechetVariance (kappa n omega)).toReal) mu
  exact hBundle.2.2.2

omit [Nonempty S] [OpensMeasurableSpace S]
  [TopologicalSpace.SeparableSpace S] in
/-- Posterior Frechet variance is nonnegative at every stage.  This statement
is pointwise, and hence stronger than the almost-sure nonnegativity required
for a nonnegative supermartingale. -/
theorem fixedTargetPosteriorVariance_nonnegative
    (filtration : Filtration ℕ mOmega)
    (kappa : (n : ℕ) →
      Kernel[filtration n, (inferInstance : MeasurableSpace S)] Omega S)
    (n : ℕ) :
    ∀ omega, 0 ≤ fixedTargetPosteriorVariance filtration kappa n omega := by
  intro omega
  exact ENNReal.toReal_nonneg

/-- The all-pairs refinement statement.  For every `i ≤ j`, the conditional
fine-stage variance equals coarse variance minus the nonnegative refinement
gain, and is therefore at most the coarse variance. -/
theorem fixedTarget_refinement
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration ℕ mOmega)
    (K : Omega → S) (hK : Measurable[mOmega] K)
    (kappa : (n : ℕ) →
      Kernel[filtration n, (inferInstance : MeasurableSpace S)] Omega S)
    [∀ n, IsMarkovKernel (kappa n)]
    (hkappa : ∀ n, IsRegularConditionalLaw mu (filtration n)
      (filtration.le n) K (kappa n))
    (s0 : S)
    (hMoment : Integrable (fun omega => dist (K omega) s0 ^ 2) mu)
    (i j : ℕ) (hij : i ≤ j) :
    (0 ≤ᵐ[mu]
      fixedTargetRefinementGain mu filtration kappa i j) ∧
    (mu[fixedTargetPosteriorVariance filtration kappa j | filtration i]
        =ᵐ[mu]
      fun omega => fixedTargetPosteriorVariance filtration kappa i omega -
        fixedTargetRefinementGain mu filtration kappa i j omega) ∧
    (mu[fixedTargetPosteriorVariance filtration kappa j | filtration i]
        ≤ᵐ[mu]
      fixedTargetPosteriorVariance filtration kappa i) := by
  have hGain := frechetRefinementGain_wellPosed
    mu (filtration i) (filtration j) (filtration.mono hij)
      (filtration.le j) K hK (kappa i) (kappa j)
      (hkappa i) (hkappa j) s0 hMoment
  have hIdentity :
      mu[fixedTargetPosteriorVariance filtration kappa j | filtration i]
          =ᵐ[mu]
        fun omega => fixedTargetPosteriorVariance filtration kappa i omega -
          fixedTargetRefinementGain mu filtration kappa i j omega := by
    filter_upwards with omega
    simp only [fixedTargetPosteriorVariance,
      fixedTargetRefinementGain, frechetRefinementGain, refinementGain]
    ring
  have hOrder :
      mu[fixedTargetPosteriorVariance filtration kappa j | filtration i]
          ≤ᵐ[mu]
        fixedTargetPosteriorVariance filtration kappa i := by
    filter_upwards [hIdentity, hGain.2.2] with omega hEq hNonnegative
    rw [hEq]
    exact sub_le_self _ hNonnegative
  exact ⟨hGain.2.2, hIdentity, hOrder⟩

/-- Fixed-target learning.  Posterior Frechet variance is a nonnegative
supermartingale, and at every adjacent pair of stages its conditional decrease
is exactly the nonnegative Frechet refinement gain `Gamma`. -/
theorem fixedTarget_learning
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration ℕ mOmega)
    (K : Omega → S) (hK : Measurable[mOmega] K)
    (kappa : (n : ℕ) →
      Kernel[filtration n, (inferInstance : MeasurableSpace S)] Omega S)
    [∀ n, IsMarkovKernel (kappa n)]
    (hkappa : ∀ n, IsRegularConditionalLaw mu (filtration n)
      (filtration.le n) K (kappa n))
    (s0 : S)
    (hMoment : Integrable (fun omega => dist (K omega) s0 ^ 2) mu) :
    (∀ n, 0 ≤ᵐ[mu]
      fixedTargetPosteriorVariance filtration kappa n) ∧
    (∀ n,
      (0 ≤ᵐ[mu]
        fixedTargetRefinementGain mu filtration kappa n (n + 1)) ∧
      (mu[fixedTargetPosteriorVariance filtration kappa (n + 1) |
          filtration n] =ᵐ[mu]
        fun omega => fixedTargetPosteriorVariance filtration kappa n omega -
          fixedTargetRefinementGain mu filtration kappa n (n + 1) omega) ∧
      (mu[fixedTargetPosteriorVariance filtration kappa (n + 1) |
          filtration n] ≤ᵐ[mu]
        fixedTargetPosteriorVariance filtration kappa n)) ∧
    Supermartingale
      (fixedTargetPosteriorVariance filtration kappa) filtration mu := by
  have hNonnegative : ∀ n, 0 ≤ᵐ[mu]
      fixedTargetPosteriorVariance filtration kappa n := by
    intro n
    exact Filter.Eventually.of_forall
      (fixedTargetPosteriorVariance_nonnegative filtration kappa n)
  have hStep : ∀ n,
      (0 ≤ᵐ[mu]
        fixedTargetRefinementGain mu filtration kappa n (n + 1)) ∧
      (mu[fixedTargetPosteriorVariance filtration kappa (n + 1) |
          filtration n] =ᵐ[mu]
        fun omega => fixedTargetPosteriorVariance filtration kappa n omega -
          fixedTargetRefinementGain mu filtration kappa n (n + 1) omega) ∧
      (mu[fixedTargetPosteriorVariance filtration kappa (n + 1) |
          filtration n] ≤ᵐ[mu]
        fixedTargetPosteriorVariance filtration kappa n) := by
    intro n
    exact fixedTarget_refinement mu filtration K hK kappa hkappa
      s0 hMoment n (n + 1) (Nat.le_succ n)
  have hSupermartingale : Supermartingale
      (fixedTargetPosteriorVariance filtration kappa) filtration mu := by
    refine ⟨stronglyAdapted_fixedTargetPosteriorVariance
      filtration kappa, ?_, ?_⟩
    · intro i j hij
      exact (fixedTarget_refinement mu filtration K hK kappa hkappa
        s0 hMoment i j hij).2.2
    · intro n
      exact integrable_fixedTargetPosteriorVariance
        mu filtration K hK kappa hkappa s0 hMoment n
  exact ⟨hNonnegative, hStep, hSupermartingale⟩

end FixedTargetLearning

end

end SequentialLearning
