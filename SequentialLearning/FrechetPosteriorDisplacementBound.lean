import SequentialLearning.PosteriorDisplacementInfrastructure
import SequentialLearning.PosteriorDisplacementBound

/-!
# Fréchet posterior-displacement bound

This file closes Result 17 by joining the metric/RCD part of Result 16 to the
deterministic conditional-expectation argument already formalised in
`PosteriorDisplacementBound`.
-/

namespace SequentialLearning

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

noncomputable section

variable {Omega S : Type*} {mOmega : MeasurableSpace Omega}
  [PseudoMetricSpace S] [MeasurableSpace S] [Nonempty S]
  [OpensMeasurableSpace S] [TopologicalSpace.SeparableSpace S]

/-- Separate second moments about a common reference point imply an
integrable squared displacement. -/
theorem integrable_pairSquaredDistance_of_reference
    (mu : Measure[mOmega] Omega) [IsFiniteMeasure mu]
    (X Y : Omega → S) (hX : Measurable[mOmega] X)
    (hY : Measurable[mOmega] Y) (s0 : S)
    (hXMoment : Integrable (fun omega => dist (X omega) s0 ^ 2) mu)
    (hYMoment : Integrable (fun omega => dist (Y omega) s0 ^ 2) mu) :
    Integrable (fun omega => dist (X omega) (Y omega) ^ 2) mu := by
  have hMajorant : Integrable
      (fun omega =>
        2 * dist (X omega) s0 ^ 2 + 2 * dist (Y omega) s0 ^ 2) mu :=
    (hXMoment.const_mul 2).add (hYMoment.const_mul 2)
  apply hMajorant.mono'
  · exact (hX.dist hY).pow_const 2 |>.aestronglyMeasurable
  · filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hTriangle : dist (X omega) (Y omega) ≤
        dist (X omega) s0 + dist (Y omega) s0 := by
      simpa only [dist_comm (Y omega) s0] using
        dist_triangle (X omega) s0 (Y omega)
    have hSquare : dist (X omega) (Y omega) ^ 2 ≤
        (dist (X omega) s0 + dist (Y omega) s0) ^ 2 :=
      (sq_le_sq₀ dist_nonneg (add_nonneg dist_nonneg dist_nonneg)).2 hTriangle
    nlinarith [sq_nonneg (dist (X omega) s0 - dist (Y omega) s0)]

/-- Result 17 in its full Fréchet/RCD form.  `U` and `V` are the old- and
new-estimand posterior Fréchet variances under the larger sigma-algebra, and
`Delta` is their completed-quotient posterior Wasserstein displacement.

The only isolated library-level input is `hW`, the Giry measurability of
`W₂` on the Polish completion. -/
theorem frechet_posterior_displacement_bound
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (mSmall mLarge : MeasurableSpace Omega)
    (hmLarge : mLarge ≤ mOmega)
    (X Y : Omega → S) (hX : Measurable[mOmega] X)
    (hY : Measurable[mOmega] Y)
    (rho : Kernel[mLarge,
      (inferInstance : MeasurableSpace (S × S))] Omega (S × S))
    [IsMarkovKernel rho]
    (hrho : IsRegularConditionalLaw mu mLarge hmLarge
      (fun omega => (X omega, Y omega)) rho)
    (s0 : S)
    (hXMoment : Integrable (fun omega => dist (X omega) s0 ^ 2) mu)
    (hYMoment : Integrable (fun omega => dist (Y omega) s0 ^ 2) mu)
    (hW : Wasserstein2LawMeasurable (PseudometricCompletion S)) :
    let U : Omega → ℝ := fun omega =>
      (frechetVariance ((Kernel.fst rho) omega)).toReal
    let V : Omega → ℝ := fun omega =>
      (frechetVariance ((Kernel.snd rho) omega)).toReal
    let Delta : Omega → ℝ := posteriorDisplacement rho
    (∀ᵐ omega ∂mu,
      |Real.sqrt (V omega) - Real.sqrt (U omega)| ≤ Delta omega) ∧
    (∀ᵐ omega ∂mu,
      V omega - U omega ≤
        Delta omega * (Delta omega + 2 * Real.sqrt (U omega))) ∧
    (displacementMovementTerm mu mSmall U V ≤ᵐ[mu]
      mu[(fun omega =>
        Delta omega ^ 2 + 2 * Delta omega * Real.sqrt (U omega)) |
          mSmall]) := by
  dsimp only
  have hFstRCD := regularConditionalLaw_fst_of_pair
    mu mLarge hmLarge X Y hX hY rho hrho
  have hSndRCD := regularConditionalLaw_snd_of_pair
    mu mLarge hmLarge X Y hX hY rho hrho
  have hFstWell := posteriorFrechet_finite_and_integrable
    mu mLarge hmLarge X hX (Kernel.fst rho) hFstRCD s0 hXMoment
  have hSndWell := posteriorFrechet_finite_and_integrable
    mu mLarge hmLarge Y hY (Kernel.snd rho) hSndRCD s0 hYMoment
  have hFstMoment : ∀ᵐ omega ∂mu,
      HasFiniteSecondMoment ((Kernel.fst rho) omega) := by
    filter_upwards [hFstWell.1] with omega hRisk
    exact ⟨s0, hRisk⟩
  have hSndMoment : ∀ᵐ omega ∂mu,
      HasFiniteSecondMoment ((Kernel.snd rho) omega) := by
    filter_upwards [hSndWell.1] with omega hRisk
    exact ⟨s0, hRisk⟩
  have hRoot := posterior_root_variance_bound_from_jointKernel
    rho mu hFstMoment hSndMoment
  have hMoveMoment : Integrable
      (fun omega => dist (X omega) (Y omega) ^ 2) mu :=
    integrable_pairSquaredDistance_of_reference
      mu X Y hX hY s0 hXMoment hYMoment
  have hDelta : MemLp (posteriorDisplacement rho) 2 mu :=
    posteriorDisplacement_memLp_two
      mu mLarge hmLarge X Y hX hY rho hrho hW hMoveMoment
  have hUNonnegative : 0 ≤ᵐ[mu]
      (fun omega => (frechetVariance ((Kernel.fst rho) omega)).toReal) :=
    Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg
  have hVNonnegative : 0 ≤ᵐ[mu]
      (fun omega => (frechetVariance ((Kernel.snd rho) omega)).toReal) :=
    Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg
  have hRootU : MemLp
      (fun omega => Real.sqrt
        (frechetVariance ((Kernel.fst rho) omega)).toReal) 2 mu :=
    memLp_two_sqrt_of_nonnegative_integrable mu
      (fun omega => (frechetVariance ((Kernel.fst rho) omega)).toReal)
      hUNonnegative hFstWell.2.2.2
  have hBoundInt : Integrable
      (fun omega =>
        posteriorDisplacement rho omega ^ 2 +
          2 * posteriorDisplacement rho omega *
            Real.sqrt (frechetVariance ((Kernel.fst rho) omega)).toReal) mu :=
    integrable_displacement_bound_of_memLp_two mu
      (fun omega => (frechetVariance ((Kernel.fst rho) omega)).toReal)
      (posteriorDisplacement rho) hDelta hRootU
  exact posterior_displacement_bound mu mSmall
    (fun omega => (frechetVariance ((Kernel.fst rho) omega)).toReal)
    (fun omega => (frechetVariance ((Kernel.snd rho) omega)).toReal)
    (posteriorDisplacement rho)
    hUNonnegative hVNonnegative hRoot
    hFstWell.2.2.2 hSndWell.2.2.2 hBoundInt

end

end SequentialLearning
