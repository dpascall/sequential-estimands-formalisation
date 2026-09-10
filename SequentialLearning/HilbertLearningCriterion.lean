import SequentialLearning.StrictOracleGap
import SequentialLearning.ExactCriterion
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Hilbert form of the exact one-step learning criterion

This file formalises Lemma `increment`, Theorem `hilbcriterion`, and the
resolved-increment corollary. The target movement is decomposed into its
posterior mean and its conditionally centred unresolved component.
-/

namespace SequentialLearning

open Filter MeasureTheory
open scoped ENNReal MeasureTheory ProbabilityTheory RealInnerProductSpace

noncomputable section

section HilbertLearningCriterion

variable {Ω H : Type*} {m0 : MeasurableSpace Ω}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Information about the old target revealed by the larger information
state. -/
def oldTargetInnovation (μ : Measure[m0] Ω)
    (mSmall mLarge : MeasurableSpace Ω) (KOld : Ω → H) : Ω → H :=
  posteriorMean μ mLarge KOld - posteriorMean μ mSmall KOld

/-- The part of target movement unresolved at the larger information state. -/
def unresolvedMovement (μ : Measure[m0] Ω)
    (mLarge : MeasurableSpace Ω) (KOld KNew : Ω → H) : Ω → H :=
  conditionallyCentered μ mLarge (KNew - KOld)

/-- Residual uncertainty about the old target after the larger information
state has been observed. -/
def oldTargetResidual (μ : Measure[m0] Ω)
    (mLarge : MeasurableSpace Ω) (KOld : Ω → H) : Ω → H :=
  conditionallyCentered μ mLarge KOld

/-- The conditional expectation of a conditionally centred integrable random
element is zero. -/
theorem condExp_conditionallyCentered_zero
    (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ m0)
    (X : Ω → H) (hX : Integrable X μ) :
    μ[conditionallyCentered μ m X | m] =ᵐ[μ] 0 := by
  have hSub :
      μ[X - posteriorMean μ m X | m] =ᵐ[μ]
        μ[X | m] - μ[posteriorMean μ m X | m] :=
    condExp_sub hX integrable_condExp m
  have hTower :
      μ[posteriorMean μ m X | m] =ᵐ[μ] posteriorMean μ m X := by
    simpa only [posteriorMean] using
      (condExp_condExp_of_le (μ := μ) (f := X)
        (m₁ := m) (m₂ := m) le_rfl hm)
  change μ[X - posteriorMean μ m X | m] =ᵐ[μ] 0
  refine hSub.trans ?_
  filter_upwards [hTower] with ω hTowerω
  simp only [Pi.sub_apply, Pi.zero_apply]
  rw [hTowerω]
  simp [posteriorMean]

/-- Residual-after-the-increment lemma. -/
theorem residual_after_increment
    (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (mSmall mLarge : MeasurableSpace Ω)
    (hSmallLarge : mSmall ≤ mLarge) (hLargeAmbient : mLarge ≤ m0)
    (KOld KNew : Ω → H)
    (hKOld : MemLp KOld 2 μ) (hKNew : MemLp KNew 2 μ) :
    (μ[oldTargetInnovation μ mSmall mLarge KOld | mSmall] =ᵐ[μ] 0) ∧
    (μ[unresolvedMovement μ mLarge KOld KNew | mLarge] =ᵐ[μ] 0) ∧
    (μ[oldTargetResidual μ mLarge KOld | mLarge] =ᵐ[μ] 0) ∧
    (conditionallyCentered μ mLarge KNew =ᵐ[μ]
      oldTargetResidual μ mLarge KOld +
        unresolvedMovement μ mLarge KOld KNew) := by
  have hOneTwo : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hKOldInt : Integrable KOld μ := hKOld.integrable hOneTwo
  have hKNewInt : Integrable KNew μ := hKNew.integrable hOneTwo
  have hDeltaInt : Integrable (KNew - KOld) μ := hKNewInt.sub hKOldInt
  have hInnovationSub :
      μ[posteriorMean μ mLarge KOld - posteriorMean μ mSmall KOld | mSmall]
          =ᵐ[μ]
        μ[posteriorMean μ mLarge KOld | mSmall] -
          μ[posteriorMean μ mSmall KOld | mSmall] :=
    condExp_sub integrable_condExp integrable_condExp mSmall
  have hTowerLarge :
      μ[posteriorMean μ mLarge KOld | mSmall] =ᵐ[μ]
        posteriorMean μ mSmall KOld := by
    simpa only [posteriorMean] using
      (condExp_condExp_of_le (μ := μ) (f := KOld)
        hSmallLarge hLargeAmbient)
  have hTowerSmall :
      μ[posteriorMean μ mSmall KOld | mSmall] =ᵐ[μ]
        posteriorMean μ mSmall KOld := by
    simpa only [posteriorMean] using
      (condExp_condExp_of_le (μ := μ) (f := KOld)
        (m₁ := mSmall) (m₂ := mSmall) le_rfl
          (hSmallLarge.trans hLargeAmbient))
  have hInnovationZero :
      μ[oldTargetInnovation μ mSmall mLarge KOld | mSmall] =ᵐ[μ] 0 := by
    change μ[posteriorMean μ mLarge KOld -
      posteriorMean μ mSmall KOld | mSmall] =ᵐ[μ] 0
    refine hInnovationSub.trans ?_
    filter_upwards [hTowerLarge, hTowerSmall] with ω hLargeω hSmallω
    simp only [Pi.sub_apply, Pi.zero_apply]
    rw [hLargeω, hSmallω]
    simp
  have hMovementZero :
      μ[unresolvedMovement μ mLarge KOld KNew | mLarge] =ᵐ[μ] 0 := by
    exact condExp_conditionallyCentered_zero μ mLarge hLargeAmbient
      (KNew - KOld) hDeltaInt
  have hResidualZero :
      μ[oldTargetResidual μ mLarge KOld | mLarge] =ᵐ[μ] 0 := by
    exact condExp_conditionallyCentered_zero μ mLarge hLargeAmbient
      KOld hKOldInt
  have hCondSub :
      μ[KNew - KOld | mLarge] =ᵐ[μ]
        μ[KNew | mLarge] - μ[KOld | mLarge] :=
    condExp_sub hKNewInt hKOldInt mLarge
  have hResidualIdentity :
      conditionallyCentered μ mLarge KNew =ᵐ[μ]
        oldTargetResidual μ mLarge KOld +
          unresolvedMovement μ mLarge KOld KNew := by
    filter_upwards [hCondSub] with ω hCondSubω
    change KNew ω - μ[KNew | mLarge] ω =
      (KOld ω - μ[KOld | mLarge] ω) +
        ((KNew ω - KOld ω) - μ[KNew - KOld | mLarge] ω)
    simp only [Pi.sub_apply] at hCondSubω
    rw [hCondSubω]
    abel
  exact ⟨hInnovationZero, hMovementZero, hResidualZero, hResidualIdentity⟩

/-- Conditional total variance in innovation form. The information gain
about the old target is the conditional second moment of the posterior-mean
innovation. -/
theorem posteriorVariance_refinement_hilbert
    (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (mSmall mLarge : MeasurableSpace Ω)
    (hSmallLarge : mSmall ≤ mLarge) (hLargeAmbient : mLarge ≤ m0)
    (KOld : Ω → H) (hKOld : MemLp KOld 2 μ) :
    posteriorVariance μ mSmall KOld =ᵐ[μ]
      fun ω =>
        μ[posteriorVariance μ mLarge KOld | mSmall] ω +
          μ[(fun a =>
            ‖oldTargetInnovation μ mSmall mLarge KOld a‖ ^ 2) |
              mSmall] ω := by
  let R : Ω → H := oldTargetResidual μ mLarge KOld
  let A : Ω → H := oldTargetInnovation μ mSmall mLarge KOld
  have hOneTwo : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hKOldInt : Integrable KOld μ := hKOld.integrable hOneTwo
  have hR : MemLp R 2 μ := by
    change MemLp (KOld - posteriorMean μ mLarge KOld) 2 μ
    exact hKOld.sub (hKOld.condExp hOneTwo)
  have hA : MemLp A 2 μ := by
    change MemLp
      (posteriorMean μ mLarge KOld - posteriorMean μ mSmall KOld) 2 μ
    exact (hKOld.condExp hOneTwo).sub (hKOld.condExp hOneTwo)
  have hRInt : Integrable R μ := hR.integrable hOneTwo
  have hALargeMeas : StronglyMeasurable[mLarge] A := by
    dsimp only [A, oldTargetInnovation]
    exact stronglyMeasurable_condExp.sub
      (stronglyMeasurable_condExp.mono hSmallLarge)
  have hCenteredDecomposition :
      conditionallyCentered μ mSmall KOld =ᵐ[μ] R + A := by
    have hTower :
        μ[posteriorMean μ mLarge KOld | mSmall] =ᵐ[μ]
          posteriorMean μ mSmall KOld := by
      simpa only [posteriorMean] using
        (condExp_condExp_of_le (μ := μ) (f := KOld)
          hSmallLarge hLargeAmbient)
    filter_upwards [hTower] with ω hTowerω
    change KOld ω - μ[KOld | mSmall] ω =
      (KOld ω - μ[KOld | mLarge] ω) +
        (μ[KOld | mLarge] ω - μ[KOld | mSmall] ω)
    abel
  have hCrossInt :
      Integrable (fun ω => inner ℝ (R ω) (A ω)) μ :=
    integrable_real_inner_of_memLp_two μ R A hR hA
  have hCrossPull :
      μ[(fun ω => inner ℝ (R ω) (A ω)) | mLarge] =ᵐ[μ]
        fun ω => inner ℝ (μ[R | mLarge] ω) (A ω) := by
    have hPull :=
      condExp_bilin_of_stronglyMeasurable_right
        (B := innerSL ℝ) hALargeMeas hCrossInt hRInt
    have hInnerInput :
        (fun ω => (innerSL ℝ) (R ω) (A ω)) =
          fun ω => inner ℝ (R ω) (A ω) := by
      funext ω
      rw [innerSL_apply_apply]
    have hInnerOutput :
        (fun ω => (innerSL ℝ) (μ[R | mLarge] ω) (A ω)) =
          fun ω => inner ℝ (μ[R | mLarge] ω) (A ω) := by
      funext ω
      rw [innerSL_apply_apply]
    rw [hInnerInput, hInnerOutput] at hPull
    exact hPull
  have hRZero : μ[R | mLarge] =ᵐ[μ] 0 := by
    exact condExp_conditionallyCentered_zero μ mLarge hLargeAmbient
      KOld hKOldInt
  have hCrossLargeZero :
      μ[(fun ω => inner ℝ (R ω) (A ω)) | mLarge] =ᵐ[μ] 0 := by
    refine hCrossPull.trans ?_
    filter_upwards [hRZero] with ω hRZeroω
    rw [hRZeroω]
    simp
  have hCrossSmallZero :
      μ[(fun ω => inner ℝ (R ω) (A ω)) | mSmall] =ᵐ[μ] 0 := by
    have hTower :=
      condExp_condExp_of_le (μ := μ)
        (f := fun ω => inner ℝ (R ω) (A ω))
        hSmallLarge hLargeAmbient
    have hCongr :
        μ[μ[(fun ω => inner ℝ (R ω) (A ω)) | mLarge] | mSmall]
            =ᵐ[μ] μ[(0 : Ω → ℝ) | mSmall] :=
      condExp_congr_ae hCrossLargeZero
    filter_upwards [hTower, hCongr] with ω hTowerω hCongrω
    rw [← hTowerω, hCongrω]
    simp
  have hRSqInt : Integrable (fun ω => ‖R ω‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hR.1).mp hR
  have hRTower :
      μ[(fun ω => ‖R ω‖ ^ 2) | mSmall] =ᵐ[μ]
        μ[posteriorVariance μ mLarge KOld | mSmall] := by
    have hTower :=
      condExp_condExp_of_le (μ := μ) (f := fun ω => ‖R ω‖ ^ 2)
        hSmallLarge hLargeAmbient
    simpa only [posteriorVariance, posteriorMSE, R, oldTargetResidual,
      conditionallyCentered, posteriorMean] using hTower.symm
  have hVarianceToSum :
      posteriorVariance μ mSmall KOld =ᵐ[μ]
        μ[(fun ω => ‖R ω + A ω‖ ^ 2) | mSmall] := by
    apply condExp_congr_ae
    filter_upwards [hCenteredDecomposition] with ω hω
    change ‖conditionallyCentered μ mSmall KOld ω‖ ^ 2 =
      ‖R ω + A ω‖ ^ 2
    rw [hω]
    simp only [Pi.add_apply]
  have hPolarisation := conditional_norm_add_sq μ mSmall R A hR hA
  refine hVarianceToSum.trans (hPolarisation.trans ?_)
  filter_upwards [hCrossSmallZero, hRTower] with ω hCrossω hRTowerω
  rw [hCrossω, hRTowerω]
  simp only [Pi.zero_apply, mul_zero, add_zero]
  rfl

/-- The part of the next-stage variance change attributable to unresolved
target movement, expressed as a squared norm plus its covariance with the old
target residual. -/
def hilbertMovementIntegrand (μ : Measure[m0] Ω)
    (mLarge : MeasurableSpace Ω) (KOld KNew : Ω → H) : Ω → ℝ :=
  fun ω =>
    ‖unresolvedMovement μ mLarge KOld KNew ω‖ ^ 2 +
      2 * inner ℝ (oldTargetResidual μ mLarge KOld ω)
        (unresolvedMovement μ mLarge KOld KNew ω)

/-- At the larger information state, replacing the old target by the new
target changes posterior variance by the conditional expectation of the
Hilbert movement integrand. -/
theorem posteriorVariance_after_movement_hilbert
    (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (mSmall mLarge : MeasurableSpace Ω)
    (hSmallLarge : mSmall ≤ mLarge) (hLargeAmbient : mLarge ≤ m0)
    (KOld KNew : Ω → H)
    (hKOld : MemLp KOld 2 μ) (hKNew : MemLp KNew 2 μ) :
    posteriorVariance μ mLarge KNew =ᵐ[μ]
      fun ω =>
        posteriorVariance μ mLarge KOld ω +
          μ[hilbertMovementIntegrand μ mLarge KOld KNew | mLarge] ω := by
  let R : Ω → H := oldTargetResidual μ mLarge KOld
  let W : Ω → H := unresolvedMovement μ mLarge KOld KNew
  have hOneTwo : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hR : MemLp R 2 μ := by
    change MemLp (KOld - posteriorMean μ mLarge KOld) 2 μ
    exact hKOld.sub (hKOld.condExp hOneTwo)
  have hDelta : MemLp (KNew - KOld) 2 μ := hKNew.sub hKOld
  have hW : MemLp W 2 μ := by
    change MemLp ((KNew - KOld) - posteriorMean μ mLarge (KNew - KOld)) 2 μ
    exact hDelta.sub (hDelta.condExp hOneTwo)
  have hResidualIdentity :=
    (residual_after_increment μ mSmall mLarge hSmallLarge hLargeAmbient
      KOld KNew hKOld hKNew).2.2.2
  have hVarianceToSum :
      posteriorVariance μ mLarge KNew =ᵐ[μ]
        μ[(fun ω => ‖R ω + W ω‖ ^ 2) | mLarge] := by
    apply condExp_congr_ae
    filter_upwards [hResidualIdentity] with ω hω
    change ‖conditionallyCentered μ mLarge KNew ω‖ ^ 2 =
      ‖R ω + W ω‖ ^ 2
    rw [hω]
    simp only [Pi.add_apply, R, W]
  have hPolarisation := conditional_norm_add_sq μ mLarge R W hR hW
  have hWSqInt : Integrable (fun ω => ‖W ω‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hW.1).mp hW
  have hCrossInt : Integrable (fun ω => inner ℝ (R ω) (W ω)) μ :=
    integrable_real_inner_of_memLp_two μ R W hR hW
  have hMovementCond :
      μ[hilbertMovementIntegrand μ mLarge KOld KNew | mLarge] =ᵐ[μ]
        fun ω =>
          μ[(fun a => ‖W a‖ ^ 2) | mLarge] ω +
            2 * μ[(fun a => inner ℝ (R a) (W a)) | mLarge] ω := by
    have hAdd := condExp_add hWSqInt (hCrossInt.smul (2 : ℝ)) mLarge
    have hSmul := condExp_smul (μ := μ) (2 : ℝ)
      (fun a => inner ℝ (R a) (W a)) mLarge
    filter_upwards [hAdd, hSmul] with ω hAddω hSmulω
    change μ[(fun a => ‖W a‖ ^ 2 + 2 * inner ℝ (R a) (W a)) |
      mLarge] ω = _
    rw [show (fun a => ‖W a‖ ^ 2 + 2 * inner ℝ (R a) (W a)) =
        (fun a => ‖W a‖ ^ 2) +
          (2 : ℝ) • (fun a => inner ℝ (R a) (W a)) by
      funext a
      simp [smul_eq_mul]]
    rw [hAddω]
    simp only [Pi.add_apply]
    rw [hSmulω]
    simp [Pi.smul_apply, smul_eq_mul]
  refine hVarianceToSum.trans (hPolarisation.trans ?_)
  filter_upwards [hMovementCond] with ω hMovementω
  rw [hMovementω]
  simp only [posteriorVariance, posteriorMSE, R, oldTargetResidual,
    conditionallyCentered]
  ring

/-- Manuscript information term `J`: old-target posterior variance resolved by
the information refinement. -/
def hilbertInformationTerm (μ : Measure[m0] Ω)
    (mSmall mLarge : MeasurableSpace Ω) (KOld : Ω → H) : Ω → ℝ :=
  fun ω =>
    informationGain (posteriorVariance μ mSmall KOld ω)
      (μ[posteriorVariance μ mLarge KOld | mSmall] ω)

/-- Manuscript movement term `S`: the posterior-variance cost of changing the
target, evaluated from the smaller information state. -/
def hilbertEstimandMovementTerm (μ : Measure[m0] Ω)
    (mSmall mLarge : MeasurableSpace Ω)
    (KOld KNew : Ω → H) : Ω → ℝ :=
  fun ω =>
    estimandMovement
      (μ[posteriorVariance μ mLarge KNew | mSmall] ω)
      (μ[posteriorVariance μ mLarge KOld | mSmall] ω)

/-- Hilbert form of the exact one-step learning criterion. It identifies `J`
with the conditional squared posterior-mean innovation, identifies `S` with
the conditional unresolved-movement expression, and states the resulting
necessary-and-sufficient learning inequality. -/
theorem hilbert_one_step_learning_criterion
    (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (mSmall mLarge : MeasurableSpace Ω)
    (hSmallLarge : mSmall ≤ mLarge) (hLargeAmbient : mLarge ≤ m0)
    (KOld KNew : Ω → H)
    (hKOld : MemLp KOld 2 μ) (hKNew : MemLp KNew 2 μ) :
    (hilbertInformationTerm μ mSmall mLarge KOld =ᵐ[μ]
      μ[(fun ω =>
        ‖oldTargetInnovation μ mSmall mLarge KOld ω‖ ^ 2) | mSmall]) ∧
    (hilbertEstimandMovementTerm μ mSmall mLarge KOld KNew =ᵐ[μ]
      μ[hilbertMovementIntegrand μ mLarge KOld KNew | mSmall]) ∧
    (∀ᵐ ω ∂μ,
      μ[posteriorVariance μ mLarge KNew | mSmall] ω ≤
          posteriorVariance μ mSmall KOld ω ↔
        μ[hilbertMovementIntegrand μ mLarge KOld KNew | mSmall] ω ≤
          μ[(fun a =>
            ‖oldTargetInnovation μ mSmall mLarge KOld a‖ ^ 2) |
              mSmall] ω) := by
  let Q : Ω → ℝ := hilbertMovementIntegrand μ mLarge KOld KNew
  have hOneTwo : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hR : MemLp (oldTargetResidual μ mLarge KOld) 2 μ := by
    change MemLp (KOld - posteriorMean μ mLarge KOld) 2 μ
    exact hKOld.sub (hKOld.condExp hOneTwo)
  have hDelta : MemLp (KNew - KOld) 2 μ := hKNew.sub hKOld
  have hW : MemLp (unresolvedMovement μ mLarge KOld KNew) 2 μ := by
    change MemLp ((KNew - KOld) - posteriorMean μ mLarge (KNew - KOld)) 2 μ
    exact hDelta.sub (hDelta.condExp hOneTwo)
  have hWSqInt : Integrable
      (fun ω => ‖unresolvedMovement μ mLarge KOld KNew ω‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hW.1).mp hW
  have hCrossInt : Integrable
      (fun ω => inner ℝ (oldTargetResidual μ mLarge KOld ω)
        (unresolvedMovement μ mLarge KOld KNew ω)) μ :=
    integrable_real_inner_of_memLp_two μ
      (oldTargetResidual μ mLarge KOld)
      (unresolvedMovement μ mLarge KOld KNew) hR hW
  have hQInt : Integrable Q μ := by
    dsimp only [Q, hilbertMovementIntegrand]
    exact hWSqInt.add (hCrossInt.smul (2 : ℝ))
  have hRefinement := posteriorVariance_refinement_hilbert μ
    mSmall mLarge hSmallLarge hLargeAmbient KOld hKOld
  have hJ :
      hilbertInformationTerm μ mSmall mLarge KOld =ᵐ[μ]
        μ[(fun ω =>
          ‖oldTargetInnovation μ mSmall mLarge KOld ω‖ ^ 2) | mSmall] := by
    filter_upwards [hRefinement] with ω hRefinementω
    dsimp only [hilbertInformationTerm, informationGain]
    rw [hRefinementω]
    ring
  have hMovement := posteriorVariance_after_movement_hilbert μ
    mSmall mLarge hSmallLarge hLargeAmbient KOld KNew hKOld hKNew
  have hLargeDifference :
      (fun ω => posteriorVariance μ mLarge KNew ω -
        posteriorVariance μ mLarge KOld ω) =ᵐ[μ]
          μ[Q | mLarge] := by
    filter_upwards [hMovement] with ω hMovementω
    dsimp only [Q]
    rw [hMovementω]
    ring
  have hDifferenceCongr :
      μ[(fun ω => posteriorVariance μ mLarge KNew ω -
        posteriorVariance μ mLarge KOld ω) | mSmall] =ᵐ[μ]
          μ[μ[Q | mLarge] | mSmall] :=
    condExp_congr_ae hLargeDifference
  have hDifferenceSub :
      μ[(fun ω => posteriorVariance μ mLarge KNew ω -
        posteriorVariance μ mLarge KOld ω) | mSmall] =ᵐ[μ]
          μ[posteriorVariance μ mLarge KNew | mSmall] -
            μ[posteriorVariance μ mLarge KOld | mSmall] :=
    condExp_sub integrable_condExp integrable_condExp mSmall
  have hQTower : μ[μ[Q | mLarge] | mSmall] =ᵐ[μ] μ[Q | mSmall] :=
    condExp_condExp_of_le hSmallLarge hLargeAmbient
  have hS :
      hilbertEstimandMovementTerm μ mSmall mLarge KOld KNew =ᵐ[μ]
        μ[Q | mSmall] := by
    filter_upwards [hDifferenceCongr, hDifferenceSub, hQTower] with
      ω hCongrω hSubω hTowerω
    dsimp only [hilbertEstimandMovementTerm, estimandMovement]
    simp only [Pi.sub_apply] at hSubω
    rw [← hSubω, hCongrω, hTowerω]
  refine ⟨hJ, ?_, ?_⟩
  · simpa only [Q] using hS
  filter_upwards [hJ, hS] with ω hJω hSω
  have hCriterion := exact_learning_iff
    (posteriorVariance μ mSmall KOld ω)
    (μ[posteriorVariance μ mLarge KOld | mSmall] ω)
    (μ[posteriorVariance μ mLarge KNew | mSmall] ω)
  dsimp only [hilbertInformationTerm] at hJω
  dsimp only [hilbertEstimandMovementTerm] at hSω
  rw [hJω, hSω] at hCriterion
  simpa only [Q, ge_iff_le] using hCriterion

/-- If the target increment is already resolved at the larger information
state, its unresolved component and hence `S` vanish. The exact criterion
then guarantees one-step learning. -/
theorem resolved_increment_learning
    (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (mSmall mLarge : MeasurableSpace Ω)
    (hSmallLarge : mSmall ≤ mLarge) (hLargeAmbient : mLarge ≤ m0)
    (KOld KNew : Ω → H)
    (hKOld : MemLp KOld 2 μ) (hKNew : MemLp KNew 2 μ)
    (hIncrementMeasurable : StronglyMeasurable[mLarge] (KNew - KOld)) :
    (hilbertEstimandMovementTerm μ mSmall mLarge KOld KNew =ᵐ[μ] 0) ∧
    (μ[posteriorVariance μ mLarge KNew | mSmall] =ᵐ[μ]
      fun ω => posteriorVariance μ mSmall KOld ω -
        hilbertInformationTerm μ mSmall mLarge KOld ω) ∧
    (μ[posteriorVariance μ mLarge KNew | mSmall] ≤ᵐ[μ]
      posteriorVariance μ mSmall KOld) := by
  let Q : Ω → ℝ := hilbertMovementIntegrand μ mLarge KOld KNew
  have hOneTwo : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hIncrementInt : Integrable (KNew - KOld) μ :=
    (hKNew.sub hKOld).integrable hOneTwo
  have hIncrementCond :
      μ[KNew - KOld | mLarge] = KNew - KOld :=
    condExp_of_stronglyMeasurable hLargeAmbient
      hIncrementMeasurable hIncrementInt
  have hWZero :
      unresolvedMovement μ mLarge KOld KNew = 0 := by
    funext ω
    dsimp only [unresolvedMovement, conditionallyCentered, posteriorMean]
    rw [hIncrementCond]
    simp
  have hQZero : Q = 0 := by
    funext ω
    dsimp only [Q, hilbertMovementIntegrand]
    rw [hWZero]
    simp
  have hCriterion := hilbert_one_step_learning_criterion μ
    mSmall mLarge hSmallLarge hLargeAmbient KOld KNew hKOld hKNew
  have hSFormula := hCriterion.2.1
  have hSZero :
      hilbertEstimandMovementTerm μ mSmall mLarge KOld KNew =ᵐ[μ] 0 := by
    have hQCondZero : μ[Q | mSmall] = 0 := by
      rw [hQZero]
      simp
    simpa only [Q, hQCondZero] using hSFormula
  have hInnovationNonnegative :
      (0 : Ω → ℝ) ≤ᵐ[μ]
        μ[(fun a =>
          ‖oldTargetInnovation μ mSmall mLarge KOld a‖ ^ 2) | mSmall] := by
    apply condExp_nonneg
    exact Filter.Eventually.of_forall (fun ω => sq_nonneg _)
  have hQCondZero : μ[Q | mSmall] = 0 := by
    rw [hQZero]
    simp
  have hLearning :
      μ[posteriorVariance μ mLarge KNew | mSmall] ≤ᵐ[μ]
        posteriorVariance μ mSmall KOld := by
    filter_upwards [hCriterion.2.2, hInnovationNonnegative] with
      ω hCriterionω hNonnegativeω
    apply hCriterionω.mpr
    simpa only [Q, hQCondZero, Pi.zero_apply] using hNonnegativeω
  have hExactResolved :
      μ[posteriorVariance μ mLarge KNew | mSmall] =ᵐ[μ]
        fun ω => posteriorVariance μ mSmall KOld ω -
          hilbertInformationTerm μ mSmall mLarge KOld ω := by
    filter_upwards [hSZero] with ω hSZeroω
    dsimp only [hilbertEstimandMovementTerm, estimandMovement] at hSZeroω
    dsimp only [hilbertInformationTerm, informationGain]
    have hExpectedEqual :
        μ[posteriorVariance μ mLarge KNew | mSmall] ω =
          μ[posteriorVariance μ mLarge KOld | mSmall] ω :=
      sub_eq_zero.mp hSZeroω
    rw [hExpectedEqual]
    ring
  exact ⟨hSZero, hExactResolved, hLearning⟩

end HilbertLearningCriterion

end

end SequentialLearning
