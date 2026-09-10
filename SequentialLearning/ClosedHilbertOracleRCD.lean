import SequentialLearning.ClosedBinaryOracleRCD
import SequentialLearning.HilbertOracleRCD

/-!
# Closed Hilbert binary-oracle interface

This file removes the implementation-level branch-`L²` premises from the
Hilbert oracle theorem.  Interior branch moments follow from the coarse RCD and
the master second moment; endpoint branches have zero weight.
-/

namespace SequentialLearning

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal MeasureTheory ProbabilityTheory RealInnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [MeasurableSpace H] [OpensMeasurableSpace H]
  [TopologicalSpace.SeparableSpace H]

omit [InnerProductSpace ℝ H] in
/-- Finite Fréchet risk at the origin is exactly the moment condition needed
for the identity map to belong to `L²`. -/
theorem memLp_id_two_of_frechetRisk_zero_lt_top
    (nu : Measure H) [IsProbabilityMeasure nu]
    (hFinite : frechetRisk nu 0 < ∞) :
    MemLp (id : H → H) 2 nu := by
  have hRoot : frechetRootRisk nu 0 < ∞ :=
    (frechetRisk_lt_top_iff_rootRisk_lt_top nu 0).1 hFinite
  refine ⟨stronglyMeasurable_id.aestronglyMeasurable, ?_⟩
  have hNorm : eLpNorm (id : H → H) 2 nu =
      eLpNorm (fun x : H ↦ ‖x‖) 2 nu := by
    apply eLpNorm_congr_norm_ae
    filter_upwards with x
    simp
  rw [hNorm]
  simpa only [frechetRootRisk, dist_zero_right] using hRoot

variable {Omega : Type*} {mOmega : MeasurableSpace Omega}

/-- Closed probabilistic Hilbert-oracle theorem.  The only probabilistic
assumptions are the two regular conditional laws and the master square moment;
no separate branch moment is exposed. -/
theorem actual_probabilistic_hilbert_oracle_closed
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (mSmall mLarge : MeasurableSpace Omega)
    (hSmallLarge : mSmall ≤ mLarge) (hLargeAmbient : mLarge ≤ mOmega)
    (A : Set Omega) (hA : MeasurableSet[mLarge] A)
    (K : Omega → H) (hK : Measurable[mOmega] K)
    (kappaA kappaAc : Kernel[mSmall] Omega H)
    [IsMarkovKernel kappaA] [IsMarkovKernel kappaAc]
    (hCoarseRCD : IsRegularConditionalLaw mu mSmall
      (hSmallLarge.trans hLargeAmbient) K
      (binaryEventMixtureKernel mu mSmall A kappaA kappaAc))
    (hFineRCD : IsRegularConditionalLaw mu mLarge hLargeAmbient K
      (binaryOracleKernel hSmallLarge A hA kappaA kappaAc))
    (s0 : H)
    (hMoment : Integrable (fun omega ↦ dist (K omega) s0 ^ 2) mu) :
    (binaryOracleFrechetGain mu mSmall mLarge hSmallLarge
        A hA kappaA kappaAc =ᵐ[mu]
      hilbertBinaryOracleRCDFormula mu mSmall A kappaA kappaAc) ∧
    StronglyMeasurable[mSmall]
      (binaryOracleFrechetGain mu mSmall mLarge hSmallLarge
        A hA kappaA kappaAc) ∧
    Integrable
      (binaryOracleFrechetGain mu mSmall mLarge hSmallLarge
        A hA kappaA kappaAc) mu ∧
    (0 ≤ᵐ[mu]
      binaryOracleFrechetGain mu mSmall mLarge hSmallLarge
        A hA kappaA kappaAc) ∧
    MeasurableSet[mSmall]
      (hilbertBinaryOracleRCDStrictEvent mu mSmall A kappaA kappaAc) ∧
    (∀ᵐ omega ∂mu,
      0 < binaryOracleFrechetGain mu mSmall mLarge hSmallLarge
          A hA kappaA kappaAc omega ↔
        omega ∈ hilbertBinaryOracleRCDStrictEvent
          mu mSmall A kappaA kappaAc) ∧
    ((0 < ∫ omega,
        binaryOracleFrechetGain mu mSmall mLarge hSmallLarge
          A hA kappaA kappaAc omega ∂mu) ↔
      0 < mu (hilbertBinaryOracleRCDStrictEvent
        mu mSmall A kappaA kappaAc)) ∧
    (∀ᵐ omega ∂mu,
      omega ∈ frechetBinaryOracleStrictEvent
          mu mSmall mLarge hSmallLarge A hA kappaA kappaAc ↔
        omega ∈ hilbertBinaryOracleRCDStrictEvent
          mu mSmall A kappaA kappaAc) := by
  let kappaCoarse : Kernel[mSmall] Omega H :=
    binaryEventMixtureKernel mu mSmall A kappaA kappaAc
  let p : Omega → ℝ := boundedBinaryEventProbability mu mSmall A
  let varianceA : Omega → ℝ := posteriorFrechetVarianceReal mSmall kappaA
  let varianceAc : Omega → ℝ := posteriorFrechetVarianceReal mSmall kappaAc
  let meanA : Omega → H := hilbertKernelMean mSmall kappaA
  let meanAc : Omega → H := hilbertKernelMean mSmall kappaAc
  let Gamma : Omega → ℝ := binaryOracleFrechetGain
    mu mSmall mLarge hSmallLarge A hA kappaA kappaAc
  let GapH : Omega → ℝ := randomActualHilbertOracleGap
    p varianceA varianceAc meanA meanAc
  let GH : Set Omega :=
    hilbertBinaryOracleRCDStrictEvent mu mSmall A kappaA kappaAc
  have hFrechet := actual_binary_oracle_frechet_refinement_closed
    mu mSmall mLarge hSmallLarge hLargeAmbient A hA K hK
      kappaA kappaAc hCoarseRCD hFineRCD s0 hMoment
  have hMixtureFinite : ∀ᵐ omega ∂mu,
      ∀ s : H, frechetRisk (kappaCoarse omega) s < ∞ :=
    posteriorFrechetRisk_finite_everywhere_ae
      mu mSmall (hSmallLarge.trans hLargeAmbient) K hK
        kappaCoarse hCoarseRCD s0 hMoment
  have hActualToHilbert :
      actualFrechetBinaryOracleGapRCD mu mSmall A kappaA kappaAc =ᵐ[mu]
        GapH := by
    filter_upwards [hMixtureFinite] with omega hFiniteOmega
    have hpBounds := boundedBinaryEventProbability_bounds mu mSmall A omega
    have hBoundA : BddBelow
        (Set.range (frechetRiskReal (kappaA omega))) :=
      ⟨0, by rintro _ ⟨s, rfl⟩; exact ENNReal.toReal_nonneg⟩
    have hBoundAc : BddBelow
        (Set.range (frechetRiskReal (kappaAc omega))) :=
      ⟨0, by rintro _ ⟨s, rfl⟩; exact ENNReal.toReal_nonneg⟩
    dsimp only [actualFrechetBinaryOracleGapRCD, GapH,
      randomActualHilbertOracleGap]
    change actualBinaryOracleGap (p omega)
        (frechetRiskReal (kappaA omega))
        (frechetRiskReal (kappaAc omega)) =
      actualBinaryOracleGap (p omega)
        (hilbertBranchRisk (varianceA omega) (meanA omega))
        (hilbertBranchRisk (varianceAc omega) (meanAc omega))
    by_cases hpZero : p omega = 0
    · rw [hpZero,
        actualBinaryOracleGap_zero_of_left_weight_zero
          (frechetRiskReal (kappaA omega))
          (frechetRiskReal (kappaAc omega)) hBoundA hBoundAc,
        actualHilbertBinaryOracleGap_formula]
      all_goals norm_num
    by_cases hpOne : p omega = 1
    · rw [hpOne,
        actualBinaryOracleGap_zero_of_right_weight_zero
          (frechetRiskReal (kappaA omega))
          (frechetRiskReal (kappaAc omega)) hBoundA hBoundAc,
        actualHilbertBinaryOracleGap_formula]
      all_goals norm_num
    have hpPositive : 0 < p omega :=
      lt_of_le_of_ne hpBounds.1 (Ne.symm hpZero)
    have hpLessOne : p omega < 1 := lt_of_le_of_ne hpBounds.2 hpOne
    have hMixtureZero : frechetRisk
        (binaryMixtureMeasure (p omega) (kappaA omega) (kappaAc omega)) 0 < ∞ := by
      have hs := hFiniteOmega 0
      change frechetRisk
        (binaryMixtureMeasure (p omega) (kappaA omega) (kappaAc omega)) 0 < ∞ at hs
      exact hs
    have hL2A : MemLp (id : H → H) 2 (kappaA omega) :=
      memLp_id_two_of_frechetRisk_zero_lt_top (kappaA omega)
        (frechetRisk_lt_top_left_of_binaryMixture
          (p omega) (kappaA omega) (kappaAc omega) 0
            hpPositive hMixtureZero)
    have hL2Ac : MemLp (id : H → H) 2 (kappaAc omega) :=
      memLp_id_two_of_frechetRisk_zero_lt_top (kappaAc omega)
        (frechetRisk_lt_top_right_of_binaryMixture
          (p omega) (kappaA omega) (kappaAc omega) 0
            hpLessOne hMixtureZero)
    have hRiskA : frechetRiskReal (kappaA omega) =
        hilbertBranchRisk (varianceA omega) (meanA omega) := by
      funext s
      exact frechetRiskReal_eq_kernelHilbertBranchRisk
        mSmall kappaA omega hL2A s
    have hRiskAc : frechetRiskReal (kappaAc omega) =
        hilbertBranchRisk (varianceAc omega) (meanAc omega) := by
      funext s
      exact frechetRiskReal_eq_kernelHilbertBranchRisk
        mSmall kappaAc omega hL2Ac s
    rw [hRiskA, hRiskAc]
  have hGammaHilbert : Gamma =ᵐ[mu] GapH :=
    hFrechet.1.trans hActualToHilbert
  have hp : ∀ omega, 0 ≤ p omega ∧ p omega ≤ 1 :=
    boundedBinaryEventProbability_bounds mu mSmall A
  have hpMeasurable : StronglyMeasurable[mSmall] p :=
    (measurable_boundedBinaryEventProbability mu mSmall A).stronglyMeasurable
  have hMeanAMeasurable : StronglyMeasurable[mSmall] meanA :=
    stronglyMeasurable_hilbertKernelMean mSmall kappaA
  have hMeanAcMeasurable : StronglyMeasurable[mSmall] meanAc :=
    stronglyMeasurable_hilbertKernelMean mSmall kappaAc
  have hGapFormula : GapH =
      hilbertBinaryOracleRCDFormula mu mSmall A kappaA kappaAc := by
    funext omega
    dsimp only [GapH, randomActualHilbertOracleGap,
      hilbertBinaryOracleRCDFormula, p, meanA, meanAc]
    exact actualHilbertBinaryOracleGap_formula
      (boundedBinaryEventProbability mu mSmall A omega)
      (varianceA omega) (varianceAc omega)
      (hilbertKernelMean mSmall kappaA omega)
      (hilbertKernelMean mSmall kappaAc omega)
      (hp omega).1 (hp omega).2
  have hGammaFormula : Gamma =ᵐ[mu]
      hilbertBinaryOracleRCDFormula mu mSmall A kappaA kappaAc := by
    filter_upwards [hGammaHilbert] with omega hGammaOmega
    rw [hGammaOmega]
    exact congrFun hGapFormula omega
  have hGHDef : GH = hilbertBinaryOracleStrictEvent p meanA meanAc := by rfl
  have hFormulaMeasurable : StronglyMeasurable[mSmall]
      (hilbertBinaryOracleRCDFormula mu mSmall A kappaA kappaAc) := by
    change StronglyMeasurable[mSmall] (fun omega ↦
      p omega * (1 - p omega) * ‖meanA omega - meanAc omega‖ ^ 2)
    exact (hpMeasurable.mul
      (stronglyMeasurable_const.sub hpMeasurable)).mul
        ((hMeanAMeasurable.sub hMeanAcMeasurable).norm.pow 2)
  have hGHPositive : ∀ omega,
      omega ∈ GH ↔
        0 < hilbertBinaryOracleRCDFormula
          mu mSmall A kappaA kappaAc omega := by
    intro omega
    rw [hGHDef]
    change (0 < p omega ∧ p omega < 1 ∧ meanA omega ≠ meanAc omega) ↔
      0 < p omega * (1 - p omega) * ‖meanA omega - meanAc omega‖ ^ 2
    exact (hilbertOracleGap_pos_iff
      (p omega) (meanA omega) (meanAc omega)
      (hp omega).1 (hp omega).2).symm
  have hGHMeasurable : MeasurableSet[mSmall] GH := by
    have hSet : GH = {omega |
        0 < hilbertBinaryOracleRCDFormula
          mu mSmall A kappaA kappaAc omega} := by
      ext omega
      exact hGHPositive omega
    rw [hSet]
    exact measurableSet_lt measurable_const hFormulaMeasurable.measurable
  have hStrict : ∀ᵐ omega ∂mu,
      0 < Gamma omega ↔ omega ∈ GH := by
    filter_upwards [hGammaFormula] with omega hGammaOmega
    rw [hGammaOmega]
    exact (hGHPositive omega).symm
  have hIntegralCriterion :
      (0 < ∫ omega, Gamma omega ∂mu) ↔ 0 < mu GH := by
    exact strict_oracle_gap_integral_pos_iff mu Gamma GH
      hFrechet.2.2.2.1 hFrechet.2.2.1 hStrict
  have hEventAgreement : ∀ᵐ omega ∂mu,
      omega ∈ frechetBinaryOracleStrictEvent
          mu mSmall mLarge hSmallLarge A hA kappaA kappaAc ↔
        omega ∈ GH := by
    filter_upwards [hStrict] with omega hStrictOmega
    exact hStrictOmega
  simpa only [Gamma, GH] using
    ⟨hGammaFormula, hFrechet.2.1, hFrechet.2.2.1,
      hFrechet.2.2.2.1, hGHMeasurable, hStrict,
      hIntegralCriterion, hEventAgreement⟩

end

end SequentialLearning
