import SequentialLearning.BinaryOracleRCD
import SequentialLearning.ProbabilisticHilbertOracle
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# The binary-oracle formula for Hilbert-valued regular conditional laws

This file closes the probabilistic Hilbert specialization of the binary-oracle
result. It first proves the Hilbert Frechet-risk decomposition for an actual
square-integrable probability law and identifies its Bochner mean as the
Frechet minimizer. It then applies that decomposition to the two branch kernels
of `BinaryOracleRCD`, obtaining the exact between-branch formula for the actual
refinement gain, its measurable strictness event, and the positive-expectation
criterion.
-/

namespace SequentialLearning

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal MeasureTheory ProbabilityTheory RealInnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [MeasurableSpace H] [OpensMeasurableSpace H]
  [TopologicalSpace.SeparableSpace H]

def hilbertMeasureMean (nu : Measure H) : H :=
  ∫ x, x ∂nu

def hilbertMeasureVarianceReal (nu : Measure H) : ℝ :=
  ∫ x, ‖x - hilbertMeasureMean nu‖ ^ 2 ∂nu

omit [OpensMeasurableSpace H] [TopologicalSpace.SeparableSpace H] in
theorem frechetRiskReal_eq_hilbertBranchRisk
    (nu : Measure H) [IsProbabilityMeasure nu]
    (hnu : MemLp (id : H → H) 2 nu) (s : H) :
    frechetRiskReal nu s =
      hilbertBranchRisk (hilbertMeasureVarianceReal nu)
        (hilbertMeasureMean nu) s := by
  let mean : H := hilbertMeasureMean nu
  have hIdInt : Integrable (id : H → H) nu := hnu.integrable one_le_two
  have hCenteredLp : MemLp (fun x : H => x - mean) 2 nu := by
    change MemLp ((id : H → H) - fun _ : H => mean) 2 nu
    exact hnu.sub (memLp_const mean)
  have hAtSLp : MemLp (fun x : H => x - s) 2 nu := by
    change MemLp ((id : H → H) - fun _ : H => s) 2 nu
    exact hnu.sub (memLp_const s)
  have hCenteredSq : Integrable (fun x : H => ‖x - mean‖ ^ 2) nu :=
    hCenteredLp.integrable_norm_pow (by norm_num)
  have hAtSSq : Integrable (fun x : H => ‖x - s‖ ^ 2) nu :=
    hAtSLp.integrable_norm_pow (by norm_num)
  have hCenteredInt : Integrable (fun x : H => x - mean) nu :=
    hCenteredLp.integrable one_le_two
  have hCrossInt : Integrable
      (fun x : H => 2 * inner ℝ (x - mean) (mean - s)) nu :=
    (hCenteredInt.inner_const (mean - s)).const_mul 2
  have hConstInt : Integrable (fun _ : H => ‖mean - s‖ ^ 2) nu :=
    integrable_const _
  have hPointwise : (fun x : H => ‖x - s‖ ^ 2) =
      fun x => ‖x - mean‖ ^ 2 +
        2 * inner ℝ (x - mean) (mean - s) +
        ‖mean - s‖ ^ 2 := by
    funext x
    rw [show x - s = (x - mean) + (mean - s) by abel]
    exact norm_add_sq_real (x - mean) (mean - s)
  have hCenteredIntegral : ∫ x : H, x - mean ∂nu = 0 := by
    calc
      (∫ x : H, x - mean ∂nu) =
          (∫ x : H, x ∂nu) - ∫ _x : H, mean ∂nu :=
        integral_sub hIdInt (integrable_const mean)
      _ = 0 := by simp [mean, hilbertMeasureMean]
  have hCrossIntegral :
      ∫ x : H, 2 * inner ℝ (x - mean) (mean - s) ∂nu = 0 := by
    calc
      (∫ x : H, 2 * inner ℝ (x - mean) (mean - s) ∂nu) =
          2 * ∫ x : H, inner ℝ (mean - s) (x - mean) ∂nu := by
        rw [integral_const_mul]
        congr 1
        apply integral_congr_ae
        filter_upwards with x
        rw [real_inner_comm]
      _ = 2 * inner ℝ (mean - s) (∫ x : H, x - mean ∂nu) := by
        rw [integral_inner hCenteredInt (mean - s)]
      _ = 0 := by rw [hCenteredIntegral]; simp
  have hRiskIntegral : frechetRiskReal nu s = ∫ x : H, ‖x - s‖ ^ 2 ∂nu := by
    rw [frechetRiskReal, frechetRisk_eq_lintegral]
    simp only [dist_eq_norm]
    rw [← ofReal_integral_eq_lintegral_ofReal hAtSSq
      (Filter.Eventually.of_forall fun x => sq_nonneg ‖x - s‖)]
    rw [ENNReal.toReal_ofReal]
    exact integral_nonneg fun x => sq_nonneg ‖x - s‖
  have hTotalIntegral :
      (∫ x : H, ‖x - mean‖ ^ 2 +
          2 * inner ℝ (x - mean) (mean - s) + ‖mean - s‖ ^ 2 ∂nu) =
        (∫ x : H, ‖x - mean‖ ^ 2 ∂nu) +
          (∫ x : H, 2 * inner ℝ (x - mean) (mean - s) ∂nu) +
          (∫ _x : H, ‖mean - s‖ ^ 2 ∂nu) := by
    calc
      _ = (∫ x : H, ‖x - mean‖ ^ 2 +
              2 * inner ℝ (x - mean) (mean - s) ∂nu) +
            (∫ _x : H, ‖mean - s‖ ^ 2 ∂nu) := by
          exact integral_add (hCenteredSq.add hCrossInt) hConstInt
      _ = _ := by
        rw [integral_add hCenteredSq hCrossInt]
  rw [hRiskIntegral, hPointwise]
  rw [hTotalIntegral, hCrossIntegral]
  simp only [add_zero, integral_const]
  simp
  simp only [hilbertBranchRisk, hilbertMeasureVarianceReal, mean]
  rw [norm_sub_rev]

omit [InnerProductSpace ℝ H] [CompleteSpace H]
  [OpensMeasurableSpace H] [TopologicalSpace.SeparableSpace H] in
theorem frechetRisk_ne_top_of_memLp_id
    (nu : Measure H) [IsProbabilityMeasure nu]
    (hnu : MemLp (id : H → H) 2 nu) (s : H) :
    frechetRisk nu s ≠ ∞ := by
  have hAtSLp : MemLp (fun x : H => x - s) 2 nu := by
    change MemLp ((id : H → H) - fun _ : H => s) 2 nu
    exact hnu.sub (memLp_const s)
  have hAtSSq : Integrable (fun x : H => ‖x - s‖ ^ 2) nu :=
    hAtSLp.integrable_norm_pow (by norm_num)
  rw [frechetRisk_eq_lintegral]
  simp only [dist_eq_norm]
  rw [← ofReal_integral_eq_lintegral_ofReal hAtSSq
    (Filter.Eventually.of_forall fun x => sq_nonneg ‖x - s‖)]
  exact ENNReal.ofReal_ne_top

omit [TopologicalSpace.SeparableSpace H] in
theorem frechetVariance_toReal_eq_hilbertMeasureVarianceReal
    (nu : Measure H) [IsProbabilityMeasure nu]
    (hnu : MemLp (id : H → H) 2 nu) :
    (frechetVariance nu).toReal = hilbertMeasureVarianceReal nu := by
  have hFinite : ∀ s : H, frechetRisk nu s ≠ ∞ :=
    frechetRisk_ne_top_of_memLp_id nu hnu
  have hRisk : frechetRiskReal nu =
      hilbertBranchRisk (hilbertMeasureVarianceReal nu)
        (hilbertMeasureMean nu) := by
    funext s
    exact frechetRiskReal_eq_hilbertBranchRisk nu hnu s
  rw [← sInf_frechetRiskReal nu hFinite, hRisk,
    sInf_hilbertBranchRisk]

variable {Omega : Type*} {mOmega : MeasurableSpace Omega}

def hilbertKernelMean
    (m : MeasurableSpace Omega) (kappa : Kernel[m] Omega H) : Omega → H :=
  fun omega => hilbertMeasureMean (kappa omega)

theorem stronglyMeasurable_hilbertKernelMean
    (m : MeasurableSpace Omega) (kappa : Kernel[m] Omega H)
    [IsSFiniteKernel kappa] :
    StronglyMeasurable[m] (hilbertKernelMean m kappa) := by
  exact stronglyMeasurable_id.integral_kernel

omit [TopologicalSpace.SeparableSpace H] in
theorem frechetRiskReal_eq_kernelHilbertBranchRisk
    (m : MeasurableSpace Omega) (kappa : Kernel[m] Omega H)
    [IsMarkovKernel kappa] (omega : Omega)
    (homega : MemLp (id : H → H) 2 (kappa omega)) (s : H) :
    frechetRiskReal (kappa omega) s =
      hilbertBranchRisk (posteriorFrechetVarianceReal m kappa omega)
        (hilbertKernelMean m kappa omega) s := by
  rw [frechetRiskReal_eq_hilbertBranchRisk (kappa omega) homega s]
  simp only [posteriorFrechetVarianceReal, hilbertKernelMean]
  rw [frechetVariance_toReal_eq_hilbertMeasureVarianceReal
    (kappa omega) homega]

def hilbertBinaryOracleRCDFormula
    (mu : Measure[mOmega] Omega) (mSmall : MeasurableSpace Omega)
    (A : Set Omega) (kappaA kappaAc : Kernel[mSmall] Omega H) :
    Omega → ℝ :=
  fun omega =>
    boundedBinaryEventProbability mu mSmall A omega *
      (1 - boundedBinaryEventProbability mu mSmall A omega) *
      ‖hilbertKernelMean mSmall kappaA omega -
        hilbertKernelMean mSmall kappaAc omega‖ ^ 2

def hilbertBinaryOracleRCDStrictEvent
    (mu : Measure[mOmega] Omega) (mSmall : MeasurableSpace Omega)
    (A : Set Omega) (kappaA kappaAc : Kernel[mSmall] Omega H) :
    Set Omega :=
  hilbertBinaryOracleStrictEvent
    (boundedBinaryEventProbability mu mSmall A)
    (hilbertKernelMean mSmall kappaA)
    (hilbertKernelMean mSmall kappaAc)

theorem actual_probabilistic_hilbert_oracle
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
    (hMoment : Integrable (fun omega => dist (K omega) s0 ^ 2) mu)
    (hBranchL2A : ∀ᵐ omega ∂mu,
      MemLp (id : H → H) 2 (kappaA omega))
    (hBranchL2Ac : ∀ᵐ omega ∂mu,
      MemLp (id : H → H) 2 (kappaAc omega)) :
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
  have hFiniteA : ∀ᵐ omega ∂mu,
      ∀ s : H, frechetRisk (kappaA omega) s ≠ ∞ := by
    filter_upwards [hBranchL2A] with omega homega
    exact frechetRisk_ne_top_of_memLp_id (kappaA omega) homega
  have hFiniteAc : ∀ᵐ omega ∂mu,
      ∀ s : H, frechetRisk (kappaAc omega) s ≠ ∞ := by
    filter_upwards [hBranchL2Ac] with omega homega
    exact frechetRisk_ne_top_of_memLp_id (kappaAc omega) homega
  have hFrechet := actual_binary_oracle_frechet_refinement
    mu mSmall mLarge hSmallLarge hLargeAmbient A hA K hK
      kappaA kappaAc hCoarseRCD hFineRCD s0 hMoment hFiniteA hFiniteAc
  have hActualToHilbert :
      actualFrechetBinaryOracleGapRCD mu mSmall A kappaA kappaAc =ᵐ[mu]
        GapH := by
    filter_upwards [hBranchL2A, hBranchL2Ac] with omega hL2Aomega hL2Acomega
    have hRiskA : frechetRiskReal (kappaA omega) =
        hilbertBranchRisk (varianceA omega) (meanA omega) := by
      funext s
      exact frechetRiskReal_eq_kernelHilbertBranchRisk
        mSmall kappaA omega hL2Aomega s
    have hRiskAc : frechetRiskReal (kappaAc omega) =
        hilbertBranchRisk (varianceAc omega) (meanAc omega) := by
      funext s
      exact frechetRiskReal_eq_kernelHilbertBranchRisk
        mSmall kappaAc omega hL2Acomega s
    dsimp only [actualFrechetBinaryOracleGapRCD, GapH,
      randomActualHilbertOracleGap]
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
  have hGHDef : GH = hilbertBinaryOracleStrictEvent p meanA meanAc := by
    rfl
  have hFormulaMeasurable : StronglyMeasurable[mSmall]
      (hilbertBinaryOracleRCDFormula mu mSmall A kappaA kappaAc) := by
    change StronglyMeasurable[mSmall] (fun omega =>
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
