import SequentialLearning.BinaryOracleGap
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# Binary-oracle refinement from regular conditional distributions

This file realizes the abstract binary-oracle gap algebra using regular conditional
distributions. Two branch kernels are mixed by a bounded version of the conditional
event probability to form the coarse posterior, and are selected according to the
revealed event to form the oracle posterior. The resulting Frechet refinement gain is
identified with the binary-oracle gap, including its measurable strictness event and
the quantitative separated-sublevel-set lower bound.
-/

namespace SequentialLearning

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal MeasureTheory ProbabilityTheory

noncomputable section

variable {Omega : Type*} {mOmega : MeasurableSpace Omega}

def liftKernel
    {mSmall mLarge : MeasurableSpace Omega} (hSmallLarge : mSmall ≤ mLarge)
    {S : Type*} [MeasurableSpace S]
    (kappa : Kernel[mSmall] Omega S) : Kernel[mLarge] Omega S :=
  ProbabilityTheory.Kernel.comap kappa id (measurable_id'' hSmallLarge)

@[simp]
theorem liftKernel_apply
    {mSmall mLarge : MeasurableSpace Omega} (hSmallLarge : mSmall ≤ mLarge)
    {S : Type*} [MeasurableSpace S]
    (kappa : Kernel[mSmall] Omega S) (omega : Omega) :
    liftKernel hSmallLarge kappa omega = kappa omega := by
  rfl

instance liftKernel.instIsMarkovKernel
    {mSmall mLarge : MeasurableSpace Omega} (hSmallLarge : mSmall ≤ mLarge)
    {S : Type*} [MeasurableSpace S]
    (kappa : Kernel[mSmall] Omega S) [IsMarkovKernel kappa] :
    IsMarkovKernel (liftKernel hSmallLarge kappa) := by
  dsimp only [liftKernel]
  infer_instance

noncomputable def binaryMixtureKernel
    {m : MeasurableSpace Omega} {S : Type*} [MeasurableSpace S]
    (p : Omega → ℝ) (hpMeas : Measurable[m] p)
    (kappaA kappaAc : Kernel[m] Omega S) : Kernel[m] Omega S where
  toFun omega := binaryMixtureMeasure (p omega) (kappaA omega) (kappaAc omega)
  measurable' := Measure.measurable_measure.mpr fun B hB => by
    simp only [binaryMixtureMeasure, Measure.add_apply,
      Measure.smul_apply, smul_eq_mul]
    exact ((hpMeas.ennreal_ofReal.mul (kappaA.measurable_coe hB)).add
      ((measurable_const.sub hpMeas).ennreal_ofReal.mul
        (kappaAc.measurable_coe hB)))

theorem binaryMixtureKernel_apply
    {m : MeasurableSpace Omega} {S : Type*} [MeasurableSpace S]
    (p : Omega → ℝ) (hpMeas : Measurable[m] p)
    (kappaA kappaAc : Kernel[m] Omega S) (omega : Omega) :
    binaryMixtureKernel p hpMeas kappaA kappaAc omega =
      binaryMixtureMeasure (p omega) (kappaA omega) (kappaAc omega) := by
  rfl

instance binaryMixtureKernel.instIsMarkovKernel
    {m : MeasurableSpace Omega} {S : Type*} [MeasurableSpace S]
    (p : Omega → ℝ) (hpMeas : Measurable[m] p)
    (kappaA kappaAc : Kernel[m] Omega S)
    [IsMarkovKernel kappaA] [IsMarkovKernel kappaAc]
    [Fact (∀ omega, 0 ≤ p omega ∧ p omega ≤ 1)] :
    IsMarkovKernel (binaryMixtureKernel p hpMeas kappaA kappaAc) := by
  refine ⟨fun omega => ⟨?_⟩⟩
  rw [binaryMixtureKernel_apply]
  simp only [binaryMixtureMeasure, Measure.add_apply,
    Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (Fact.out (p := ∀ omega, 0 ≤ p omega ∧ p omega ≤ 1) omega).1
    (sub_nonneg.mpr (Fact.out (p := ∀ omega, 0 ≤ p omega ∧ p omega ≤ 1) omega).2)]
  norm_num

open scoped Classical in
noncomputable def binaryBranchValue
    (A : Set Omega) (f g : Omega → ℝ) : Omega → ℝ :=
  Set.piecewise A f g

open scoped Classical in
noncomputable def binaryOracleKernel
    {mSmall mLarge : MeasurableSpace Omega} (hSmallLarge : mSmall ≤ mLarge)
    {S : Type*} [MeasurableSpace S]
    (A : Set Omega) (hA : MeasurableSet[mLarge] A)
    (kappaA kappaAc : Kernel[mSmall] Omega S) : Kernel[mLarge] Omega S :=
  Kernel.piecewise hA
    (liftKernel hSmallLarge kappaA) (liftKernel hSmallLarge kappaAc)

theorem binaryOracleKernel_apply_of_mem
    {mSmall mLarge : MeasurableSpace Omega} (hSmallLarge : mSmall ≤ mLarge)
    {S : Type*} [MeasurableSpace S]
    (A : Set Omega) (hA : MeasurableSet[mLarge] A)
    (kappaA kappaAc : Kernel[mSmall] Omega S) (omega : Omega)
    (homega : omega ∈ A) :
    binaryOracleKernel hSmallLarge A hA kappaA kappaAc omega =
      kappaA omega := by
  classical
  simp only [binaryOracleKernel, Kernel.piecewise_apply, homega, ↓reduceIte,
    liftKernel_apply]

theorem binaryOracleKernel_apply_of_not_mem
    {mSmall mLarge : MeasurableSpace Omega} (hSmallLarge : mSmall ≤ mLarge)
    {S : Type*} [MeasurableSpace S]
    (A : Set Omega) (hA : MeasurableSet[mLarge] A)
    (kappaA kappaAc : Kernel[mSmall] Omega S) (omega : Omega)
    (homega : omega ∉ A) :
    binaryOracleKernel hSmallLarge A hA kappaA kappaAc omega =
      kappaAc omega := by
  classical
  simp only [binaryOracleKernel, Kernel.piecewise_apply, homega, ↓reduceIte,
    liftKernel_apply]

instance binaryOracleKernel.instIsMarkovKernel
    {mSmall mLarge : MeasurableSpace Omega} (hSmallLarge : mSmall ≤ mLarge)
    {S : Type*} [MeasurableSpace S]
    (A : Set Omega) (hA : MeasurableSet[mLarge] A)
    (kappaA kappaAc : Kernel[mSmall] Omega S)
    [IsMarkovKernel kappaA] [IsMarkovKernel kappaAc] :
    IsMarkovKernel
      (binaryOracleKernel hSmallLarge A hA kappaA kappaAc) := by
  dsimp only [binaryOracleKernel]
  infer_instance

theorem posteriorFrechetVarianceReal_binaryOracleKernel
    {mSmall mLarge : MeasurableSpace Omega} (hSmallLarge : mSmall ≤ mLarge)
    {S : Type*} [PseudoMetricSpace S] [MeasurableSpace S] [Nonempty S]
    [OpensMeasurableSpace S] [TopologicalSpace.SeparableSpace S]
    (A : Set Omega) (hA : MeasurableSet[mLarge] A)
    (kappaA kappaAc : Kernel[mSmall] Omega S)
    [IsMarkovKernel kappaA] [IsMarkovKernel kappaAc] :
    posteriorFrechetVarianceReal mLarge
        (binaryOracleKernel hSmallLarge A hA kappaA kappaAc) =
      binaryBranchValue A
        (posteriorFrechetVarianceReal mSmall kappaA)
        (posteriorFrechetVarianceReal mSmall kappaAc) := by
  funext omega
  classical
  by_cases homega : omega ∈ A
  · simp [posteriorFrechetVarianceReal, binaryOracleKernel_apply_of_mem,
      binaryBranchValue, homega]
  · simp [posteriorFrechetVarianceReal, binaryOracleKernel_apply_of_not_mem,
      binaryBranchValue, homega]

def realEventIndicator (A : Set Omega) : Omega → ℝ :=
  A.indicator (fun _ => 1)

def binaryEventProbability (mu : Measure[mOmega] Omega)
    (m : MeasurableSpace Omega) (A : Set Omega) : Omega → ℝ :=
  mu[realEventIndicator A | m]

theorem binaryEventProbability_bounds
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (m : MeasurableSpace Omega) (hm : m ≤ mOmega)
    (A : Set Omega) (hA : MeasurableSet[mOmega] A) :
    ∀ᵐ omega ∂mu,
      0 ≤ binaryEventProbability mu m A omega ∧
        binaryEventProbability mu m A omega ≤ 1 := by
  have hIInt : Integrable (realEventIndicator A) mu :=
    (integrable_const (1 : ℝ)).indicator hA
  have hZeroInt : Integrable (0 : Omega → ℝ) mu := integrable_zero _ _ _
  have hOneInt : Integrable (fun _ : Omega => (1 : ℝ)) mu := integrable_const 1
  have hNonnegative :
      0 ≤ᵐ[mu] binaryEventProbability mu m A := by
    have h := condExp_mono (m := m) (μ := mu) hZeroInt hIInt
      (Filter.Eventually.of_forall fun omega => by
        dsimp only [realEventIndicator]
        by_cases homega : omega ∈ A <;> simp [homega])
    simpa only [condExp_zero, binaryEventProbability] using h
  have hAtMostOne :
      binaryEventProbability mu m A ≤ᵐ[mu] fun _ => (1 : ℝ) := by
    have h := condExp_mono (m := m) (μ := mu) hIInt hOneInt
      (Filter.Eventually.of_forall fun omega => by
        dsimp only [realEventIndicator]
        by_cases homega : omega ∈ A <;> simp [homega])
    simpa only [condExp_const hm, binaryEventProbability] using h
  filter_upwards [hNonnegative, hAtMostOne] with omega h0 h1
  exact ⟨h0, h1⟩

def boundedBinaryEventProbability (mu : Measure[mOmega] Omega)
    (m : MeasurableSpace Omega) (A : Set Omega) : Omega → ℝ :=
  fun omega => max 0 (min 1 (binaryEventProbability mu m A omega))

theorem measurable_boundedBinaryEventProbability
    (mu : Measure[mOmega] Omega) (m : MeasurableSpace Omega) (A : Set Omega) :
    Measurable[m] (boundedBinaryEventProbability mu m A) := by
  exact measurable_const.max
    (measurable_const.min stronglyMeasurable_condExp.measurable)

theorem boundedBinaryEventProbability_bounds
    (mu : Measure[mOmega] Omega) (m : MeasurableSpace Omega) (A : Set Omega)
    (omega : Omega) :
    0 ≤ boundedBinaryEventProbability mu m A omega ∧
      boundedBinaryEventProbability mu m A omega ≤ 1 := by
  dsimp only [boundedBinaryEventProbability]
  constructor <;> simp

theorem boundedBinaryEventProbability_ae_eq
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (m : MeasurableSpace Omega) (hm : m ≤ mOmega)
    (A : Set Omega) (hA : MeasurableSet[mOmega] A) :
    boundedBinaryEventProbability mu m A =ᵐ[mu]
      binaryEventProbability mu m A := by
  filter_upwards [binaryEventProbability_bounds mu m hm A hA] with
      omega homega
  simp only [boundedBinaryEventProbability, min_eq_right homega.2,
    max_eq_right homega.1]

noncomputable def binaryEventMixtureKernel
    (mu : Measure[mOmega] Omega) (m : MeasurableSpace Omega) (A : Set Omega)
    {S : Type*} [MeasurableSpace S]
    (kappaA kappaAc : Kernel[m] Omega S) : Kernel[m] Omega S :=
  binaryMixtureKernel (boundedBinaryEventProbability mu m A)
    (measurable_boundedBinaryEventProbability mu m A) kappaA kappaAc

@[simp]
theorem binaryEventMixtureKernel_apply
    (mu : Measure[mOmega] Omega) (m : MeasurableSpace Omega) (A : Set Omega)
    {S : Type*} [MeasurableSpace S]
    (kappaA kappaAc : Kernel[m] Omega S) (omega : Omega) :
    binaryEventMixtureKernel mu m A kappaA kappaAc omega =
      binaryMixtureMeasure (boundedBinaryEventProbability mu m A omega)
        (kappaA omega) (kappaAc omega) := by
  rfl

instance binaryEventMixtureKernel.instIsMarkovKernel
    (mu : Measure[mOmega] Omega) (m : MeasurableSpace Omega) (A : Set Omega)
    {S : Type*} [MeasurableSpace S]
    (kappaA kappaAc : Kernel[m] Omega S)
    [IsMarkovKernel kappaA] [IsMarkovKernel kappaAc] :
    IsMarkovKernel (binaryEventMixtureKernel mu m A kappaA kappaAc) := by
  let _ : Fact (∀ omega,
      0 ≤ boundedBinaryEventProbability mu m A omega ∧
        boundedBinaryEventProbability mu m A omega ≤ 1) :=
    ⟨boundedBinaryEventProbability_bounds mu m A⟩
  dsimp only [binaryEventMixtureKernel]
  infer_instance

theorem condExp_binary_piecewise
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (m : MeasurableSpace Omega) (hm : m ≤ mOmega)
    (A : Set Omega) (hA : MeasurableSet[mOmega] A)
    (f g : Omega → ℝ)
    (hfMeas : StronglyMeasurable[m] f)
    (hgMeas : StronglyMeasurable[m] g)
    (hAInt : Integrable (realEventIndicator A * f) mu)
    (hAcInt : Integrable
      ((fun omega => 1 - realEventIndicator A omega) * g) mu) :
    mu[binaryBranchValue A f g | m] =ᵐ[mu]
      fun omega =>
        binaryEventProbability mu m A omega * f omega +
          (1 - binaryEventProbability mu m A omega) * g omega := by
  classical
  let I : Omega → ℝ := realEventIndicator A
  have hIMeas : Measurable[mOmega] I := by
    exact measurable_const.indicator hA
  have hIInt : Integrable I mu := by
    exact (integrable_const (1 : ℝ)).indicator hA
  have hOneSubIInt : Integrable (fun omega => 1 - I omega) mu :=
    (integrable_const (1 : ℝ)).sub hIInt
  have hIfInt : Integrable (I * f) mu := by
    simpa only [I] using hAInt
  have hOneSubIgInt : Integrable ((fun omega => 1 - I omega) * g) mu := by
    simpa only [I] using hAcInt
  have hPiecewise : binaryBranchValue A f g =
      I * f + (fun omega => 1 - I omega) * g := by
    funext omega
    dsimp only [binaryBranchValue, I, realEventIndicator]
    by_cases homega : omega ∈ A <;> simp [homega]
  rw [hPiecewise]
  have hAdd := condExp_add hIfInt hOneSubIgInt m
  have hFirst := condExp_mul_of_stronglyMeasurable_right
    hfMeas hIfInt hIInt
  have hSecond := condExp_mul_of_stronglyMeasurable_right
    hgMeas hOneSubIgInt hOneSubIInt
  have hComplement :
      mu[(fun omega => 1 - I omega) | m] =ᵐ[mu]
        fun omega => 1 - binaryEventProbability mu m A omega := by
    have hSub := condExp_sub (integrable_const (1 : ℝ)) hIInt m
    filter_upwards [hSub] with omega hSubOmega
    change mu[((fun _ : Omega => (1 : ℝ)) - I) | m] omega = _
    rw [hSubOmega]
    simp only [condExp_const hm, Pi.sub_apply]
    change 1 - mu[I | m] omega = 1 - mu[I | m] omega
    rfl
  filter_upwards [hAdd, hFirst, hSecond, hComplement] with
      omega hAddOmega hFirstOmega hSecondOmega hComplementOmega
  rw [hAddOmega, Pi.add_apply, hFirstOmega, hSecondOmega,
    Pi.mul_apply, Pi.mul_apply]
  change mu[I | m] omega * f omega +
      mu[(fun omega => 1 - I omega) | m] omega * g omega =
    mu[I | m] omega * f omega + (1 - mu[I | m] omega) * g omega
  rw [hComplementOmega]
  rfl

theorem condExp_posteriorFrechetVariance_binaryOracleKernel
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (mSmall mLarge : MeasurableSpace Omega)
    (hSmallLarge : mSmall ≤ mLarge) (hLargeAmbient : mLarge ≤ mOmega)
    {S : Type*} [PseudoMetricSpace S] [MeasurableSpace S] [Nonempty S]
    [OpensMeasurableSpace S] [TopologicalSpace.SeparableSpace S]
    (A : Set Omega) (hA : MeasurableSet[mLarge] A)
    (kappaA kappaAc : Kernel[mSmall] Omega S)
    [IsMarkovKernel kappaA] [IsMarkovKernel kappaAc]
    (hFineInt : Integrable
      (posteriorFrechetVarianceReal mLarge
        (binaryOracleKernel hSmallLarge A hA kappaA kappaAc)) mu) :
    mu[posteriorFrechetVarianceReal mLarge
          (binaryOracleKernel hSmallLarge A hA kappaA kappaAc) |
        mSmall] =ᵐ[mu]
      fun omega =>
        boundedBinaryEventProbability mu mSmall A omega *
            posteriorFrechetVarianceReal mSmall kappaA omega +
          (1 - boundedBinaryEventProbability mu mSmall A omega) *
            posteriorFrechetVarianceReal mSmall kappaAc omega := by
  let VA : Omega → ℝ := posteriorFrechetVarianceReal mSmall kappaA
  let VAc : Omega → ℝ := posteriorFrechetVarianceReal mSmall kappaAc
  let VFine : Omega → ℝ := posteriorFrechetVarianceReal mLarge
    (binaryOracleKernel hSmallLarge A hA kappaA kappaAc)
  let I : Omega → ℝ := realEventIndicator A
  have hFineEq : VFine = binaryBranchValue A VA VAc := by
    exact posteriorFrechetVarianceReal_binaryOracleKernel
      hSmallLarge A hA kappaA kappaAc
  have hBranchInt : Integrable (binaryBranchValue A VA VAc) mu :=
    hFineInt.congr (Filter.Eventually.of_forall fun omega =>
      congr_fun hFineEq omega)
  have hVAmeas : StronglyMeasurable[mSmall] VA := by
    exact stronglyMeasurable_posteriorFrechetVarianceReal mSmall kappaA
  have hVAcmeas : StronglyMeasurable[mSmall] VAc := by
    exact stronglyMeasurable_posteriorFrechetVarianceReal mSmall kappaAc
  have hImeas : Measurable[mOmega] I := by
    exact measurable_const.indicator (hLargeAmbient A hA)
  have hAInt : Integrable (I * VA) mu := by
    apply hBranchInt.mono'
    · exact (hImeas.mul
        ((hVAmeas.mono (hSmallLarge.trans hLargeAmbient)).measurable))
          |>.aestronglyMeasurable
    · filter_upwards with omega
      dsimp only [I, VA, VAc, realEventIndicator, binaryBranchValue]
      rw [Real.norm_eq_abs]
      by_cases homega : omega ∈ A <;>
        simp [homega, posteriorFrechetVarianceReal,
          abs_of_nonneg ENNReal.toReal_nonneg]
  have hAcInt : Integrable ((fun omega => 1 - I omega) * VAc) mu := by
    apply hBranchInt.mono'
    · exact ((hImeas.const_sub 1).mul
        ((hVAcmeas.mono (hSmallLarge.trans hLargeAmbient)).measurable))
          |>.aestronglyMeasurable
    · filter_upwards with omega
      dsimp only [I, VA, VAc, realEventIndicator, binaryBranchValue]
      rw [Real.norm_eq_abs]
      by_cases homega : omega ∈ A <;>
        simp [homega, posteriorFrechetVarianceReal,
          abs_of_nonneg ENNReal.toReal_nonneg]
  have hCond := condExp_binary_piecewise
    mu mSmall (hSmallLarge.trans hLargeAmbient) A
      (hLargeAmbient A hA) VA VAc hVAmeas hVAcmeas hAInt hAcInt
  have hpEq := boundedBinaryEventProbability_ae_eq
    mu mSmall (hSmallLarge.trans hLargeAmbient) A (hLargeAmbient A hA)
  calc
    mu[VFine | mSmall] =ᵐ[mu]
        mu[binaryBranchValue A VA VAc | mSmall] :=
      condExp_congr_ae (Filter.Eventually.of_forall fun omega =>
        congr_fun hFineEq omega)
    _ =ᵐ[mu] fun omega =>
        binaryEventProbability mu mSmall A omega * VA omega +
          (1 - binaryEventProbability mu mSmall A omega) * VAc omega := hCond
    _ =ᵐ[mu] fun omega =>
        boundedBinaryEventProbability mu mSmall A omega * VA omega +
          (1 - boundedBinaryEventProbability mu mSmall A omega) * VAc omega := by
      filter_upwards [hpEq] with omega hpOmega
      rw [hpOmega]

def binaryOracleFrechetGain
    (mu : Measure[mOmega] Omega)
    (mSmall mLarge : MeasurableSpace Omega)
    (hSmallLarge : mSmall ≤ mLarge)
    (A : Set Omega) (hA : MeasurableSet[mLarge] A)
    {S : Type*} [PseudoMetricSpace S] [MeasurableSpace S]
    (kappaA kappaAc : Kernel[mSmall] Omega S) : Omega → ℝ :=
  frechetRefinementGain mu mSmall mLarge
    (binaryEventMixtureKernel mu mSmall A kappaA kappaAc)
    (binaryOracleKernel hSmallLarge A hA kappaA kappaAc)

def actualFrechetBinaryOracleGapRCD
    (mu : Measure[mOmega] Omega) (mSmall : MeasurableSpace Omega)
    (A : Set Omega)
    {S : Type*} [PseudoMetricSpace S] [MeasurableSpace S] [Nonempty S]
    [OpensMeasurableSpace S]
    (kappaA kappaAc : Kernel[mSmall] Omega S) : Omega → ℝ :=
  fun omega => actualBinaryOracleGap
    (boundedBinaryEventProbability mu mSmall A omega)
    (frechetRiskReal (kappaA omega))
    (frechetRiskReal (kappaAc omega))

def frechetBinaryOracleStrictEvent
    (mu : Measure[mOmega] Omega)
    (mSmall mLarge : MeasurableSpace Omega)
    (hSmallLarge : mSmall ≤ mLarge)
    (A : Set Omega) (hA : MeasurableSet[mLarge] A)
    {S : Type*} [PseudoMetricSpace S] [MeasurableSpace S]
    (kappaA kappaAc : Kernel[mSmall] Omega S) : Set Omega :=
  {omega | 0 < binaryOracleFrechetGain
    mu mSmall mLarge hSmallLarge A hA kappaA kappaAc omega}

theorem actual_binary_oracle_frechet_refinement
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (mSmall mLarge : MeasurableSpace Omega)
    (hSmallLarge : mSmall ≤ mLarge) (hLargeAmbient : mLarge ≤ mOmega)
    (A : Set Omega) (hA : MeasurableSet[mLarge] A)
    {S : Type*} [PseudoMetricSpace S] [MeasurableSpace S] [Nonempty S]
    [OpensMeasurableSpace S] [TopologicalSpace.SeparableSpace S]
    (K : Omega → S) (hK : Measurable[mOmega] K)
    (kappaA kappaAc : Kernel[mSmall] Omega S)
    [IsMarkovKernel kappaA] [IsMarkovKernel kappaAc]
    (hCoarseRCD : IsRegularConditionalLaw mu mSmall
      (hSmallLarge.trans hLargeAmbient) K
      (binaryEventMixtureKernel mu mSmall A kappaA kappaAc))
    (hFineRCD : IsRegularConditionalLaw mu mLarge hLargeAmbient K
      (binaryOracleKernel hSmallLarge A hA kappaA kappaAc))
    (s0 : S)
    (hMoment : Integrable (fun omega => dist (K omega) s0 ^ 2) mu)
    (hFiniteRiskA : ∀ᵐ omega ∂mu,
      ∀ s : S, frechetRisk (kappaA omega) s ≠ ∞)
    (hFiniteRiskAc : ∀ᵐ omega ∂mu,
      ∀ s : S, frechetRisk (kappaAc omega) s ≠ ∞) :
    (binaryOracleFrechetGain mu mSmall mLarge hSmallLarge
        A hA kappaA kappaAc =ᵐ[mu]
      actualFrechetBinaryOracleGapRCD mu mSmall A kappaA kappaAc) ∧
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
      (frechetBinaryOracleStrictEvent mu mSmall mLarge hSmallLarge
        A hA kappaA kappaAc) ∧
    (∀ᵐ omega ∂mu,
      omega ∈ frechetBinaryOracleStrictEvent
          mu mSmall mLarge hSmallLarge A hA kappaA kappaAc ↔
        0 < boundedBinaryEventProbability mu mSmall A omega ∧
        boundedBinaryEventProbability mu mSmall A omega < 1 ∧
        ¬HasCommonApproxMinimizingSequence
          (excessAboveInfimum (frechetRiskReal (kappaA omega)))
          (excessAboveInfimum (frechetRiskReal (kappaAc omega)))) ∧
    (∀ᵐ omega ∂mu,
      omega ∉ frechetBinaryOracleStrictEvent
          mu mSmall mLarge hSmallLarge A hA kappaA kappaAc →
        binaryOracleFrechetGain mu mSmall mLarge hSmallLarge
          A hA kappaA kappaAc omega = 0) ∧
    ((0 < ∫ omega,
        binaryOracleFrechetGain mu mSmall mLarge hSmallLarge
          A hA kappaA kappaAc omega ∂mu) ↔
      0 < mu (frechetBinaryOracleStrictEvent
        mu mSmall mLarge hSmallLarge A hA kappaA kappaAc)) := by
  let kappaCoarse : Kernel[mSmall] Omega S :=
    binaryEventMixtureKernel mu mSmall A kappaA kappaAc
  let kappaFine : Kernel[mLarge] Omega S :=
    binaryOracleKernel hSmallLarge A hA kappaA kappaAc
  let p : Omega → ℝ := boundedBinaryEventProbability mu mSmall A
  let Gamma : Omega → ℝ := binaryOracleFrechetGain
    mu mSmall mLarge hSmallLarge A hA kappaA kappaAc
  let Gap : Omega → ℝ :=
    actualFrechetBinaryOracleGapRCD mu mSmall A kappaA kappaAc
  let G : Set Omega := frechetBinaryOracleStrictEvent
    mu mSmall mLarge hSmallLarge A hA kappaA kappaAc
  have hFineWell := posteriorFrechet_finite_and_integrable
    mu mLarge hLargeAmbient K hK kappaFine hFineRCD s0 hMoment
  have hFineInt : Integrable
      (posteriorFrechetVarianceReal mLarge kappaFine) mu := by
    change Integrable
      (fun omega => (frechetVariance (kappaFine omega)).toReal) mu
    exact hFineWell.2.2.2
  have hCondFine :=
    condExp_posteriorFrechetVariance_binaryOracleKernel
      mu mSmall mLarge hSmallLarge hLargeAmbient A hA
        kappaA kappaAc hFineInt
  have hGainWell := frechetRefinementGain_wellPosed
    mu mSmall mLarge hSmallLarge hLargeAmbient K hK
      kappaCoarse kappaFine hCoarseRCD hFineRCD s0 hMoment
  have hGamma : Gamma =ᵐ[mu] Gap := by
    filter_upwards [hCondFine, hFiniteRiskA, hFiniteRiskAc] with
        omega hCondOmega hFiniteAOmega hFiniteAcOmega
    have hpOmega := boundedBinaryEventProbability_bounds
      mu mSmall A omega
    have hActual := actual_frechet_binary_oracle_gap
      (p omega) (kappaA omega) (kappaAc omega)
      hpOmega.1 hpOmega.2 hFiniteAOmega hFiniteAcOmega
    dsimp only [Gamma, Gap, binaryOracleFrechetGain,
      actualFrechetBinaryOracleGapRCD, frechetRefinementGain,
      refinementGain, kappaCoarse, kappaFine]
    rw [hCondOmega]
    simpa only [posteriorFrechetVarianceReal,
      binaryEventMixtureKernel_apply, p] using hActual.symm
  have hGammaMeasurable : StronglyMeasurable[mSmall] Gamma := by
    exact hGainWell.1
  have hGammaIntegrable : Integrable Gamma mu := hGainWell.2.1
  have hGammaNonnegative : 0 ≤ᵐ[mu] Gamma := hGainWell.2.2
  have hGDef : G = {omega | 0 < Gamma omega} := by
    rfl
  have hGMeasurable : MeasurableSet[mSmall] G := by
    rw [hGDef]
    exact measurableSet_lt measurable_const hGammaMeasurable.measurable
  have hGCharacterization : ∀ᵐ omega ∂mu,
      omega ∈ G ↔
        0 < p omega ∧ p omega < 1 ∧
        ¬HasCommonApproxMinimizingSequence
          (excessAboveInfimum (frechetRiskReal (kappaA omega)))
          (excessAboveInfimum (frechetRiskReal (kappaAc omega))) := by
    filter_upwards [hGamma, hFiniteRiskA, hFiniteRiskAc] with
        omega hGammaOmega hFiniteAOmega hFiniteAcOmega
    have hpOmega := boundedBinaryEventProbability_bounds
      mu mSmall A omega
    change 0 < Gamma omega ↔ _
    rw [hGammaOmega]
    exact actualBinaryOracleGap_pos_iff
      (p omega)
      (frechetRiskReal (kappaA omega))
      (frechetRiskReal (kappaAc omega))
      hpOmega.1 hpOmega.2
      ⟨0, by rintro _ ⟨s, rfl⟩; exact ENNReal.toReal_nonneg⟩
      ⟨0, by rintro _ ⟨s, rfl⟩; exact ENNReal.toReal_nonneg⟩
  have hZeroOutside : ∀ᵐ omega ∂mu,
      omega ∉ G → Gamma omega = 0 := by
    filter_upwards [hGammaNonnegative] with omega hNonnegativeOmega
    intro hNotG
    have hNotPositive : ¬0 < Gamma omega := by
      exact fun hPositive => hNotG hPositive
    exact le_antisymm (le_of_not_gt hNotPositive) hNonnegativeOmega
  have hIntegralCriterion :
      (0 < ∫ omega, Gamma omega ∂mu) ↔ 0 < mu G := by
    exact strict_oracle_gap_integral_pos_iff mu Gamma G
      hGammaNonnegative hGammaIntegrable
      (Filter.Eventually.of_forall fun _ => Iff.rfl)
  simpa only [Gamma, Gap, G, p] using
    ⟨hGamma, hGammaMeasurable, hGammaIntegrable,
      hGammaNonnegative, hGMeasurable, hGCharacterization,
      hZeroOutside, hIntegralCriterion⟩

theorem binaryOracleFrechetGain_lower_bound_of_disjoint_sublevels
    (mu : Measure[mOmega] Omega)
    (mSmall mLarge : MeasurableSpace Omega)
    (hSmallLarge : mSmall ≤ mLarge)
    (A : Set Omega) (hA : MeasurableSet[mLarge] A)
    {S : Type*} [PseudoMetricSpace S] [MeasurableSpace S] [Nonempty S]
    [OpensMeasurableSpace S]
    (kappaA kappaAc : Kernel[mSmall] Omega S)
    (hGamma : binaryOracleFrechetGain mu mSmall mLarge hSmallLarge
        A hA kappaA kappaAc =ᵐ[mu]
      actualFrechetBinaryOracleGapRCD mu mSmall A kappaA kappaAc)
    (epsilon : ℝ) (hEpsilon : 0 < epsilon)
    (hFiniteRiskA : ∀ᵐ omega ∂mu,
      ∀ s : S, frechetRisk (kappaA omega) s ≠ ∞)
    (hFiniteRiskAc : ∀ᵐ omega ∂mu,
      ∀ s : S, frechetRisk (kappaAc omega) s ≠ ∞)
    (hDisjoint : ∀ᵐ omega ∂mu,
      Disjoint
        {s | excessAboveInfimum (frechetRiskReal (kappaA omega)) s < epsilon}
        {s | excessAboveInfimum (frechetRiskReal (kappaAc omega)) s < epsilon}) :
    (fun omega =>
      min (boundedBinaryEventProbability mu mSmall A omega)
          (1 - boundedBinaryEventProbability mu mSmall A omega) * epsilon) ≤ᵐ[mu]
      binaryOracleFrechetGain mu mSmall mLarge hSmallLarge
        A hA kappaA kappaAc := by
  filter_upwards [hGamma, hFiniteRiskA, hFiniteRiskAc, hDisjoint] with
      omega hGammaOmega hFiniteAOmega hFiniteAcOmega hDisjointOmega
  let p := boundedBinaryEventProbability mu mSmall A omega
  let riskA := frechetRiskReal (kappaA omega)
  let riskAc := frechetRiskReal (kappaAc omega)
  have hp := boundedBinaryEventProbability_bounds mu mSmall A omega
  have hBoundA : BddBelow (Set.range riskA) :=
    ⟨0, by rintro _ ⟨s, rfl⟩; exact ENNReal.toReal_nonneg⟩
  have hBoundAc : BddBelow (Set.range riskAc) :=
    ⟨0, by rintro _ ⟨s, rfl⟩; exact ENNReal.toReal_nonneg⟩
  have hRepresentation := actualBinaryOracleGap_representation
    p riskA riskAc hp.1 hp.2 hBoundA hBoundAc
  have hLower := abstractOracleGap_lower_bound_of_disjoint_sublevels
    p epsilon (excessAboveInfimum riskA) (excessAboveInfimum riskAc)
      hp.1 hp.2 hEpsilon
      (excessAboveInfimum_nonnegative riskA hBoundA)
      (excessAboveInfimum_nonnegative riskAc hBoundAc)
      hDisjointOmega
  calc
    min p (1 - p) * epsilon ≤
        abstractOracleGap p
          (excessAboveInfimum riskA) (excessAboveInfimum riskAc) := hLower
    _ = actualBinaryOracleGap p riskA riskAc := hRepresentation.symm
    _ = binaryOracleFrechetGain mu mSmall mLarge hSmallLarge
          A hA kappaA kappaAc omega := by
      simpa only [actualFrechetBinaryOracleGapRCD, p, riskA, riskAc] using
        hGammaOmega.symm

end

end SequentialLearning
