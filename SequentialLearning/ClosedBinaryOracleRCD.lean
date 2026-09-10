import SequentialLearning.BinaryOracleRCD
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Closed binary-oracle regular-conditional-law interfaces

The original binary-oracle implementation asked callers to prove that both
branch risks were finite almost surely.  That is stronger than the statistical
hypotheses require: on the interior-probability event, branch finiteness follows
from finiteness of the mixture law, while at probabilities zero and one the
unused branch has no effect on the oracle gap.

This file packages that observation and exposes the binary-oracle theorem under
only regular-conditional-law existence and the master second-moment assumption.
-/

namespace SequentialLearning

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal MeasureTheory ProbabilityTheory

noncomputable section

section DeterministicClosure

variable {S : Type*} [PseudoMetricSpace S] [MeasurableSpace S]
  [Nonempty S] [OpensMeasurableSpace S]

omit [PseudoMetricSpace S] [MeasurableSpace S] [OpensMeasurableSpace S] in
/-- The actual oracle gap vanishes when the first branch has zero weight. -/
theorem actualBinaryOracleGap_zero_of_left_weight_zero
    (riskA riskAc : S → ℝ)
    (hA : BddBelow (Set.range riskA))
    (hAc : BddBelow (Set.range riskAc)) :
    actualBinaryOracleGap 0 riskA riskAc = 0 := by
  rw [actualBinaryOracleGap_representation 0 riskA riskAc
    (by norm_num) (by norm_num) hA hAc]
  exact abstractOracleGap_zero_of_left_weight_zero
    (excessAboveInfimum riskA) (excessAboveInfimum riskAc)
    (sInf_excessAboveInfimum_eq_zero riskAc hAc)

omit [PseudoMetricSpace S] [MeasurableSpace S] [OpensMeasurableSpace S] in
/-- The actual oracle gap vanishes when the complementary branch has zero
weight. -/
theorem actualBinaryOracleGap_zero_of_right_weight_zero
    (riskA riskAc : S → ℝ)
    (hA : BddBelow (Set.range riskA))
    (hAc : BddBelow (Set.range riskAc)) :
    actualBinaryOracleGap 1 riskA riskAc = 0 := by
  rw [actualBinaryOracleGap_representation 1 riskA riskAc
    (by norm_num) (by norm_num) hA hAc]
  exact abstractOracleGap_zero_of_right_weight_zero
    (excessAboveInfimum riskA) (excessAboveInfimum riskAc)
    (sInf_excessAboveInfimum_eq_zero riskA hA)

omit [Nonempty S] [OpensMeasurableSpace S] in
/-- A positive-weight component of a finite-risk binary mixture has finite
risk. -/
theorem frechetRisk_lt_top_left_of_binaryMixture
    (p : ℝ) (nuA nuAc : Measure S) (s : S)
    (hp : 0 < p)
    (hMixture : frechetRisk (binaryMixtureMeasure p nuA nuAc) s < ∞) :
    frechetRisk nuA s < ∞ := by
  rw [frechetRisk_binaryMixture] at hMixture
  have hWeighted : ENNReal.ofReal p * frechetRisk nuA s < ∞ :=
    (ENNReal.add_lt_top.1 hMixture).1
  exact ENNReal.lt_top_of_mul_ne_top_right hWeighted.ne
    (ENNReal.ofReal_ne_zero_iff.mpr hp)

omit [Nonempty S] [OpensMeasurableSpace S] in
/-- The complementary positive-weight component of a finite-risk binary
mixture has finite risk. -/
theorem frechetRisk_lt_top_right_of_binaryMixture
    (p : ℝ) (nuA nuAc : Measure S) (s : S)
    (hp : p < 1)
    (hMixture : frechetRisk (binaryMixtureMeasure p nuA nuAc) s < ∞) :
    frechetRisk nuAc s < ∞ := by
  rw [frechetRisk_binaryMixture] at hMixture
  have hWeighted : ENNReal.ofReal (1 - p) * frechetRisk nuAc s < ∞ :=
    (ENNReal.add_lt_top.1 hMixture).2
  exact ENNReal.lt_top_of_mul_ne_top_right hWeighted.ne
    (ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr hp))

/-- The exact Fréchet binary-oracle identity needs only finiteness of the
mixture risk.  At an interior probability this implies finiteness of both
branches; at an endpoint the identity reduces algebraically to zero. -/
theorem actual_frechet_binary_oracle_gap_of_mixture_finite
    (p : ℝ) (nuA nuAc : Measure S)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hFiniteMixture : ∀ s : S,
      frechetRisk (binaryMixtureMeasure p nuA nuAc) s ≠ ∞) :
    actualBinaryOracleGap p
        (frechetRiskReal nuA) (frechetRiskReal nuAc) =
      (frechetVariance (binaryMixtureMeasure p nuA nuAc)).toReal -
        (p * (frechetVariance nuA).toReal +
          (1 - p) * (frechetVariance nuAc).toReal) := by
  by_cases hpZero : p = 0
  · subst p
    have hUnresolved : binaryUnresolvedRisk 0
        (frechetRiskReal nuA) (frechetRiskReal nuAc) =
        frechetRiskReal nuAc := by
      funext s
      simp [binaryUnresolvedRisk]
    rw [actualBinaryOracleGap, hUnresolved]
    simp [binaryResolvedRisk, binaryMixtureMeasure]
  by_cases hpOne : p = 1
  · subst p
    have hUnresolved : binaryUnresolvedRisk 1
        (frechetRiskReal nuA) (frechetRiskReal nuAc) =
        frechetRiskReal nuA := by
      funext s
      simp [binaryUnresolvedRisk]
    rw [actualBinaryOracleGap, hUnresolved]
    simp [binaryResolvedRisk, binaryMixtureMeasure]
  have hpPositive : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hpZero)
  have hpLessOne : p < 1 := lt_of_le_of_ne hp1 hpOne
  have hFiniteA : ∀ s : S, frechetRisk nuA s ≠ ∞ := by
    intro s
    exact (frechetRisk_lt_top_left_of_binaryMixture
      p nuA nuAc s hpPositive (lt_top_iff_ne_top.2 (hFiniteMixture s))).ne
  have hFiniteAc : ∀ s : S, frechetRisk nuAc s ≠ ∞ := by
    intro s
    exact (frechetRisk_lt_top_right_of_binaryMixture
      p nuA nuAc s hpLessOne (lt_top_iff_ne_top.2 (hFiniteMixture s))).ne
  exact actual_frechet_binary_oracle_gap p nuA nuAc
    hp0 hp1 hFiniteA hFiniteAc

end DeterministicClosure

section RandomClosure

variable {Omega : Type*} {mOmega : MeasurableSpace Omega}

/-- Closed regular-conditional-law form of the Fréchet binary-oracle theorem.

Unlike `actual_binary_oracle_frechet_refinement`, this theorem has no separate
branch-finiteness hypotheses.  They are derived from the coarse conditional law
on the interior-probability event, and are not needed at the endpoints. -/
theorem actual_binary_oracle_frechet_refinement_closed
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
    (hMoment : Integrable (fun omega ↦ dist (K omega) s0 ^ 2) mu) :
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
      (fun omega ↦ (frechetVariance (kappaFine omega)).toReal) mu
    exact hFineWell.2.2.2
  have hCondFine :=
    condExp_posteriorFrechetVariance_binaryOracleKernel
      mu mSmall mLarge hSmallLarge hLargeAmbient A hA
        kappaA kappaAc hFineInt
  have hGainWell := frechetRefinementGain_wellPosed
    mu mSmall mLarge hSmallLarge hLargeAmbient K hK
      kappaCoarse kappaFine hCoarseRCD hFineRCD s0 hMoment
  have hMixtureFinite : ∀ᵐ omega ∂mu,
      ∀ s : S, frechetRisk (kappaCoarse omega) s < ∞ :=
    posteriorFrechetRisk_finite_everywhere_ae
      mu mSmall (hSmallLarge.trans hLargeAmbient) K hK
        kappaCoarse hCoarseRCD s0 hMoment
  have hGamma : Gamma =ᵐ[mu] Gap := by
    filter_upwards [hCondFine, hMixtureFinite] with
        omega hCondOmega hFiniteOmega
    have hpOmega := boundedBinaryEventProbability_bounds
      mu mSmall A omega
    have hActual := actual_frechet_binary_oracle_gap_of_mixture_finite
      (p omega) (kappaA omega) (kappaAc omega)
      hpOmega.1 hpOmega.2 (by
        intro s
        have hs := hFiniteOmega s
        change frechetRisk
          (binaryMixtureMeasure (p omega) (kappaA omega) (kappaAc omega)) s < ∞ at hs
        exact hs.ne)
    dsimp only [Gamma, Gap, binaryOracleFrechetGain,
      actualFrechetBinaryOracleGapRCD, frechetRefinementGain,
      refinementGain, kappaCoarse, kappaFine]
    rw [hCondOmega]
    simpa only [posteriorFrechetVarianceReal,
      binaryEventMixtureKernel_apply, p] using hActual.symm
  have hGammaMeasurable : StronglyMeasurable[mSmall] Gamma := hGainWell.1
  have hGammaIntegrable : Integrable Gamma mu := hGainWell.2.1
  have hGammaNonnegative : 0 ≤ᵐ[mu] Gamma := hGainWell.2.2
  have hGDef : G = {omega | 0 < Gamma omega} := by rfl
  have hGMeasurable : MeasurableSet[mSmall] G := by
    rw [hGDef]
    exact measurableSet_lt measurable_const hGammaMeasurable.measurable
  have hGCharacterization : ∀ᵐ omega ∂mu,
      omega ∈ G ↔
        0 < p omega ∧ p omega < 1 ∧
        ¬HasCommonApproxMinimizingSequence
          (excessAboveInfimum (frechetRiskReal (kappaA omega)))
          (excessAboveInfimum (frechetRiskReal (kappaAc omega))) := by
    filter_upwards [hGamma] with omega hGammaOmega
    have hpOmega := boundedBinaryEventProbability_bounds mu mSmall A omega
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
    have hNotPositive : ¬0 < Gamma omega := fun hPositive ↦ hNotG hPositive
    exact le_antisymm (le_of_not_gt hNotPositive) hNonnegativeOmega
  have hIntegralCriterion :
      (0 < ∫ omega, Gamma omega ∂mu) ↔ 0 < mu G := by
    exact strict_oracle_gap_integral_pos_iff mu Gamma G
      hGammaNonnegative hGammaIntegrable
      (Filter.Eventually.of_forall fun _ ↦ Iff.rfl)
  simpa only [Gamma, Gap, G, p] using
    ⟨hGamma, hGammaMeasurable, hGammaIntegrable,
      hGammaNonnegative, hGMeasurable, hGCharacterization,
      hZeroOutside, hIntegralCriterion⟩

/-- Quantitative binary-oracle lower bound with no branch-finiteness premises. -/
theorem binaryOracleFrechetGain_lower_bound_of_disjoint_sublevels_closed
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
    (hDisjoint : ∀ᵐ omega ∂mu,
      Disjoint
        {s | excessAboveInfimum (frechetRiskReal (kappaA omega)) s < epsilon}
        {s | excessAboveInfimum (frechetRiskReal (kappaAc omega)) s < epsilon}) :
    (fun omega ↦
      min (boundedBinaryEventProbability mu mSmall A omega)
          (1 - boundedBinaryEventProbability mu mSmall A omega) * epsilon) ≤ᵐ[mu]
      binaryOracleFrechetGain mu mSmall mLarge hSmallLarge
        A hA kappaA kappaAc := by
  filter_upwards [hGamma, hDisjoint] with
      omega hGammaOmega hDisjointOmega
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

end RandomClosure

end

end SequentialLearning
