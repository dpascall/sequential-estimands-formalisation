import SequentialLearning.StrictOracleGap
import SequentialLearning.FrechetRefinement

/-!
# Actual value of a binary oracle

This file identifies the reduction in optimal risk obtained by revealing a
binary latent status.  The general identity is purely order-theoretic.  It is
then specialised to finite-second-moment Frechet risks and lifted pointwise to
random posterior branch risks.
-/

namespace SequentialLearning

open Filter MeasureTheory Set
open scoped ENNReal MeasureTheory ProbabilityTheory Topology

noncomputable section

section DeterministicBinaryOracleGap

variable {S : Type*} [Nonempty S]

/-- Risk before the binary branch is revealed. -/
def binaryUnresolvedRisk
    (p : ℝ) (riskA riskAc : S → ℝ) (s : S) : ℝ :=
  p * riskA s + (1 - p) * riskAc s

/-- Optimal risk after the binary branch is revealed. -/
def binaryResolvedRisk
    (p : ℝ) (riskA riskAc : S → ℝ) : ℝ :=
  p * sInf (Set.range riskA) +
    (1 - p) * sInf (Set.range riskAc)

/-- The actual binary-oracle gap: optimal unresolved risk minus optimal
resolved risk. -/
def actualBinaryOracleGap
    (p : ℝ) (riskA riskAc : S → ℝ) : ℝ :=
  sInf (Set.range (binaryUnresolvedRisk p riskA riskAc)) -
    binaryResolvedRisk p riskA riskAc

/-- Translation commutes with the infimum of a nonempty, bounded-below
real-valued range. -/
theorem sInf_range_add_const
    (f : S → ℝ) (c : ℝ) (hBounded : BddBelow (Set.range f)) :
    sInf (Set.range (fun s => f s + c)) =
      sInf (Set.range f) + c := by
  have hRange : Set.range (fun s => f s + c) =
      (fun x : ℝ => x + c) '' Set.range f := by
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨f s, ⟨s, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
      exact ⟨s, rfl⟩
  rw [hRange]
  exact ((OrderIso.addRight c).map_csInf'
    (Set.range_nonempty f) hBounded).symm

omit [Nonempty S] in
/-- Unresolved risk is resolved risk plus the weighted branch excesses. -/
theorem binaryRisk_eq_mixtureExcess_add_resolved
    (p : ℝ) (riskA riskAc : S → ℝ) (s : S) :
    binaryUnresolvedRisk p riskA riskAc s =
      oracleMixtureExcess p
          (excessAboveInfimum riskA)
          (excessAboveInfimum riskAc) s +
        binaryResolvedRisk p riskA riskAc := by
  simp only [binaryUnresolvedRisk, oracleMixtureExcess,
    excessAboveInfimum, binaryResolvedRisk]
  ring

/-- The actual gap equals the abstract weighted infimum of the two branch
excess-risk functions. -/
theorem actualBinaryOracleGap_representation
    (p : ℝ) (riskA riskAc : S → ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hA : BddBelow (Set.range riskA))
    (hAc : BddBelow (Set.range riskAc)) :
    actualBinaryOracleGap p riskA riskAc =
      abstractOracleGap p
        (excessAboveInfimum riskA)
        (excessAboveInfimum riskAc) := by
  let c := binaryResolvedRisk p riskA riskAc
  have hMixtureBounded : BddBelow
      (Set.range (oracleMixtureExcess p
        (excessAboveInfimum riskA)
        (excessAboveInfimum riskAc))) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨s, rfl⟩
    exact oracleMixtureExcess_nonnegative p
      (excessAboveInfimum riskA) (excessAboveInfimum riskAc)
      hp0 hp1
      (excessAboveInfimum_nonnegative riskA hA)
      (excessAboveInfimum_nonnegative riskAc hAc) s
  have hFunction : binaryUnresolvedRisk p riskA riskAc =
      fun s => oracleMixtureExcess p
          (excessAboveInfimum riskA)
          (excessAboveInfimum riskAc) s + c := by
    funext s
    exact binaryRisk_eq_mixtureExcess_add_resolved p riskA riskAc s
  rw [actualBinaryOracleGap, hFunction,
    sInf_range_add_const _ c hMixtureBounded]
  simp [abstractOracleGap, c]

/-- The actual binary-oracle gap is nonnegative. -/
theorem actualBinaryOracleGap_nonnegative
    (p : ℝ) (riskA riskAc : S → ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hA : BddBelow (Set.range riskA))
    (hAc : BddBelow (Set.range riskAc)) :
    0 ≤ actualBinaryOracleGap p riskA riskAc := by
  rw [actualBinaryOracleGap_representation p riskA riskAc
    hp0 hp1 hA hAc]
  exact abstractOracleGap_nonnegative p
    (excessAboveInfimum riskA) (excessAboveInfimum riskAc)
    hp0 hp1
    (excessAboveInfimum_nonnegative riskA hA)
    (excessAboveInfimum_nonnegative riskAc hAc)

/-- Strict actual oracle value is equivalent to an interior branch
probability and failure of simultaneous approximate minimisation. -/
theorem actualBinaryOracleGap_pos_iff
    (p : ℝ) (riskA riskAc : S → ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hA : BddBelow (Set.range riskA))
    (hAc : BddBelow (Set.range riskAc)) :
    0 < actualBinaryOracleGap p riskA riskAc ↔
      0 < p ∧ p < 1 ∧
        ¬HasCommonApproxMinimizingSequence
          (excessAboveInfimum riskA)
          (excessAboveInfimum riskAc) := by
  rw [actualBinaryOracleGap_representation p riskA riskAc
    hp0 hp1 hA hAc]
  exact abstractOracleGap_strict_iff p
    (excessAboveInfimum riskA) (excessAboveInfimum riskAc)
    hp0 hp1
    (excessAboveInfimum_nonnegative riskA hA)
    (excessAboveInfimum_nonnegative riskAc hAc)
    (sInf_excessAboveInfimum_eq_zero riskA hA)
    (sInf_excessAboveInfimum_eq_zero riskAc hAc)

end DeterministicBinaryOracleGap

section FrechetBinaryOracleGap

variable {S : Type*} [PseudoMetricSpace S] [MeasurableSpace S]
  [Nonempty S] [OpensMeasurableSpace S]

/-- Real-valued Frechet risk on the finite-second-moment branch. -/
def frechetRiskReal (nu : Measure S) (s : S) : ℝ :=
  (frechetRisk nu s).toReal

/-- Mixture of the two posterior branch laws. -/
def binaryMixtureMeasure
    (p : ℝ) (nuA nuAc : Measure S) : Measure S :=
  ENNReal.ofReal p • nuA + ENNReal.ofReal (1 - p) • nuAc

/-- The infimum of real Frechet risk is the real Frechet variance whenever
all centre risks are finite. -/
theorem sInf_frechetRiskReal
    (nu : Measure S)
    (hFinite : ∀ s : S, frechetRisk nu s ≠ ∞) :
    sInf (Set.range (frechetRiskReal nu)) =
      (frechetVariance nu).toReal := by
  rw [frechetVariance, ENNReal.toReal_iInf hFinite]
  exact sInf_range

omit [Nonempty S] [OpensMeasurableSpace S] in
/-- Frechet risk under the mixture law is the corresponding mixture of
branch risks. -/
theorem frechetRisk_binaryMixture
    (p : ℝ) (nuA nuAc : Measure S) (s : S) :
    frechetRisk (binaryMixtureMeasure p nuA nuAc) s =
      ENNReal.ofReal p * frechetRisk nuA s +
        ENNReal.ofReal (1 - p) * frechetRisk nuAc s := by
  simp only [frechetRisk_eq_lintegral, binaryMixtureMeasure,
    lintegral_add_measure, lintegral_smul_measure, smul_eq_mul]

/-- Real form of the preceding mixture identity. -/
theorem frechetRiskReal_binaryMixture
    (p : ℝ) (nuA nuAc : Measure S) (s : S)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hFiniteA : frechetRisk nuA s ≠ ∞)
    (hFiniteAc : frechetRisk nuAc s ≠ ∞) :
    frechetRiskReal (binaryMixtureMeasure p nuA nuAc) s =
      p * frechetRiskReal nuA s +
        (1 - p) * frechetRiskReal nuAc s := by
  rw [frechetRiskReal, frechetRisk_binaryMixture]
  rw [ENNReal.toReal_add]
  · rw [ENNReal.toReal_mul, ENNReal.toReal_mul]
    simp [frechetRiskReal, ENNReal.toReal_ofReal hp0,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hp1)]
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hFiniteA
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hFiniteAc

/-- For finite branch second moments, the exact reduction in optimal
Frechet risk is the actual binary-oracle gap of the two branch risks. -/
theorem actual_frechet_binary_oracle_gap
    (p : ℝ) (nuA nuAc : Measure S)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hFiniteA : ∀ s : S, frechetRisk nuA s ≠ ∞)
    (hFiniteAc : ∀ s : S, frechetRisk nuAc s ≠ ∞) :
    actualBinaryOracleGap p
        (frechetRiskReal nuA) (frechetRiskReal nuAc) =
      (frechetVariance (binaryMixtureMeasure p nuA nuAc)).toReal -
        (p * (frechetVariance nuA).toReal +
          (1 - p) * (frechetVariance nuAc).toReal) := by
  have hFiniteMixture : ∀ s : S,
      frechetRisk (binaryMixtureMeasure p nuA nuAc) s ≠ ∞ := by
    intro s
    rw [frechetRisk_binaryMixture]
    exact ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hFiniteA s),
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hFiniteAc s)⟩
  have hRiskFunction : binaryUnresolvedRisk p
      (frechetRiskReal nuA) (frechetRiskReal nuAc) =
        frechetRiskReal (binaryMixtureMeasure p nuA nuAc) := by
    funext s
    exact (frechetRiskReal_binaryMixture p nuA nuAc s
      hp0 hp1 (hFiniteA s) (hFiniteAc s)).symm
  simp only [actualBinaryOracleGap, binaryResolvedRisk]
  rw [hRiskFunction, sInf_frechetRiskReal _ hFiniteMixture,
    sInf_frechetRiskReal nuA hFiniteA,
    sInf_frechetRiskReal nuAc hFiniteAc]

end FrechetBinaryOracleGap

section RandomBinaryOracleGap

variable {Omega S : Type*} {mOmega : MeasurableSpace Omega} [Nonempty S]

/-- Pointwise actual gap for random posterior branch risks. -/
def randomActualBinaryOracleGap
    (p : Omega → ℝ) (riskA riskAc : Omega → S → ℝ) : Omega → ℝ :=
  fun omega => actualBinaryOracleGap (p omega)
    (riskA omega) (riskAc omega)

/-- A measurable version of the strict-value event. -/
def measurableBinaryOracleStrictEvent
    (p : Omega → ℝ) (riskA riskAc : Omega → S → ℝ) : Set Omega :=
  {omega | 0 < randomActualBinaryOracleGap p riskA riskAc omega}

/-- Complete pointwise binary-oracle representation and strictness result.
Measurability is stated for the selected actual-gap version; this avoids
claiming measurability of the sequence-defined event before a version has
been fixed. -/
theorem actual_binary_oracle_gap_and_measurable_strictness
    (mu : Measure[mOmega] Omega)
    (p : Omega → ℝ) (riskA riskAc : Omega → S → ℝ)
    (hp : ∀ᵐ omega ∂mu, 0 ≤ p omega ∧ p omega ≤ 1)
    (hA : ∀ᵐ omega ∂mu, BddBelow (Set.range (riskA omega)))
    (hAc : ∀ᵐ omega ∂mu, BddBelow (Set.range (riskAc omega)))
    (hMeasurable : StronglyMeasurable[mOmega]
      (randomActualBinaryOracleGap p riskA riskAc)) :
    (0 ≤ᵐ[mu] randomActualBinaryOracleGap p riskA riskAc) ∧
      MeasurableSet[mOmega]
        (measurableBinaryOracleStrictEvent p riskA riskAc) ∧
      (∀ᵐ omega ∂mu,
        omega ∈ measurableBinaryOracleStrictEvent p riskA riskAc ↔
          0 < p omega ∧ p omega < 1 ∧
            ¬HasCommonApproxMinimizingSequence
              (excessAboveInfimum (riskA omega))
              (excessAboveInfimum (riskAc omega))) := by
  have hNonnegative : 0 ≤ᵐ[mu]
      randomActualBinaryOracleGap p riskA riskAc := by
    filter_upwards [hp, hA, hAc] with omega hpomega hAomega hAcomega
    exact actualBinaryOracleGap_nonnegative
      (p omega) (riskA omega) (riskAc omega)
      hpomega.1 hpomega.2 hAomega hAcomega
  have hEventMeasurable : MeasurableSet[mOmega]
      (measurableBinaryOracleStrictEvent p riskA riskAc) := by
    exact measurableSet_lt measurable_const hMeasurable.measurable
  refine ⟨hNonnegative, hEventMeasurable, ?_⟩
  filter_upwards [hp, hA, hAc] with omega hpomega hAomega hAcomega
  change 0 < randomActualBinaryOracleGap p riskA riskAc omega ↔ _
  exact actualBinaryOracleGap_pos_iff
    (p omega) (riskA omega) (riskAc omega)
    hpomega.1 hpomega.2 hAomega hAcomega

/-- A nonnegative integrable actual oracle gap is valuable in expectation
exactly when its measurable strict-value event has positive probability. -/
theorem actual_binary_oracle_integral_pos_iff
    (mu : Measure[mOmega] Omega)
    (p : Omega → ℝ) (riskA riskAc : Omega → S → ℝ)
    (hNonnegative : 0 ≤ᵐ[mu]
      randomActualBinaryOracleGap p riskA riskAc)
    (hIntegrable : Integrable
      (randomActualBinaryOracleGap p riskA riskAc) mu) :
    (0 < ∫ omega,
        randomActualBinaryOracleGap p riskA riskAc omega ∂mu) ↔
      0 < mu (measurableBinaryOracleStrictEvent p riskA riskAc) := by
  exact strict_oracle_gap_integral_pos_iff mu
    (randomActualBinaryOracleGap p riskA riskAc)
    (measurableBinaryOracleStrictEvent p riskA riskAc)
    hNonnegative hIntegrable (Filter.Eventually.of_forall fun _ => Iff.rfl)

end RandomBinaryOracleGap

end

end SequentialLearning
