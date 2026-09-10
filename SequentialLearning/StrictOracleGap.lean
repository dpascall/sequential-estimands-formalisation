import SequentialLearning.OracleHilbertGap
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Strict value of a binary information oracle

This file formalises Proposition `oraclestrict` after the general Fréchet-risk
calculation has supplied two non-negative branch excess-risk functions.  The
core result characterises strict positivity of their weighted infimum by the
absence of a common approximate minimising sequence.
-/

namespace SequentialLearning

open Filter MeasureTheory Set
open scoped ENNReal MeasureTheory ProbabilityTheory Topology

noncomputable section

section DeterministicStrictOracleGap

variable {S : Type*} [Nonempty S]

/-- Excess risk above the infimum of a branch risk function. -/
def excessAboveInfimum (risk : S → ℝ) (s : S) : ℝ :=
  risk s - sInf (Set.range risk)

omit [Nonempty S] in
/-- Excess above an infimum is non-negative whenever the risk is bounded
below. -/
theorem excessAboveInfimum_nonnegative
    (risk : S → ℝ) (hBounded : BddBelow (Set.range risk)) :
    ∀ s, 0 ≤ excessAboveInfimum risk s := by
  intro s
  exact sub_nonneg.mpr (csInf_le hBounded ⟨s, rfl⟩)

/-- The infimum of the excess-above-infimum function is zero; no exact
minimiser is required. -/
theorem sInf_excessAboveInfimum_eq_zero
    (risk : S → ℝ) (hBounded : BddBelow (Set.range risk)) :
    sInf (Set.range (excessAboveInfimum risk)) = 0 := by
  apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
    (Set.range_nonempty _)
  · rintro _ ⟨s, rfl⟩
    exact excessAboveInfimum_nonnegative risk hBounded s
  · intro w hw
    have hInfLt : sInf (Set.range risk) < sInf (Set.range risk) + w := by
      linarith
    obtain ⟨_, ⟨s, rfl⟩, hs⟩ :=
      exists_lt_of_csInf_lt (Set.range_nonempty _) hInfLt
    refine ⟨excessAboveInfimum risk s, ⟨s, rfl⟩, ?_⟩
    dsimp [excessAboveInfimum]
    linarith

/-- Weighted branch excess risk before a binary status is revealed. -/
def oracleMixtureExcess (p : ℝ) (excessA excessAc : S → ℝ) (s : S) : ℝ :=
  p * excessA s + (1 - p) * excessAc s

/-- The value of resolving the binary status, represented as the infimum of
the weighted branch excess risks. -/
def abstractOracleGap (p : ℝ) (excessA excessAc : S → ℝ) : ℝ :=
  sInf (Set.range (oracleMixtureExcess p excessA excessAc))

/-- A single sequence asymptotically minimises both branch excess risks. -/
def HasCommonApproxMinimizingSequence
    (excessA excessAc : S → ℝ) : Prop :=
  ∃ s : ℕ → S,
    Tendsto (fun n => excessA (s n)) atTop (𝓝 0) ∧
      Tendsto (fun n => excessAc (s n)) atTop (𝓝 0)

/-- Epsilon-form of simultaneous approximate minimisation. -/
def HasArbitrarilySmallCommonExcess
    (excessA excessAc : S → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ s : S, excessA s < ε ∧ excessAc s < ε

omit [Nonempty S] in
/-- The sequential and epsilon formulations of a common approximate minimiser
are equivalent for non-negative real excess risks. -/
theorem hasCommonApproxMinimizingSequence_iff
    (excessA excessAc : S → ℝ)
    (hA : ∀ s, 0 ≤ excessA s) (hAc : ∀ s, 0 ≤ excessAc s) :
    HasCommonApproxMinimizingSequence excessA excessAc ↔
      HasArbitrarilySmallCommonExcess excessA excessAc := by
  constructor
  · rintro ⟨s, hsA, hsAc⟩ ε hε
    have hAEventually : ∀ᶠ n in atTop, excessA (s n) < ε :=
      hsA.eventually (Iio_mem_nhds hε)
    have hAcEventually : ∀ᶠ n in atTop, excessAc (s n) < ε :=
      hsAc.eventually (Iio_mem_nhds hε)
    obtain ⟨n, hnA, hnAc⟩ := (hAEventually.and hAcEventually).exists
    exact ⟨s n, hnA, hnAc⟩
  · intro hSmall
    classical
    have hεpos : ∀ n : ℕ, 0 < (1 : ℝ) / ((n : ℝ) + 1) := by
      intro n
      positivity
    choose s hsA hsAc using fun n : ℕ =>
      hSmall (1 / ((n : ℝ) + 1)) (hεpos n)
    refine ⟨s, ?_, ?_⟩
    · exact squeeze_zero (fun n => hA (s n))
        (fun n => (hsA n).le)
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    · exact squeeze_zero (fun n => hAc (s n))
        (fun n => (hsAc n).le)
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

omit [Nonempty S] in
/-- Weighted excess risk is non-negative when the branch weights and branch
excess risks are non-negative. -/
theorem oracleMixtureExcess_nonnegative
    (p : ℝ) (excessA excessAc : S → ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hA : ∀ s, 0 ≤ excessA s) (hAc : ∀ s, 0 ≤ excessAc s) :
    ∀ s, 0 ≤ oracleMixtureExcess p excessA excessAc s := by
  intro s
  exact add_nonneg (mul_nonneg hp0 (hA s))
    (mul_nonneg (sub_nonneg.mpr hp1) (hAc s))

/-- The abstract oracle gap is non-negative. -/
theorem abstractOracleGap_nonnegative
    (p : ℝ) (excessA excessAc : S → ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hA : ∀ s, 0 ≤ excessA s) (hAc : ∀ s, 0 ≤ excessAc s) :
    0 ≤ abstractOracleGap p excessA excessAc := by
  apply le_csInf (Set.range_nonempty _)
  rintro _ ⟨s, rfl⟩
  exact oracleMixtureExcess_nonnegative p excessA excessAc hp0 hp1 hA hAc s

/-- At an interior branch probability, the weighted infimum is zero exactly
when the two branch excess risks can be made simultaneously arbitrarily small. -/
theorem abstractOracleGap_eq_zero_iff_small
    (p : ℝ) (excessA excessAc : S → ℝ)
    (hp0 : 0 < p) (hp1 : p < 1)
    (hA : ∀ s, 0 ≤ excessA s) (hAc : ∀ s, 0 ≤ excessAc s) :
    abstractOracleGap p excessA excessAc = 0 ↔
      HasArbitrarilySmallCommonExcess excessA excessAc := by
  have hp0' : 0 ≤ p := hp0.le
  have hp1' : p ≤ 1 := hp1.le
  have hq0 : 0 < 1 - p := sub_pos.mpr hp1
  constructor
  · intro hGap ε hε
    have hδ : 0 < min (p * ε) ((1 - p) * ε) := by
      exact lt_min (mul_pos hp0 hε) (mul_pos hq0 hε)
    have hInfLt :
        abstractOracleGap p excessA excessAc <
          min (p * ε) ((1 - p) * ε) := by
      rw [hGap]
      exact hδ
    obtain ⟨_, ⟨s, rfl⟩, hs⟩ :=
      exists_lt_of_csInf_lt (Set.range_nonempty _) hInfLt
    have hpA_le :
        p * excessA s ≤ oracleMixtureExcess p excessA excessAc s := by
      dsimp [oracleMixtureExcess]
      exact le_add_of_nonneg_right (mul_nonneg hq0.le (hAc s))
    have hqAc_le :
        (1 - p) * excessAc s ≤ oracleMixtureExcess p excessA excessAc s := by
      dsimp [oracleMixtureExcess]
      exact le_add_of_nonneg_left (mul_nonneg hp0' (hA s))
    have hpA_lt : p * excessA s < p * ε :=
      hpA_le.trans_lt (hs.trans_le (min_le_left _ _))
    have hqAc_lt : (1 - p) * excessAc s < (1 - p) * ε :=
      hqAc_le.trans_lt (hs.trans_le (min_le_right _ _))
    have hsA : excessA s < ε := by nlinarith
    have hsAc : excessAc s < ε := by nlinarith
    exact ⟨s, hsA, hsAc⟩
  · intro hSmall
    apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
      (Set.range_nonempty _)
    · rintro _ ⟨s, rfl⟩
      exact oracleMixtureExcess_nonnegative p excessA excessAc
        hp0' hp1' hA hAc s
    · intro w hw
      obtain ⟨s, hsA, hsAc⟩ := hSmall w hw
      refine ⟨oracleMixtureExcess p excessA excessAc s, ⟨s, rfl⟩, ?_⟩
      have hpPart : p * excessA s < p * w :=
        mul_lt_mul_of_pos_left hsA hp0
      have hqPart : (1 - p) * excessAc s < (1 - p) * w :=
        mul_lt_mul_of_pos_left hsAc hq0
      dsimp [oracleMixtureExcess]
      linarith

/-- At an interior branch probability, a zero gap is equivalent to the
common-approximate-minimising-sequence condition used in the manuscript. -/
theorem abstractOracleGap_eq_zero_iff_commonSequence
    (p : ℝ) (excessA excessAc : S → ℝ)
    (hp0 : 0 < p) (hp1 : p < 1)
    (hA : ∀ s, 0 ≤ excessA s) (hAc : ∀ s, 0 ≤ excessAc s) :
    abstractOracleGap p excessA excessAc = 0 ↔
      HasCommonApproxMinimizingSequence excessA excessAc := by
  rw [abstractOracleGap_eq_zero_iff_small p excessA excessAc hp0 hp1 hA hAc]
  exact (hasCommonApproxMinimizingSequence_iff excessA excessAc hA hAc).symm

/-- Equivalently, strict oracle value at an interior branch probability is the
absence of a common approximate minimising sequence. -/
theorem abstractOracleGap_pos_iff_no_commonSequence
    (p : ℝ) (excessA excessAc : S → ℝ)
    (hp0 : 0 < p) (hp1 : p < 1)
    (hA : ∀ s, 0 ≤ excessA s) (hAc : ∀ s, 0 ≤ excessAc s) :
    0 < abstractOracleGap p excessA excessAc ↔
      ¬HasCommonApproxMinimizingSequence excessA excessAc := by
  have hGapNonnegative := abstractOracleGap_nonnegative p excessA excessAc
    hp0.le hp1.le hA hAc
  have hZero := abstractOracleGap_eq_zero_iff_commonSequence
    p excessA excessAc hp0 hp1 hA hAc
  constructor
  · intro hPositive hCommon
    have hGapZero := hZero.mpr hCommon
    linarith
  · intro hNoCommon
    have hGapNe : abstractOracleGap p excessA excessAc ≠ 0 := by
      intro hGapZero
      exact hNoCommon (hZero.mp hGapZero)
    exact lt_of_le_of_ne hGapNonnegative (Ne.symm hGapNe)

omit [Nonempty S] in
/-- When the first branch has zero weight, the oracle gap is the infimum of
the second branch excess risk and hence vanishes. -/
theorem abstractOracleGap_zero_of_left_weight_zero
    (excessA excessAc : S → ℝ)
    (hInfAc : sInf (Set.range excessAc) = 0) :
    abstractOracleGap 0 excessA excessAc = 0 := by
  have hFunction : oracleMixtureExcess 0 excessA excessAc = excessAc := by
    funext s
    simp [oracleMixtureExcess]
  rw [abstractOracleGap, hFunction, hInfAc]

omit [Nonempty S] in
/-- Symmetric endpoint result when the second branch has zero weight. -/
theorem abstractOracleGap_zero_of_right_weight_zero
    (excessA excessAc : S → ℝ)
    (hInfA : sInf (Set.range excessA) = 0) :
    abstractOracleGap 1 excessA excessAc = 0 := by
  have hFunction : oracleMixtureExcess 1 excessA excessAc = excessA := by
    funext s
    simp [oracleMixtureExcess]
  rw [abstractOracleGap, hFunction, hInfA]

/-- Disjoint epsilon-sublevel sets give the manuscript's quantitative lower
bound on the oracle gap. -/
theorem abstractOracleGap_lower_bound_of_disjoint_sublevels
    (p ε : ℝ) (excessA excessAc : S → ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 < ε)
    (hA : ∀ s, 0 ≤ excessA s) (hAc : ∀ s, 0 ≤ excessAc s)
    (hDisjoint :
      Disjoint {s | excessA s < ε} {s | excessAc s < ε}) :
    min p (1 - p) * ε ≤ abstractOracleGap p excessA excessAc := by
  apply le_csInf (Set.range_nonempty _)
  rintro _ ⟨s, rfl⟩
  have hNotBoth : ¬(excessA s < ε ∧ excessAc s < ε) := by
    rintro ⟨hsA, hsAc⟩
    exact (Set.disjoint_left.mp hDisjoint hsA) hsAc
  have hq0 : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  by_cases hsA : excessA s < ε
  · have hsAc : ε ≤ excessAc s := by
      exact le_of_not_gt fun h => hNotBoth ⟨hsA, h⟩
    have hMinWeight : min p (1 - p) * ε ≤ (1 - p) * ε :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) hε.le
    have hBranch : (1 - p) * ε ≤ (1 - p) * excessAc s :=
      mul_le_mul_of_nonneg_left hsAc hq0
    have hOther : 0 ≤ p * excessA s := mul_nonneg hp0 (hA s)
    dsimp [oracleMixtureExcess]
    linarith
  · have hsA' : ε ≤ excessA s := le_of_not_gt hsA
    have hMinWeight : min p (1 - p) * ε ≤ p * ε :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) hε.le
    have hBranch : p * ε ≤ p * excessA s :=
      mul_le_mul_of_nonneg_left hsA' hp0
    have hOther : 0 ≤ (1 - p) * excessAc s := mul_nonneg hq0 (hAc s)
    dsimp [oracleMixtureExcess]
    linarith

/-- Complete deterministic strictness theorem, including the two endpoint
branches.  The individual branch infima are needed only at `p = 0` or `p = 1`. -/
theorem abstractOracleGap_strict_iff
    (p : ℝ) (excessA excessAc : S → ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hA : ∀ s, 0 ≤ excessA s) (hAc : ∀ s, 0 ≤ excessAc s)
    (hInfA : sInf (Set.range excessA) = 0)
    (hInfAc : sInf (Set.range excessAc) = 0) :
    0 < abstractOracleGap p excessA excessAc ↔
      0 < p ∧ p < 1 ∧
        ¬HasCommonApproxMinimizingSequence excessA excessAc := by
  constructor
  · intro hGap
    have hpNeZero : p ≠ 0 := by
      intro hp
      subst p
      rw [abstractOracleGap_zero_of_left_weight_zero excessA excessAc hInfAc] at hGap
      exact (lt_irrefl 0) hGap
    have hpNeOne : p ≠ 1 := by
      intro hp
      subst p
      rw [abstractOracleGap_zero_of_right_weight_zero excessA excessAc hInfA] at hGap
      exact (lt_irrefl 0) hGap
    have hpPositive : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hpNeZero)
    have hpLessOne : p < 1 := lt_of_le_of_ne hp1 hpNeOne
    exact ⟨hpPositive, hpLessOne,
      (abstractOracleGap_pos_iff_no_commonSequence p excessA excessAc
        hpPositive hpLessOne hA hAc).mp hGap⟩
  · rintro ⟨hpPositive, hpLessOne, hNoCommon⟩
    exact (abstractOracleGap_pos_iff_no_commonSequence p excessA excessAc
      hpPositive hpLessOne hA hAc).mpr hNoCommon

/-- The complementary zero-gap formulation of the complete deterministic
strictness theorem. -/
theorem abstractOracleGap_eq_zero_iff_not_strict
    (p : ℝ) (excessA excessAc : S → ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hA : ∀ s, 0 ≤ excessA s) (hAc : ∀ s, 0 ≤ excessAc s)
    (hInfA : sInf (Set.range excessA) = 0)
    (hInfAc : sInf (Set.range excessAc) = 0) :
    abstractOracleGap p excessA excessAc = 0 ↔
      ¬(0 < p ∧ p < 1 ∧
        ¬HasCommonApproxMinimizingSequence excessA excessAc) := by
  have hNonnegative := abstractOracleGap_nonnegative p excessA excessAc
    hp0 hp1 hA hAc
  have hStrict := abstractOracleGap_strict_iff p excessA excessAc
    hp0 hp1 hA hAc hInfA hInfAc
  constructor
  · intro hZero hCondition
    have hPositive := hStrict.mpr hCondition
    linarith
  · intro hNotStrict
    by_contra hNotZero
    have hPositive : 0 < abstractOracleGap p excessA excessAc :=
      lt_of_le_of_ne hNonnegative (Ne.symm hNotZero)
    exact hNotStrict (hStrict.mp hPositive)

end DeterministicStrictOracleGap

section RandomStrictOracleGap

variable {Ω S : Type*} {m0 : MeasurableSpace Ω} [Nonempty S]

/-- The event used in the manuscript: both oracle branches remain possible
and there is no common approximate minimising sequence. -/
def strictOracleSequenceEvent
    (p : Ω → ℝ) (excessA excessAc : Ω → S → ℝ) : Set Ω :=
  {ω | 0 < p ω ∧ p ω < 1 ∧
    ¬HasCommonApproxMinimizingSequence (excessA ω) (excessAc ω)}

/-- Almost-sure form of the general strict-oracle theorem.  The assumptions
`hInfA` and `hInfAc` express that each branch function is an excess above its
own infimum. -/
theorem strict_oracle_gap_characterization
    (μ : Measure[m0] Ω)
    (p : Ω → ℝ) (excessA excessAc : Ω → S → ℝ) (Gamma : Ω → ℝ)
    (hp : ∀ᵐ ω ∂μ, 0 ≤ p ω ∧ p ω ≤ 1)
    (hNonnegative : ∀ᵐ ω ∂μ,
      ∀ s, 0 ≤ excessA ω s ∧ 0 ≤ excessAc ω s)
    (hInfA : ∀ᵐ ω ∂μ, sInf (Set.range (excessA ω)) = 0)
    (hInfAc : ∀ᵐ ω ∂μ, sInf (Set.range (excessAc ω)) = 0)
    (hGamma : Gamma =ᵐ[μ] fun ω =>
      abstractOracleGap (p ω) (excessA ω) (excessAc ω)) :
    (0 ≤ᵐ[μ] Gamma) ∧
    (∀ᵐ ω ∂μ,
      0 < Gamma ω ↔ ω ∈ strictOracleSequenceEvent p excessA excessAc) ∧
    (∀ᵐ ω ∂μ,
      ω ∉ strictOracleSequenceEvent p excessA excessAc → Gamma ω = 0) := by
  have hGammaNonnegative : 0 ≤ᵐ[μ] Gamma := by
    filter_upwards [hp, hNonnegative, hGamma] with ω hpω hNω hGammaω
    rw [hGammaω]
    exact abstractOracleGap_nonnegative
      (p ω) (excessA ω) (excessAc ω) hpω.1 hpω.2
        (fun s => (hNω s).1) (fun s => (hNω s).2)
  have hStrict : ∀ᵐ ω ∂μ,
      0 < Gamma ω ↔ ω ∈ strictOracleSequenceEvent p excessA excessAc := by
    filter_upwards [hp, hNonnegative, hInfA, hInfAc, hGamma] with
      ω hpω hNω hInfAω hInfAcω hGammaω
    rw [hGammaω]
    change 0 < abstractOracleGap (p ω) (excessA ω) (excessAc ω) ↔
      0 < p ω ∧ p ω < 1 ∧
        ¬HasCommonApproxMinimizingSequence (excessA ω) (excessAc ω)
    exact abstractOracleGap_strict_iff
      (p ω) (excessA ω) (excessAc ω) hpω.1 hpω.2
        (fun s => (hNω s).1) (fun s => (hNω s).2) hInfAω hInfAcω
  refine ⟨hGammaNonnegative, hStrict, ?_⟩
  filter_upwards [hGammaNonnegative, hStrict] with ω hNonnegativeω hStrictω
  intro hOutside
  by_contra hNonzero
  have hPositive : 0 < Gamma ω :=
    lt_of_le_of_ne hNonnegativeω (Ne.symm hNonzero)
  exact hOutside (hStrictω.mp hPositive)

/-- A non-negative integrable oracle gap is strictly valuable in expectation
exactly when its strict-value event has positive probability. -/
theorem strict_oracle_gap_integral_pos_iff
    (μ : Measure[m0] Ω) (Gamma : Ω → ℝ) (G : Set Ω)
    (hNonnegative : 0 ≤ᵐ[μ] Gamma) (hIntegrable : Integrable Gamma μ)
    (hG : ∀ᵐ ω ∂μ, 0 < Gamma ω ↔ ω ∈ G) :
    (0 < ∫ ω, Gamma ω ∂μ) ↔ 0 < μ G := by
  have hSupport : Function.support Gamma =ᵐ[μ] G := by
    filter_upwards [hNonnegative, hG] with ω hNonnegativeω hGω
    apply propext
    change (Gamma ω ≠ 0 ↔ ω ∈ G)
    constructor
    · intro hNonzero
      exact hGω.mp (lt_of_le_of_ne hNonnegativeω (Ne.symm hNonzero))
    · intro hIn hZero
      have hPositive := hGω.mpr hIn
      linarith
  have hMeasure : μ (Function.support Gamma) = μ G := measure_congr hSupport
  rw [integral_pos_iff_support_of_nonneg_ae hNonnegative hIntegrable,
    hMeasure]

/-- Under an almost-sure characterisation, the original sequence-defined
event is null-measurable.  Actual measurability requires an exact version or a
completed sigma-algebra. -/
theorem strictOracleSequenceEvent_nullMeasurable
    (μ : Measure[m0] Ω) (Gamma : Ω → ℝ) (G : Set Ω)
    (hGammaMeasurable : AEStronglyMeasurable Gamma μ)
    (hG : ∀ᵐ ω ∂μ, 0 < Gamma ω ↔ ω ∈ G) :
    NullMeasurableSet G μ := by
  have hPositive : NullMeasurableSet {ω | 0 < Gamma ω} μ :=
    nullMeasurableSet_lt aemeasurable_const hGammaMeasurable.aemeasurable
  have hSetAE : {ω | 0 < Gamma ω} =ᵐ[μ] G := by
    filter_upwards [hG] with ω hGω
    exact propext hGω
  exact hPositive.congr hSetAE

/-- If the strictness characterisation is made pointwise for chosen versions,
the sequence-defined event itself is measurable. -/
theorem strictOracleSequenceEvent_measurable_of_exact
    (m : MeasurableSpace Ω) (Gamma : Ω → ℝ) (G : Set Ω)
    (hGammaMeasurable : StronglyMeasurable[m] Gamma)
    (hG : ∀ ω, 0 < Gamma ω ↔ ω ∈ G) :
    MeasurableSet[m] G := by
  have hSet : G = {ω | 0 < Gamma ω} := by
    ext ω
    exact (hG ω).symm
  rw [hSet]
  exact measurableSet_lt measurable_const hGammaMeasurable.measurable

/-- Almost-sure random form of the quantitative epsilon-separation bound. -/
theorem strict_oracle_gap_lower_bound
    (μ : Measure[m0] Ω)
    (p : Ω → ℝ) (ε : ℝ)
    (excessA excessAc : Ω → S → ℝ) (Gamma : Ω → ℝ)
    (hε : 0 < ε)
    (hp : ∀ᵐ ω ∂μ, 0 ≤ p ω ∧ p ω ≤ 1)
    (hNonnegative : ∀ᵐ ω ∂μ,
      ∀ s, 0 ≤ excessA ω s ∧ 0 ≤ excessAc ω s)
    (hDisjoint : ∀ᵐ ω ∂μ,
      Disjoint {s | excessA ω s < ε} {s | excessAc ω s < ε})
    (hGamma : Gamma =ᵐ[μ] fun ω =>
      abstractOracleGap (p ω) (excessA ω) (excessAc ω)) :
    (fun ω => min (p ω) (1 - p ω) * ε) ≤ᵐ[μ] Gamma := by
  filter_upwards [hp, hNonnegative, hDisjoint, hGamma] with
    ω hpω hNω hDisjointω hGammaω
  rw [hGammaω]
  exact abstractOracleGap_lower_bound_of_disjoint_sublevels
    (p ω) ε (excessA ω) (excessAc ω) hpω.1 hpω.2 hε
      (fun s => (hNω s).1) (fun s => (hNω s).2) hDisjointω

end RandomStrictOracleGap

end

end SequentialLearning
