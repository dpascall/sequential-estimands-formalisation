import SequentialLearning.ThreeWayRefinement
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Hilbert form of the absorption-oracle gap

This file formalises Corollary `oraclehilbert`.  Its deterministic core is the
completion-of-squares identity for a two-component mixture in a real Hilbert
space.  The probability-theoretic corollary is obtained by applying that
identity pointwise to the posterior branch probability and branch means.
-/

namespace SequentialLearning

open Filter MeasureTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

noncomputable section

section OracleHilbertGap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Posterior mean obtained by mixing the two oracle branches. -/
def weightedBranchMean (p : ℝ) (mA mAc : H) : H :=
  p • mA + (1 - p) • mAc

/-- Excess squared risk before the binary oracle status is revealed. -/
def weightedBranchRisk (p : ℝ) (mA mAc s : H) : ℝ :=
  p * ‖s - mA‖ ^ 2 + (1 - p) * ‖s - mAc‖ ^ 2

/-- The weighted two-branch squared risk is a squared distance from the
mixture mean plus the between-branch variance. -/
theorem weightedBranchRisk_decomposition
    (p : ℝ) (mA mAc s : H) :
    weightedBranchRisk p mA mAc s =
      ‖s - weightedBranchMean p mA mAc‖ ^ 2 +
        p * (1 - p) * ‖mA - mAc‖ ^ 2 := by
  simp only [weightedBranchRisk, weightedBranchMean]
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    inner_add_left, inner_add_right, real_inner_smul_left, inner_smul_right]
  ring

/-- Every candidate has weighted risk at least the between-branch term. -/
theorem hilbertOracleGap_le_weightedBranchRisk
    (p : ℝ) (mA mAc s : H) :
    p * (1 - p) * ‖mA - mAc‖ ^ 2 ≤
      weightedBranchRisk p mA mAc s := by
  rw [weightedBranchRisk_decomposition p mA mAc s]
  exact le_add_of_nonneg_left (sq_nonneg _)

/-- The mixture mean attains the lower bound. -/
theorem weightedBranchRisk_at_weightedBranchMean
    (p : ℝ) (mA mAc : H) :
    weightedBranchRisk p mA mAc (weightedBranchMean p mA mAc) =
      p * (1 - p) * ‖mA - mAc‖ ^ 2 := by
  rw [weightedBranchRisk_decomposition p mA mAc
    (weightedBranchMean p mA mAc)]
  simp

/-- The mixture mean is the unique minimiser of the weighted two-branch risk.
This remains true at `p = 0` and `p = 1` for the particular completion-of-
squares representation, although the unused branch mean is then irrelevant to
the original statistical interpretation. -/
theorem weightedBranchRisk_eq_gap_iff
    (p : ℝ) (mA mAc s : H) :
    weightedBranchRisk p mA mAc s =
        p * (1 - p) * ‖mA - mAc‖ ^ 2 ↔
      s = weightedBranchMean p mA mAc := by
  rw [weightedBranchRisk_decomposition p mA mAc s]
  constructor
  · intro h
    have hsq : ‖s - weightedBranchMean p mA mAc‖ ^ 2 = 0 := by
      linarith
    have hsub : s - weightedBranchMean p mA mAc = 0 := by
      simpa using hsq
    exact sub_eq_zero.mp hsub
  · rintro rfl
    simp

/-- The range of the weighted risk has the oracle gap as its least element. -/
theorem weightedBranchRisk_isLeast
    (p : ℝ) (mA mAc : H) :
    IsLeast (Set.range (weightedBranchRisk p mA mAc))
      (p * (1 - p) * ‖mA - mAc‖ ^ 2) := by
  constructor
  · exact ⟨weightedBranchMean p mA mAc,
      weightedBranchRisk_at_weightedBranchMean p mA mAc⟩
  · rintro _ ⟨s, rfl⟩
    exact hilbertOracleGap_le_weightedBranchRisk p mA mAc s

/-- The infimum in the oracle-gain formula is attained and has the familiar
between-branch variance form. -/
theorem sInf_weightedBranchRisk
    (p : ℝ) (mA mAc : H) :
    sInf (Set.range (weightedBranchRisk p mA mAc)) =
      p * (1 - p) * ‖mA - mAc‖ ^ 2 := by
  exact (weightedBranchRisk_isLeast p mA mAc).csInf_eq

omit [InnerProductSpace ℝ H] in
/-- The Hilbert oracle gap is strictly positive exactly when both branches
have positive posterior weight and their conditional means differ. -/
theorem hilbertOracleGap_pos_iff
    (p : ℝ) (mA mAc : H) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 < p * (1 - p) * ‖mA - mAc‖ ^ 2 ↔
      0 < p ∧ p < 1 ∧ mA ≠ mAc := by
  constructor
  · intro hgap
    have hpne0 : p ≠ 0 := by
      intro hp
      simp [hp] at hgap
    have hpne1 : p ≠ 1 := by
      intro hp
      simp [hp] at hgap
    have hmeans : mA ≠ mAc := by
      intro h
      simp [h] at hgap
    exact ⟨lt_of_le_of_ne hp0 (Ne.symm hpne0),
      lt_of_le_of_ne hp1 hpne1, hmeans⟩
  · rintro ⟨hp, hp_lt_one, hmeans⟩
    exact mul_pos (mul_pos hp (sub_pos.mpr hp_lt_one))
      (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hmeans)))

section RandomOracleGap

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- Pointwise lifting of the deterministic Hilbert calculation.  The input
`hGamma` is precisely the general oracle-gap representation obtained before
specialising to Hilbert space. -/
theorem hilbert_absorption_oracle_gap
    (μ : Measure[m0] Ω)
    (p : Ω → ℝ) (mA mAc : Ω → H) (Gamma : Ω → ℝ)
    (hp : ∀ᵐ ω ∂μ, 0 ≤ p ω ∧ p ω ≤ 1)
    (hGamma : Gamma =ᵐ[μ] fun ω =>
      sInf (Set.range (weightedBranchRisk (p ω) (mA ω) (mAc ω)))) :
    (Gamma =ᵐ[μ] fun ω =>
      p ω * (1 - p ω) * ‖mA ω - mAc ω‖ ^ 2) ∧
    (∀ᵐ ω ∂μ,
      0 < Gamma ω ↔ 0 < p ω ∧ p ω < 1 ∧ mA ω ≠ mAc ω) := by
  have hFormula : Gamma =ᵐ[μ] fun ω =>
      p ω * (1 - p ω) * ‖mA ω - mAc ω‖ ^ 2 := by
    filter_upwards [hp, hGamma] with ω hpω hGammaω
    rw [hGammaω]
    exact sInf_weightedBranchRisk (p ω) (mA ω) (mAc ω)
  refine ⟨hFormula, ?_⟩
  filter_upwards [hp, hFormula] with ω hpω hFormulaω
  rw [hFormulaω]
  exact hilbertOracleGap_pos_iff (p ω) (mA ω) (mAc ω) hpω.1 hpω.2

/-- If the general strict-oracle theorem has already identified `G` with the
positive-gap event, the Hilbert calculation turns it into the intersection of
unresolved branch status and unequal branch means. -/
theorem hilbert_strict_oracle_event_characterization
    (μ : Measure[m0] Ω)
    (p : Ω → ℝ) (mA mAc : Ω → H) (Gamma : Ω → ℝ) (G : Set Ω)
    (hp : ∀ᵐ ω ∂μ, 0 ≤ p ω ∧ p ω ≤ 1)
    (hGamma : Gamma =ᵐ[μ] fun ω =>
      sInf (Set.range (weightedBranchRisk (p ω) (mA ω) (mAc ω))))
    (hG : ∀ᵐ ω ∂μ, ω ∈ G ↔ 0 < Gamma ω) :
    ∀ᵐ ω ∂μ,
      ω ∈ G ↔ 0 < p ω ∧ p ω < 1 ∧ mA ω ≠ mAc ω := by
  have hStrict :=
    (hilbert_absorption_oracle_gap μ p mA mAc Gamma hp hGamma).2
  filter_upwards [hG, hStrict] with ω hGω hStrictω
  exact hGω.trans hStrictω

end RandomOracleGap

end OracleHilbertGap

end

end SequentialLearning
