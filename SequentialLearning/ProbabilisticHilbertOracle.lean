import SequentialLearning.BinaryOracleGap
import SequentialLearning.OracleHilbertGap

/-!
# Complete probabilistic Hilbert oracle formula

For squared Hilbert loss, branch risk is branch variance plus squared distance
from the branch posterior mean.  The variance terms cancel from the actual
binary-oracle gap, leaving the between-branch posterior variance.
-/

namespace SequentialLearning

open Filter MeasureTheory Set
open scoped ENNReal MeasureTheory ProbabilityTheory RealInnerProductSpace

noncomputable section

section DeterministicHilbertBranchRisk

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nonempty H]

/-- Squared-error Bayes risk within one posterior branch. -/
def hilbertBranchRisk (variance : ℝ) (mean s : H) : ℝ :=
  variance + ‖s - mean‖ ^ 2

/-- The branch posterior mean attains the branch variance, which is the least
branch risk. -/
theorem hilbertBranchRisk_isLeast (variance : ℝ) (mean : H) :
    IsLeast (Set.range (hilbertBranchRisk variance mean)) variance := by
  constructor
  · exact ⟨mean, by simp [hilbertBranchRisk]⟩
  · rintro _ ⟨s, rfl⟩
    exact le_add_of_nonneg_right (sq_nonneg _)

/-- Infimum of a Hilbert branch risk. -/
theorem sInf_hilbertBranchRisk (variance : ℝ) (mean : H) :
    sInf (Set.range (hilbertBranchRisk variance mean)) = variance := by
  exact (hilbertBranchRisk_isLeast variance mean).csInf_eq

/-- Excess above the optimal branch risk is exactly squared displacement
from the branch mean. -/
theorem excess_hilbertBranchRisk
    (variance : ℝ) (mean s : H) :
    excessAboveInfimum (hilbertBranchRisk variance mean) s =
      ‖s - mean‖ ^ 2 := by
  rw [excessAboveInfimum, sInf_hilbertBranchRisk]
  simp [hilbertBranchRisk]

/-- The actual Hilbert binary-oracle gap has the between-branch variance
formula; the within-branch variances cancel exactly. -/
theorem actualHilbertBinaryOracleGap_formula
    (p varianceA varianceAc : ℝ) (meanA meanAc : H)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    actualBinaryOracleGap p
        (hilbertBranchRisk varianceA meanA)
        (hilbertBranchRisk varianceAc meanAc) =
      p * (1 - p) * ‖meanA - meanAc‖ ^ 2 := by
  have hBoundA : BddBelow
      (Set.range (hilbertBranchRisk varianceA meanA)) :=
    ⟨varianceA, (hilbertBranchRisk_isLeast varianceA meanA).2⟩
  have hBoundAc : BddBelow
      (Set.range (hilbertBranchRisk varianceAc meanAc)) :=
    ⟨varianceAc, (hilbertBranchRisk_isLeast varianceAc meanAc).2⟩
  rw [actualBinaryOracleGap_representation p
    (hilbertBranchRisk varianceA meanA)
    (hilbertBranchRisk varianceAc meanAc) hp0 hp1 hBoundA hBoundAc]
  have hExcessA : excessAboveInfimum
      (hilbertBranchRisk varianceA meanA) =
        fun s => ‖s - meanA‖ ^ 2 := by
    funext s
    exact excess_hilbertBranchRisk varianceA meanA s
  have hExcessAc : excessAboveInfimum
      (hilbertBranchRisk varianceAc meanAc) =
        fun s => ‖s - meanAc‖ ^ 2 := by
    funext s
    exact excess_hilbertBranchRisk varianceAc meanAc s
  rw [hExcessA, hExcessAc]
  change sInf (Set.range (weightedBranchRisk p meanA meanAc)) = _
  exact sInf_weightedBranchRisk p meanA meanAc

/-- Strictness of the actual Hilbert oracle gap. -/
theorem actualHilbertBinaryOracleGap_pos_iff
    (p varianceA varianceAc : ℝ) (meanA meanAc : H)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 < actualBinaryOracleGap p
        (hilbertBranchRisk varianceA meanA)
        (hilbertBranchRisk varianceAc meanAc) ↔
      0 < p ∧ p < 1 ∧ meanA ≠ meanAc := by
  rw [actualHilbertBinaryOracleGap_formula
    p varianceA varianceAc meanA meanAc hp0 hp1]
  exact hilbertOracleGap_pos_iff p meanA meanAc hp0 hp1

end DeterministicHilbertBranchRisk

section RandomHilbertOracle

variable {Omega H : Type*} {mOmega : MeasurableSpace Omega}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nonempty H]

/-- Actual oracle gap formed from random Hilbert branch risks. -/
def randomActualHilbertOracleGap
    (p varianceA varianceAc : Omega → ℝ)
    (meanA meanAc : Omega → H) : Omega → ℝ :=
  fun omega => actualBinaryOracleGap (p omega)
    (hilbertBranchRisk (varianceA omega) (meanA omega))
    (hilbertBranchRisk (varianceAc omega) (meanAc omega))

/-- The exact strict-value event in Hilbert space. -/
def hilbertBinaryOracleStrictEvent
    (p : Omega → ℝ) (meanA meanAc : Omega → H) : Set Omega :=
  {omega | 0 < p omega ∧ p omega < 1 ∧ meanA omega ≠ meanAc omega}

/-- Complete probabilistic Hilbert-oracle theorem: exact gap, nonnegativity,
strictness, measurability of the strict event, and the positive-expectation
criterion. -/
theorem complete_probabilistic_hilbert_oracle
    (mu : Measure[mOmega] Omega)
    (p varianceA varianceAc : Omega → ℝ)
    (meanA meanAc : Omega → H)
    (hp : ∀ omega, 0 ≤ p omega ∧ p omega ≤ 1)
    (hpMeasurable : StronglyMeasurable[mOmega] p)
    (hMeanAMeasurable : StronglyMeasurable[mOmega] meanA)
    (hMeanAcMeasurable : StronglyMeasurable[mOmega] meanAc)
    (hIntegrable : Integrable
      (randomActualHilbertOracleGap
        p varianceA varianceAc meanA meanAc) mu) :
    (randomActualHilbertOracleGap
        p varianceA varianceAc meanA meanAc =
      fun omega =>
        p omega * (1 - p omega) *
          ‖meanA omega - meanAc omega‖ ^ 2) ∧
    (∀ omega, 0 ≤ randomActualHilbertOracleGap
      p varianceA varianceAc meanA meanAc omega) ∧
    MeasurableSet[mOmega]
      (hilbertBinaryOracleStrictEvent p meanA meanAc) ∧
    (∀ omega,
      0 < randomActualHilbertOracleGap
          p varianceA varianceAc meanA meanAc omega ↔
        omega ∈ hilbertBinaryOracleStrictEvent p meanA meanAc) ∧
    ((0 < ∫ omega,
        randomActualHilbertOracleGap
          p varianceA varianceAc meanA meanAc omega ∂mu) ↔
      0 < mu (hilbertBinaryOracleStrictEvent p meanA meanAc)) := by
  have hFormula : randomActualHilbertOracleGap
      p varianceA varianceAc meanA meanAc =
      fun omega => p omega * (1 - p omega) *
        ‖meanA omega - meanAc omega‖ ^ 2 := by
    funext omega
    exact actualHilbertBinaryOracleGap_formula
      (p omega) (varianceA omega) (varianceAc omega)
      (meanA omega) (meanAc omega) (hp omega).1 (hp omega).2
  have hNonnegative : ∀ omega,
      0 ≤ randomActualHilbertOracleGap
        p varianceA varianceAc meanA meanAc omega := by
    intro omega
    rw [hFormula]
    exact mul_nonneg
      (mul_nonneg (hp omega).1 (sub_nonneg.mpr (hp omega).2))
      (sq_nonneg _)
  have hStrict : ∀ omega,
      0 < randomActualHilbertOracleGap
          p varianceA varianceAc meanA meanAc omega ↔
        omega ∈ hilbertBinaryOracleStrictEvent p meanA meanAc := by
    intro omega
    change 0 < randomActualHilbertOracleGap
      p varianceA varianceAc meanA meanAc omega ↔
        0 < p omega ∧ p omega < 1 ∧ meanA omega ≠ meanAc omega
    exact actualHilbertBinaryOracleGap_pos_iff
      (p omega) (varianceA omega) (varianceAc omega)
      (meanA omega) (meanAc omega) (hp omega).1 (hp omega).2
  have hGapMeasurable : StronglyMeasurable[mOmega]
      (randomActualHilbertOracleGap
        p varianceA varianceAc meanA meanAc) := by
    rw [hFormula]
    exact (hpMeasurable.mul
      (stronglyMeasurable_const.sub hpMeasurable)).mul
        ((hMeanAMeasurable.sub hMeanAcMeasurable).norm.pow 2)
  have hEventMeasurable : MeasurableSet[mOmega]
      (hilbertBinaryOracleStrictEvent p meanA meanAc) := by
    have hSet : hilbertBinaryOracleStrictEvent p meanA meanAc =
        {omega | 0 < randomActualHilbertOracleGap
          p varianceA varianceAc meanA meanAc omega} := by
      ext omega
      exact (hStrict omega).symm
    rw [hSet]
    exact measurableSet_lt measurable_const hGapMeasurable.measurable
  have hIntegral :
      (0 < ∫ omega,
          randomActualHilbertOracleGap
            p varianceA varianceAc meanA meanAc omega ∂mu) ↔
        0 < mu (hilbertBinaryOracleStrictEvent p meanA meanAc) := by
    exact strict_oracle_gap_integral_pos_iff mu
      (randomActualHilbertOracleGap
        p varianceA varianceAc meanA meanAc)
      (hilbertBinaryOracleStrictEvent p meanA meanAc)
      (Filter.Eventually.of_forall hNonnegative)
      hIntegrable (Filter.Eventually.of_forall hStrict)
  exact ⟨hFormula, hNonnegative, hEventMeasurable, hStrict, hIntegral⟩

end RandomHilbertOracle

end

end SequentialLearning
