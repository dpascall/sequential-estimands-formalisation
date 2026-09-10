import SequentialLearning.MSEHierarchy
import SequentialLearning.HilbertLearningCriterion
import SequentialLearning.FixedTargetLearning

/-!
# Closed dynamics of the mean squared error hierarchy

`MSEHierarchy.lean` proved the hierarchy's dynamics conditional on the
fixed-target posterior-variance process already being a supermartingale.  This
file discharges that hypothesis in the Hilbert representation used by the MSE
section, using the conditional total-variance identity.
-/

namespace SequentialLearning

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal MeasureTheory ProbabilityTheory RealInnerProductSpace

noncomputable section

section MSEHierarchyDynamics

variable {Omega H : Type*} {mOmega : MeasurableSpace Omega}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Hilbert fixed-target learning in the exact representation used by the MSE
section.  The information gain between any two filtration stages is the
conditional squared norm of the posterior-mean innovation, so posterior
variance is a nonnegative supermartingale. -/
theorem hilbertFixedTargetVariance_learning
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration ℕ mOmega)
    (KLimit : Omega → H) (hKLimit : MemLp KLimit 2 mu) :
    (∀ n, 0 ≤ᵐ[mu] posteriorVariance mu (filtration n) KLimit) ∧
    Supermartingale
      (fun n => posteriorVariance mu (filtration n) KLimit)
      filtration mu := by
  have hNonnegative : ∀ n,
      0 ≤ᵐ[mu] posteriorVariance mu (filtration n) KLimit := by
    intro n
    simpa only [posteriorVariance] using
      posteriorMSE_nonnegative mu (filtration n) KLimit KLimit
  refine ⟨hNonnegative, ?_, ?_, ?_⟩
  · intro n
    dsimp only [posteriorVariance, posteriorMSE]
    exact stronglyMeasurable_condExp
  · intro i j hij
    have hRefinement := posteriorVariance_refinement_hilbert
      mu (filtration i) (filtration j) (filtration.mono hij)
        (filtration.le j) KLimit hKLimit
    have hInnovationNonnegative :
        0 ≤ᵐ[mu]
          mu[(fun omega =>
            ‖oldTargetInnovation mu (filtration i) (filtration j)
              KLimit omega‖ ^ 2) | filtration i] := by
      apply condExp_nonneg
      filter_upwards with omega
      exact sq_nonneg _
    filter_upwards [hRefinement, hInnovationNonnegative] with
        omega hRefinementOmega hInnovationOmega
    rw [hRefinementOmega]
    exact le_add_of_nonneg_right hInnovationOmega
  · intro n
    dsimp only [posteriorVariance, posteriorMSE]
    exact integrable_condExp

omit [CompleteSpace H] in
/-- The gap between the full MSE upper bound and terminal-target posterior
variance is exactly the conditional squared discrepancy, pointwise. -/
theorem fullMSEUpperBound_gap
    (mu : Measure[mOmega] Omega) (m : MeasurableSpace Omega)
    (KLimit KCurrent : Omega → H) :
    (fun omega =>
      fullMSEUpperBound mu m KLimit KCurrent omega -
        posteriorVariance mu m KLimit omega) =
      conditionalSquaredDiscrepancy mu m KLimit KCurrent := by
  funext omega
  simp [fullMSEUpperBound]

/-- Closed dynamic part of the MSE hierarchy.  No separate fixed-target
learning hypothesis remains: terminal-target posterior variance, conditional
squared discrepancy, and their sum are all nonnegative supermartingales. -/
theorem mean_squared_error_hierarchy_dynamics_closed
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration ℕ mOmega)
    (KLimit : Omega → H) (K : ℕ → Omega → H)
    (hKLimit : MemLp KLimit 2 mu) (hK : ∀ n, MemLp (K n) 2 mu)
    (hMonotone : ∀ i j, i ≤ j → ∀ omega,
      limitDiscrepancy KLimit (K j) omega ≤
        limitDiscrepancy KLimit (K i) omega) :
    (∀ n, 0 ≤ᵐ[mu] posteriorVariance mu (filtration n) KLimit) ∧
      Supermartingale
        (fun n => posteriorVariance mu (filtration n) KLimit)
        filtration mu ∧
    (∀ n, 0 ≤ᵐ[mu]
      conditionalSquaredDiscrepancy mu (filtration n) KLimit (K n)) ∧
      Supermartingale
        (fun n => conditionalSquaredDiscrepancy
          mu (filtration n) KLimit (K n)) filtration mu ∧
    (∀ n, 0 ≤ᵐ[mu]
      fullMSEUpperBound mu (filtration n) KLimit (K n)) ∧
      Supermartingale
        (fun n => fullMSEUpperBound mu (filtration n) KLimit (K n))
        filtration mu := by
  have hFixedTargetLearning :=
    (hilbertFixedTargetVariance_learning
      mu filtration KLimit hKLimit).2
  exact mean_squared_error_hierarchy_dynamics
    mu filtration KLimit K hKLimit hK hMonotone hFixedTargetLearning

/-- Complete manuscript theorem: the four-term stagewise MSE hierarchy and
the supermartingale dynamics of its lower endpoint, upper endpoint, and gap. -/
theorem mean_squared_error_hierarchy_complete
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration ℕ mOmega)
    (KLimit : Omega → H) (K : ℕ → Omega → H)
    (hKLimitMeasurable : StronglyMeasurable[mOmega] KLimit)
    (hKMeasurable : ∀ n, StronglyMeasurable[mOmega] (K n))
    (hKLimit : MemLp KLimit 2 mu) (hK : ∀ n, MemLp (K n) 2 mu)
    (hMonotone : ∀ i j, i ≤ j → ∀ omega,
      limitDiscrepancy KLimit (K j) omega ≤
        limitDiscrepancy KLimit (K i) omega) :
    (∀ n, ∀ᵐ omega ∂mu,
      posteriorVariance mu (filtration n) KLimit omega ≤
          posteriorMSE mu (filtration n) KLimit (K n) omega ∧
        posteriorMSE mu (filtration n) KLimit (K n) omega ≤
          weightedMSEUpperBound mu (filtration n) KLimit (K n) omega ∧
        weightedMSEUpperBound mu (filtration n) KLimit (K n) omega ≤
          fullMSEUpperBound mu (filtration n) KLimit (K n) omega) ∧
    ((∀ n, 0 ≤ᵐ[mu] posteriorVariance mu (filtration n) KLimit) ∧
      Supermartingale
        (fun n => posteriorVariance mu (filtration n) KLimit)
        filtration mu ∧
    (∀ n, 0 ≤ᵐ[mu]
      conditionalSquaredDiscrepancy mu (filtration n) KLimit (K n)) ∧
      Supermartingale
        (fun n => conditionalSquaredDiscrepancy
          mu (filtration n) KLimit (K n)) filtration mu ∧
    (∀ n, 0 ≤ᵐ[mu]
      fullMSEUpperBound mu (filtration n) KLimit (K n)) ∧
      Supermartingale
        (fun n => fullMSEUpperBound mu (filtration n) KLimit (K n))
        filtration mu) := by
  refine ⟨?_, mean_squared_error_hierarchy_dynamics_closed
    mu filtration KLimit K hKLimit hK hMonotone⟩
  intro n
  exact mean_squared_error_hierarchy
    mu (filtration n) (filtration.le n) KLimit (K n)
      hKLimitMeasurable (hKMeasurable n) hKLimit (hK n)

end MSEHierarchyDynamics

end

end SequentialLearning
