import SequentialLearning.FixedEstimandMSE
import SequentialLearning.MSEHierarchyDynamics

namespace SequentialLearning
open Filter MeasureTheory ProbabilityTheory
open scoped MeasureTheory ProbabilityTheory
noncomputable section
section FixedEstimandMSEClosed

variable {Omega H : Type*} {mOmega : MeasurableSpace Omega}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem fixed_estimand_mse_corollary_closed
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration ℕ mOmega)
    (KLimit : Omega → H) (K : ℕ → Omega → H)
    (hFixed : ∀ n, K n = KLimit)
    (hKLimit : MemLp KLimit 2 mu) :
    (∀ n,
      posteriorMSE mu (filtration n) KLimit (K n) =
          posteriorVariance mu (filtration n) KLimit ∧
        weightedMSEUpperBound mu (filtration n) KLimit (K n) =
          posteriorVariance mu (filtration n) KLimit ∧
        fullMSEUpperBound mu (filtration n) KLimit (K n) =
          posteriorVariance mu (filtration n) KLimit) ∧
      (∀ n, 0 ≤ᵐ[mu]
        posteriorMSE mu (filtration n) KLimit (K n)) ∧
      Supermartingale
        (fun n => posteriorMSE mu (filtration n) KLimit (K n))
        filtration mu := by
  have hFixedTargetLearning :=
    (hilbertFixedTargetVariance_learning
      mu filtration KLimit hKLimit).2
  exact fixed_estimand_mse_corollary
    mu filtration KLimit K hFixed hFixedTargetLearning

end FixedEstimandMSEClosed
end
end SequentialLearning
