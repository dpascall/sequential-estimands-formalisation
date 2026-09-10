import SequentialLearning.ObservedProcess
import SequentialLearning.ConditionalStochasticDomination
import SequentialLearning.TailSupermartingale
import SequentialLearning.IncreasingLoss
import SequentialLearning.ClosedIncreasingLoss
import SequentialLearning.MSEHierarchyDynamics
import SequentialLearning.FixedEstimandMSEClosed

/-!
# Taxonomy-facing tail and MSE results

These wrappers consume a `RealizedObservedProcess` and class membership.  The
measurability, moment, monotonicity, fixedness, and absorbing-coverage premises
required by the analytic core are obtained from the process bundle and the
definition of the selected manuscript class; callers do not restate them.
-/

namespace SequentialLearning

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal MeasureTheory ProbabilityTheory

noncomputable section

universe uOmega uS uPrefix

namespace HypotheticalSequentialEstimand
namespace StructuralPresentation

variable {Omega : Type uOmega} {S : Type uS} {Prefix : Type uPrefix}
  {mOmega : MeasurableSpace Omega}
  (K : HypotheticalSequentialEstimand Omega S Prefix)
  (A : K.StructuralPresentation)

section PseudometricResults

variable [PseudoMetricSpace S] [ENorm S]
  (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
  (R : RealizedObservedProcess K A mu)

omit [IsProbabilityMeasure mu] in
/-- For an absorbing taxonomy row, realised persistence is measurable at
every stage and agrees with equality to the terminal estimand outside one
null set, simultaneously for all stages. -/
theorem absorbingClass_process_persistence_event
    (c : AbsorbingEstimandClass)
    (hClass : HasClass K A mu c.toEstimandClass) :
    (∀ n, MeasurableSet (R.persistenceEvent K A n)) ∧
      ∀ᵐ omega ∂mu, ∀ n,
        omega ∈ R.persistenceEvent K A n ↔
          R.value K A n omega = K.limit omega := by
  refine ⟨R.measurableSet_persistenceEvent K A, ?_⟩
  exact R.persistenceEvent_iff_value_eq_of_absorbingCoverage K A
    (c.hasClass_absorbingCoverage K A mu hClass)

omit [IsProbabilityMeasure mu] in
/-- Monotone-class membership supplies pairwise antitonicity of the realised
discrepancy sequence. -/
theorem monotoneClass_process_discrepancy_antitone
    (c : MonotoneEstimandClass)
    (hClass : HasClass K A mu c.toEstimandClass) :
    ∀ ⦃n k : ℕ⦄, n ≤ k → ∀ omega,
      R.discrepancy K A k omega ≤ R.discrepancy K A n omega := by
  intro n k hnk omega
  exact R.discrepancy_antitone K A
    (c.hasClass_isMonotone K A mu hClass) hnk omega

/-- Class-facing form of `tailorder`.  The RCDs remain explicit mathematical
objects, but their stochastic order no longer requires a separately supplied
discrepancy-monotonicity hypothesis. -/
theorem monotoneClass_conditional_stochastic_domination_sequence
    (c : MonotoneEstimandClass)
    (hClass : HasClass K A mu c.toEstimandClass)
    (m : MeasurableSpace Omega) (hm : m ≤ mOmega)
    (nu : ℕ → Kernel[m, (inferInstance : MeasurableSpace ℝ)] Omega ℝ)
    (hnuMarkov : ∀ n, IsMarkovKernel (nu n))
    (hnu : ∀ n,
      IsRegularConditionalRealLaw mu m (R.discrepancy K A n) (nu n)) :
    ∀ {n k : ℕ}, n ≤ k →
      ∀ᵐ omega ∂mu, TailStochasticLE (nu k omega) (nu n omega) := by
  apply conditional_stochastic_domination_sequence
    mu m hm (R.discrepancy K A) nu hnuMarkov
      (R.discrepancy_measurable K A) hnu
  intro n
  exact ae_of_all mu
    (monotoneClass_process_discrepancy_antitone
      K A mu R c hClass (Nat.le_succ n))

/-- Class-facing form of `tailsupermart`. -/
theorem monotoneClass_conditional_tail_supermartingale
    (c : MonotoneEstimandClass)
    (hClass : HasClass K A mu c.toEstimandClass) (t : ℝ) :
    (∀ n, 0 ≤ᵐ[mu]
        conditionalTailProbability mu (R.filtration n)
          (R.discrepancy K A n) t ∧
      conditionalTailProbability mu (R.filtration n)
          (R.discrepancy K A n) t ≤ᵐ[mu] 1) ∧
    Supermartingale
      (fun n => conditionalTailProbability mu (R.filtration n)
        (R.discrepancy K A n) t) R.filtration mu := by
  apply conditional_tail_supermartingale
    mu R.filtration (R.discrepancy K A) t
      (R.discrepancy_measurable K A)
  intro n
  exact ae_of_all mu
    (monotoneClass_process_discrepancy_antitone
      K A mu R c hClass (Nat.le_succ n))

/-- Exact class-facing form of `tailloss`. Monotonicity of the transform on
the non-negative half-line supplies all measurability needed after constant-
left extension; discrepancy measurability, nonnegativity, and stagewise
decrease come from the process and class membership. -/
theorem monotoneClass_conditional_increasing_loss_supermartingale
    (c : MonotoneEstimandClass)
    (hClass : HasClass K A mu c.toEstimandClass)
    (g : ℝ → ℝ) (hg : MonotoneOn g (Set.Ici 0))
    (hIntegrability :
      (∃ C : ℝ, ∀ r : ℝ, 0 ≤ r → |g r| ≤ C) ∨
        Integrable (fun omega => g (R.discrepancy K A 0 omega)) mu) :
    Supermartingale
      (fun n => conditionalExpectedLoss mu (R.filtration n)
        (R.discrepancy K A n) g) R.filtration mu := by
  apply conditional_increasing_loss_supermartingale_nonnegative
    mu R.filtration (R.discrepancy K A) g hg
      (R.discrepancy_measurable K A)
      (R.discrepancy_nonnegative K A)
  · intro n
    exact ae_of_all mu
      (monotoneClass_process_discrepancy_antitone
        K A mu R c hClass (Nat.le_succ n))
  · exact hIntegrability

end PseudometricResults

section HilbertResults

variable {H : Type uS}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (KH : HypotheticalSequentialEstimand Omega H Prefix)
  (AH : KH.StructuralPresentation)
  (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
  (R : RealizedObservedProcess KH AH mu)

/-- Class-facing complete MSE hierarchy.  The caller supplies a monotone
taxonomy row and its `HasClass` proof; the pointwise discrepancy order is
derived internally. -/
theorem monotoneClass_mean_squared_error_hierarchy_complete
    (c : MonotoneEstimandClass)
    (hClass : HasClass KH AH mu c.toEstimandClass) :
    (∀ n, ∀ᵐ omega ∂mu,
      posteriorVariance mu (R.filtration n) KH.limit omega ≤
          posteriorMSE mu (R.filtration n) KH.limit (R.value KH AH n) omega ∧
        posteriorMSE mu (R.filtration n) KH.limit (R.value KH AH n) omega ≤
          weightedMSEUpperBound mu (R.filtration n) KH.limit
            (R.value KH AH n) omega ∧
        weightedMSEUpperBound mu (R.filtration n) KH.limit
            (R.value KH AH n) omega ≤
          fullMSEUpperBound mu (R.filtration n) KH.limit
            (R.value KH AH n) omega) ∧
    ((∀ n, 0 ≤ᵐ[mu] posteriorVariance mu (R.filtration n) KH.limit) ∧
      Supermartingale
        (fun n => posteriorVariance mu (R.filtration n) KH.limit)
        R.filtration mu ∧
    (∀ n, 0 ≤ᵐ[mu]
      conditionalSquaredDiscrepancy mu (R.filtration n) KH.limit
        (R.value KH AH n)) ∧
      Supermartingale
        (fun n => conditionalSquaredDiscrepancy mu (R.filtration n)
          KH.limit (R.value KH AH n)) R.filtration mu ∧
    (∀ n, 0 ≤ᵐ[mu]
      fullMSEUpperBound mu (R.filtration n) KH.limit (R.value KH AH n)) ∧
      Supermartingale
        (fun n => fullMSEUpperBound mu (R.filtration n)
          KH.limit (R.value KH AH n)) R.filtration mu) := by
  apply mean_squared_error_hierarchy_complete
    mu R.filtration KH.limit (R.value KH AH)
      R.limitStronglyMeasurable (R.value_stronglyMeasurable KH AH)
      R.limitMemLp (R.value_memLp KH AH)
  intro i j hij omega
  simpa only [RealizedObservedProcess.discrepancy,
    limitDiscrepancy, dist_eq_norm] using
      monotoneClass_process_discrepancy_antitone
        KH AH mu R c hClass hij omega

/-- Process-level absorbing MSE bound.  Stage-event measurability is part of
the conclusion and comes from the observed-process bundle. -/
theorem absorbingClass_process_mse_bound
    (c : AbsorbingEstimandClass)
    (hClass : HasClass KH AH mu c.toEstimandClass) :
    (∀ n, MeasurableSet (R.persistenceEvent KH AH n)) ∧
    ∀ n, ∀ᵐ omega ∂mu,
      posteriorMSE mu (R.filtration n) KH.limit (R.value KH AH n) omega ≤
        posteriorVariance mu (R.filtration n) KH.limit omega +
          (mu⟦(R.persistenceEvent KH AH n)ᶜ | R.filtration n⟧) omega *
            conditionalSquaredDiscrepancy mu (R.filtration n)
              KH.limit (R.value KH AH n) omega := by
  refine ⟨R.measurableSet_persistenceEvent KH AH, ?_⟩
  have hProcessEvent := absorbingClass_process_persistence_event
    KH AH mu R c hClass
  intro n
  have hPersistence : ∀ omega,
      omega ∈ R.persistenceEvent KH AH n →
        R.value KH AH n omega = KH.limit omega := by
    intro omega homega
    exact realizedPersistence_implies_equality KH AH (R.stage KH AH n)
      omega homega
  have hAbsorbing : ∀ᵐ omega ∂mu,
      R.value KH AH n omega = KH.limit omega →
        omega ∈ R.persistenceEvent KH AH n := by
    filter_upwards [hProcessEvent.2] with omega homega
    exact (homega n).2
  exact absorbing_classes_mse_bound
    mu (R.filtration n) (R.filtration.le n)
      KH.limit (R.value KH AH n) (R.persistenceEvent KH AH n)
      R.limitStronglyMeasurable (R.value_stronglyMeasurable KH AH n)
      R.limitMemLp (R.value_memLp KH AH n) hPersistence hAbsorbing

/-- Class-facing fixed-estimand MSE corollary.  The equality of every stage
with the terminal estimand is obtained directly from `.fixed` membership. -/
theorem fixedClass_process_mse_corollary
    (hClass : HasClass KH AH mu .fixed) :
    (∀ n,
      posteriorMSE mu (R.filtration n) KH.limit (R.value KH AH n) =
          posteriorVariance mu (R.filtration n) KH.limit ∧
        weightedMSEUpperBound mu (R.filtration n) KH.limit
            (R.value KH AH n) =
          posteriorVariance mu (R.filtration n) KH.limit ∧
        fullMSEUpperBound mu (R.filtration n) KH.limit
            (R.value KH AH n) =
          posteriorVariance mu (R.filtration n) KH.limit) ∧
      (∀ n, 0 ≤ᵐ[mu]
        posteriorMSE mu (R.filtration n) KH.limit (R.value KH AH n)) ∧
      Supermartingale
        (fun n => posteriorMSE mu (R.filtration n)
          KH.limit (R.value KH AH n)) R.filtration mu := by
  apply fixed_estimand_mse_corollary_closed
    mu R.filtration KH.limit (R.value KH AH)
  · exact R.value_eq_limit_of_fixed KH AH
      (hasClass_isFixed KH AH mu hClass)
  · exact R.limitMemLp

end HilbertResults

end StructuralPresentation
end HypotheticalSequentialEstimand

end

end SequentialLearning
