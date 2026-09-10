import SequentialLearning.FrechetWassersteinLipschitz
import Mathlib.Topology.MetricSpace.Completion

/-!
# Canonical metric completion of a pseudometric space

This is the geometric half of Result 16.  The direct Wasserstein distance on
the original measurable pseudometric space remains the definition from
`Wasserstein2`.  Here we construct the Polish target used to transport
regular conditional laws.
-/

namespace SequentialLearning

open Filter MeasureTheory Set
open scoped ENNReal MeasureTheory Topology

noncomputable section

/-- The completion of the metric separation quotient of `S`. -/
abbrev PseudometricCompletion (S : Type*) [PseudoMetricSpace S] :=
  UniformSpace.Completion (SeparationQuotient S)

instance {S : Type*} [PseudoMetricSpace S] [TopologicalSpace.SeparableSpace S] :
    TopologicalSpace.SeparableSpace (SeparationQuotient S) :=
  SeparationQuotient.isQuotientMap_mk.separableSpace

instance {S : Type*} [PseudoMetricSpace S] :
    MeasurableSpace (PseudometricCompletion S) :=
  borel (PseudometricCompletion S)

instance {S : Type*} [PseudoMetricSpace S] :
    BorelSpace (PseudometricCompletion S) :=
  ⟨rfl⟩

/-- Quotient first, then embed into the metric completion. -/
def completionEmbedding {S : Type*} [PseudoMetricSpace S] :
    S → PseudometricCompletion S :=
  fun x => UniformSpace.Completion.coe' (SeparationQuotient.mk x)

instance {S : Type*} [PseudoMetricSpace S] [Nonempty S] :
    Nonempty (PseudometricCompletion S) :=
  ⟨completionEmbedding (Classical.arbitrary S)⟩

/-- The canonical embedding preserves the pseudometric exactly. -/
@[simp] theorem completionEmbedding_dist
    {S : Type*} [PseudoMetricSpace S] (x y : S) :
    dist (completionEmbedding x) (completionEmbedding y) = dist x y := by
  exact (UniformSpace.Completion.dist_eq _ _).trans
    (SeparationQuotient.dist_mk x y)

theorem completionEmbedding_isometry
    {S : Type*} [PseudoMetricSpace S] :
    Isometry (completionEmbedding : S → PseudometricCompletion S) :=
  Isometry.of_dist_eq completionEmbedding_dist

/-- The image of the original space is dense in its completed quotient. -/
theorem completionEmbedding_denseRange
    {S : Type*} [PseudoMetricSpace S] :
    DenseRange (completionEmbedding : S → PseudometricCompletion S) := by
  have hcoe : DenseRange
      ((↑) : SeparationQuotient S →
        UniformSpace.Completion (SeparationQuotient S)) :=
    UniformSpace.Completion.denseRange_coe
  have hmk : Function.Surjective
      (SeparationQuotient.mk : S → SeparationQuotient S) :=
    Quotient.mk_surjective
  change DenseRange
    (UniformSpace.Completion.coe' ∘
      (SeparationQuotient.mk : S → SeparationQuotient S))
  exact hcoe.comp hmk.denseRange
    (UniformSpace.Completion.continuous_coe (SeparationQuotient S))

variable {S : Type*} [PseudoMetricSpace S] [MeasurableSpace S] [Nonempty S]
  [OpensMeasurableSpace S] [TopologicalSpace.SeparableSpace S]

/-- The canonical embedding is measurable from any measurable structure that
contains the pseudometric Borel sets. -/
theorem measurable_completionEmbedding :
    Measurable (completionEmbedding : S → PseudometricCompletion S) :=
  (completionEmbedding_isometry (S := S)).continuous.measurable

/-- Push a probability law to the completed metric quotient. -/
def completedLaw (mu : ProbabilityMeasure S) :
    ProbabilityMeasure (PseudometricCompletion S) :=
  mu.map measurable_completionEmbedding.aemeasurable

/-- Root risk is preserved at embedded centres. -/
theorem frechetRootRisk_completedLaw
    (mu : ProbabilityMeasure S) (s : S) :
    frechetRootRisk (completedLaw mu).toMeasure (completionEmbedding s) =
      frechetRootRisk mu.toMeasure s := by
  simp only [completedLaw, ProbabilityMeasure.toMeasure_map, frechetRootRisk]
  rw [eLpNorm_map_measure]
  · apply eLpNorm_congr_ae
    filter_upwards with x
    simp
  · exact (measurable_dist_to (completionEmbedding s)).aestronglyMeasurable
  · exact measurable_completionEmbedding.aemeasurable

/-- Squared risk is preserved at embedded centres. -/
theorem frechetRisk_completedLaw
    (mu : ProbabilityMeasure S) (s : S) :
    frechetRisk (completedLaw mu).toMeasure (completionEmbedding s) =
      frechetRisk mu.toMeasure s := by
  simp [frechetRisk, frechetRootRisk_completedLaw]

/-- Finite second moment is invariant under passage to the completed metric
quotient. -/
theorem finiteSecondMoment_completedLaw_iff (mu : ProbabilityMeasure S) :
    HasFiniteSecondMoment (completedLaw mu).toMeasure ↔
      HasFiniteSecondMoment mu.toMeasure := by
  constructor
  · intro hhat
    let s : S := Classical.arbitrary S
    have hEvery :=
      (frechetRootRisk_finite_everywhere_iff (completedLaw mu).toMeasure).1 hhat
        (completionEmbedding s)
    exact ⟨s, (frechetRisk_lt_top_iff_rootRisk_lt_top mu.toMeasure s).2 <| by
      simpa [frechetRootRisk_completedLaw] using hEvery⟩
  · rintro ⟨s, hs⟩
    exact ⟨completionEmbedding s, by simpa [frechetRisk_completedLaw] using hs⟩

/-- Result 16(i): Fréchet variance is preserved by quotient and completion. -/
theorem frechetVariance_completedLaw (mu : ProbabilityMeasure S) :
    frechetVariance (completedLaw mu).toMeasure =
      frechetVariance mu.toMeasure := by
  by_cases hmu : HasFiniteSecondMoment mu.toMeasure
  · have hhat : HasFiniteSecondMoment (completedLaw mu).toMeasure :=
      (finiteSecondMoment_completedLaw_iff mu).2 hmu
    have hDenseInf := completionEmbedding_denseRange.ciInf
      (continuous_frechetRisk (completedLaw mu).toMeasure hhat)
      (show BddBelow
          (Set.range (frechetRisk (completedLaw mu).toMeasure)) from
        ⟨0, by rintro z ⟨t, rfl⟩; exact bot_le⟩)
    rw [frechetVariance, ← hDenseInf, frechetVariance]
    apply le_antisymm
    · refine le_iInf fun s : S => ?_
      exact iInf_le_of_le
        ⟨completionEmbedding s, ⟨s, rfl⟩⟩
        (frechetRisk_completedLaw mu s).le
    · refine le_iInf fun t => ?_
      rcases t with ⟨t, ⟨s, rfl⟩⟩
      exact (iInf_le (fun x : S => frechetRisk mu.toMeasure x) s).trans_eq
        (frechetRisk_completedLaw mu s).symm
  · have hhat : ¬ HasFiniteSecondMoment (completedLaw mu).toMeasure := by
      simpa [finiteSecondMoment_completedLaw_iff] using hmu
    have hTop := (frechetRootRisk_eq_top_everywhere_iff mu.toMeasure).1 hmu
    have hhatTop :=
      (frechetRootRisk_eq_top_everywhere_iff (completedLaw mu).toMeasure).1 hhat
    have hRiskTop : frechetRisk mu.toMeasure = fun _ : S => ∞ := by
      funext s
      simp [frechetRisk, hTop s]
    have hhatRiskTop :
        frechetRisk (completedLaw mu).toMeasure =
          fun _ : PseudometricCompletion S => ∞ := by
      funext t
      simp [frechetRisk, hhatTop t]
    rw [frechetVariance, frechetVariance, hRiskTop, hhatRiskTop]
    simp

/-- Pushing a coupling through the canonical embedding preserves its cost. -/
theorem transportL2Cost_completion_map
    {mu nu : ProbabilityMeasure S} (pi : TransportCoupling mu nu) :
    transportL2Cost
        (pi.map completionEmbedding completionEmbedding
          measurable_completionEmbedding measurable_completionEmbedding) =
      transportL2Cost pi := by
  simp only [transportL2Cost, TransportCoupling.map,
    ProbabilityMeasure.toMeasure_map]
  rw [eLpNorm_map_measure]
  · apply eLpNorm_congr_ae
    filter_upwards with xy
    simp
  · exact (measurable_fst.dist measurable_snd).aestronglyMeasurable
  · exact (measurable_completionEmbedding.prodMap
      measurable_completionEmbedding).aemeasurable

/-- The Polish pushforward Wasserstein distance is no larger than the direct
pseudometric Wasserstein distance.  Equality would require a coupling-lifting
theorem and is intentionally not assumed. -/
theorem wasserstein2_completedLaw_le (mu nu : ProbabilityMeasure S) :
    wasserstein2 (completedLaw mu) (completedLaw nu) ≤ wasserstein2 mu nu := by
  rw [wasserstein2]
  refine le_iInf fun pi => ?_
  exact (wasserstein2_le_transportL2Cost
    (pi.map completionEmbedding completionEmbedding
      measurable_completionEmbedding measurable_completionEmbedding)).trans_eq
        (transportL2Cost_completion_map pi)

end

end SequentialLearning
