import SequentialLearning.FrechetWassersteinLipschitz
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

/-!
# Equality-visible flags on a pseudometric target

The flag coordinate is part of the measurable value and therefore remains
visible to literal equality and to structural constraints.  The pseudometric
ignores it.  Consequently Frechet risk and transport cost depend only on the
original coordinate, while the nine-class taxonomy can distinguish the two
flags.
-/

namespace SequentialLearning

open MeasureTheory Set
open scoped ENNReal MeasureTheory

noncomputable section

/-- A value together with a measurable, equality-visible Boolean flag. -/
structure FlagSpace (S : Type*) where
  value : S
  flag : Bool
  deriving DecidableEq

namespace FlagSpace

variable {S : Type*}

instance [Nonempty S] : Nonempty (FlagSpace S) :=
  ⟨⟨Classical.choice inferInstance, false⟩⟩

/-- The pseudometric deliberately forgets the flag. -/
instance [PseudoMetricSpace S] : PseudoMetricSpace (FlagSpace S) :=
  PseudoMetricSpace.induced value inferInstance

@[simp] theorem dist_eq [PseudoMetricSpace S] (x y : FlagSpace S) :
    dist x y = dist x.value y.value := rfl

@[simp] theorem edist_eq [PseudoMetricSpace S] (x y : FlagSpace S) :
    edist x y = edist x.value y.value := rfl

/-- The measurable structure sees both the original coordinate and the flag.
It may therefore be strictly finer than the Borel structure of the
pseudometric topology. -/
instance [MeasurableSpace S] : MeasurableSpace (FlagSpace S) :=
  MeasurableSpace.comap value inferInstance ⊔
    MeasurableSpace.comap flag (⊤ : MeasurableSpace Bool)

theorem measurable_value [MeasurableSpace S] :
    Measurable (value : FlagSpace S → S) :=
  Measurable.of_comap_le le_sup_left

theorem measurable_flag [MeasurableSpace S] :
    Measurable (flag : FlagSpace S → Bool) :=
  Measurable.of_comap_le le_sup_right

/-- Each flag fibre is a measurable event, so the flag is visible to exact
equality even though it contributes zero pseudometric distance. -/
theorem measurableSet_flag_eq [MeasurableSpace S] (b : Bool) :
    MeasurableSet {x : FlagSpace S | x.flag = b} := by
  change MeasurableSet (flag ⁻¹' ({b} : Set Bool))
  exact measurable_flag (measurableSet_singleton b)

@[simp] theorem dist_mk_same_value [PseudoMetricSpace S]
    (s : S) (b b' : Bool) :
    dist (FlagSpace.mk s b) (FlagSpace.mk s b') = 0 := by
  simp

theorem mk_ne_of_flag_ne {s : S} {b b' : Bool} (h : b ≠ b') :
    FlagSpace.mk s b ≠ FlagSpace.mk s b' := by
  intro heq
  exact h (congrArg flag heq)

instance [mS : MeasurableSpace S]
    [hS : @MeasurableSpace.CountablyGenerated S mS] :
    MeasurableSpace.CountablyGenerated (FlagSpace S) := by
  let hValue : @MeasurableSpace.CountablyGenerated (FlagSpace S)
      (MeasurableSpace.comap value mS) :=
    MeasurableSpace.CountablyGenerated.comap value
  let hFlag : @MeasurableSpace.CountablyGenerated (FlagSpace S)
      (MeasurableSpace.comap flag (⊤ : MeasurableSpace Bool)) :=
    MeasurableSpace.CountablyGenerated.comap flag
  exact MeasurableSpace.CountablyGenerated.sup hValue hFlag

/-- A dense sequence for `S`, lifted with one fixed flag, remains dense because
the other flag is at distance zero. -/
instance [PseudoMetricSpace S] [TopologicalSpace.SeparableSpace S] [Nonempty S] :
    TopologicalSpace.SeparableSpace (FlagSpace S) := by
  apply TopologicalSpace.SeparableSpace.of_denseRange
    (fun n : ℕ => FlagSpace.mk (TopologicalSpace.denseSeq S n) false)
  rw [Metric.denseRange_iff]
  intro x r hr
  rcases (Metric.denseRange_iff.mp
      (TopologicalSpace.denseRange_denseSeq S)) x.value r hr with ⟨n, hn⟩
  exact ⟨n, hn⟩

/-- Open sets for the flag pseudometric depend only on `value`; the stated
measurable structure contains their pullbacks. -/
instance [PseudoMetricSpace S] [MeasurableSpace S] [OpensMeasurableSpace S] :
    OpensMeasurableSpace (FlagSpace S) where
  borel_le := by
    rw [show borel (FlagSpace S) = (borel S).comap value by
      exact borel_comap]
    exact (MeasurableSpace.comap_mono OpensMeasurableSpace.borel_le).trans
      le_sup_left

/-- Project a flagged probability law to its pseudometric coordinate. -/
def projectLaw [MeasurableSpace S]
    (mu : ProbabilityMeasure (FlagSpace S)) : ProbabilityMeasure S :=
  mu.map measurable_value.aemeasurable

/-- Root Frechet risk is exactly the risk of the projected law. -/
theorem frechetRootRisk_eq_project
    [PseudoMetricSpace S] [MeasurableSpace S] [Nonempty S]
    [OpensMeasurableSpace S]
    (nu : Measure (FlagSpace S)) (x : FlagSpace S) :
    frechetRootRisk nu x =
      frechetRootRisk (Measure.map value nu) x.value := by
  rw [frechetRootRisk, frechetRootRisk, eLpNorm_map_measure]
  · rfl
  · exact (measurable_dist_to x.value).aestronglyMeasurable
  · exact measurable_value.aemeasurable

/-- Squared Frechet risk is exactly the risk of the projected law. -/
theorem frechetRisk_eq_project
    [PseudoMetricSpace S] [MeasurableSpace S] [Nonempty S]
    [OpensMeasurableSpace S]
    (nu : Measure (FlagSpace S)) (x : FlagSpace S) :
    frechetRisk nu x = frechetRisk (Measure.map value nu) x.value := by
  rw [frechetRisk, frechetRisk, frechetRootRisk_eq_project]

/-- Frechet variance is unchanged by the equality-visible zero-distance flag. -/
theorem frechetVariance_eq_project
    [PseudoMetricSpace S] [MeasurableSpace S] [Nonempty S]
    [OpensMeasurableSpace S]
    (nu : Measure (FlagSpace S)) :
    frechetVariance nu = frechetVariance (Measure.map value nu) := by
  rw [frechetVariance, frechetVariance]
  apply le_antisymm
  · refine le_iInf fun s => ?_
    exact (iInf_le (fun x : FlagSpace S => frechetRisk nu x)
      (FlagSpace.mk s false)).trans_eq (frechetRisk_eq_project nu _)
  · refine le_iInf fun x => ?_
    exact (iInf_le (fun s : S => frechetRisk (Measure.map value nu) s)
      x.value).trans_eq (frechetRisk_eq_project nu x).symm

theorem transportL2Cost_map_value
    [PseudoMetricSpace S] [MeasurableSpace S] [Nonempty S]
    [OpensMeasurableSpace S] [TopologicalSpace.SeparableSpace S]
    {mu nu : ProbabilityMeasure (FlagSpace S)}
    (pi : TransportCoupling mu nu) :
    transportL2Cost (pi.map value value measurable_value measurable_value) =
      transportL2Cost pi := by
  simp only [transportL2Cost, TransportCoupling.map,
    ProbabilityMeasure.toMeasure_map]
  rw [eLpNorm_map_measure]
  · rfl
  · exact (measurable_fst.dist measurable_snd).aestronglyMeasurable
  · exact (measurable_value.prodMap measurable_value).aemeasurable

/-- Forgetting the flag cannot increase the two-Wasserstein cost. -/
theorem wasserstein2_project_le
    [PseudoMetricSpace S] [MeasurableSpace S] [Nonempty S]
    [OpensMeasurableSpace S] [TopologicalSpace.SeparableSpace S]
    (mu nu : ProbabilityMeasure (FlagSpace S)) :
    wasserstein2 (projectLaw mu) (projectLaw nu) ≤ wasserstein2 mu nu := by
  refine le_iInf fun pi => ?_
  exact (wasserstein2_le_transportL2Cost
    (pi.map value value measurable_value measurable_value)).trans_eq
      (transportL2Cost_map_value pi)

/-- The extra condition needed for the reverse Wasserstein inequality: every
coupling of the projected laws can be lifted without increasing cost.  This is
not automatic for arbitrary flagged laws, because their conditional flag laws
may depend on the coordinate. -/
def CouplingsLift
    [PseudoMetricSpace S] [MeasurableSpace S] [Nonempty S]
    [OpensMeasurableSpace S] [TopologicalSpace.SeparableSpace S]
    (mu nu : ProbabilityMeasure (FlagSpace S)) : Prop :=
  ∀ pi : TransportCoupling (projectLaw mu) (projectLaw nu),
    ∃ rho : TransportCoupling mu nu,
      transportL2Cost rho ≤ transportL2Cost pi

/-- Under the explicit coupling-lift condition, projecting the flag preserves
the two-Wasserstein cost exactly. -/
theorem wasserstein2_eq_project_of_couplingsLift
    [PseudoMetricSpace S] [MeasurableSpace S] [Nonempty S]
    [OpensMeasurableSpace S] [TopologicalSpace.SeparableSpace S]
    (mu nu : ProbabilityMeasure (FlagSpace S))
    (hLift : CouplingsLift mu nu) :
    wasserstein2 mu nu = wasserstein2 (projectLaw mu) (projectLaw nu) := by
  apply le_antisymm
  · refine le_iInf fun pi => ?_
    rcases hLift pi with ⟨rho, hrho⟩
    exact (wasserstein2_le_transportL2Cost rho).trans hrho
  · exact wasserstein2_project_le mu nu

end FlagSpace

end

end SequentialLearning
