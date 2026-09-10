import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

/-!
# Two-Wasserstein transport cost

This file supplies the local optimal-transport infrastructure needed by the
sequential-learning results.  The underlying space may be pseudometric, and
its measurable structure may be finer than the Borel pseudometric sigma
algebra.  Consequently the transport plans are measures on that stated
measurable space, while their cost depends only on the pseudometric.
-/

namespace SequentialLearning

open Filter MeasureTheory Set
open scoped ENNReal MeasureTheory

noncomputable section

section Couplings

variable {S T U : Type*}
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]

/-- A probability coupling of `mu` and `nu`. -/
structure TransportCoupling
    (mu : ProbabilityMeasure S) (nu : ProbabilityMeasure T) where
  /-- Joint probability law. -/
  law : ProbabilityMeasure (S × T)
  /-- The first marginal is `mu`. -/
  fst_eq : law.map measurable_fst.aemeasurable = mu
  /-- The second marginal is `nu`. -/
  snd_eq : law.map measurable_snd.aemeasurable = nu

/-- The independent product is always a coupling. -/
def TransportCoupling.independent
    (mu : ProbabilityMeasure S) (nu : ProbabilityMeasure T) :
    TransportCoupling mu nu where
  law := mu.prod nu
  fst_eq := ProbabilityMeasure.map_fst_prod mu nu
  snd_eq := ProbabilityMeasure.map_snd_prod mu nu

instance (mu : ProbabilityMeasure S) (nu : ProbabilityMeasure T) :
    Nonempty (TransportCoupling mu nu) :=
  ⟨TransportCoupling.independent mu nu⟩

/-- Swap the coordinates of a coupling. -/
def TransportCoupling.swap
    {mu : ProbabilityMeasure S} {nu : ProbabilityMeasure T}
    (pi : TransportCoupling mu nu) : TransportCoupling nu mu where
  law := pi.law.map measurable_swap.aemeasurable
  fst_eq := by
    apply ProbabilityMeasure.toMeasure_injective
    simp only [ProbabilityMeasure.toMeasure_map]
    rw [Measure.map_map measurable_fst measurable_swap]
    change Measure.map Prod.snd pi.law.toMeasure = nu.toMeasure
    simpa only [ProbabilityMeasure.toMeasure_map] using
      congrArg ProbabilityMeasure.toMeasure pi.snd_eq
  snd_eq := by
    apply ProbabilityMeasure.toMeasure_injective
    simp only [ProbabilityMeasure.toMeasure_map]
    rw [Measure.map_map measurable_snd measurable_swap]
    change Measure.map Prod.fst pi.law.toMeasure = mu.toMeasure
    simpa only [ProbabilityMeasure.toMeasure_map] using
      congrArg ProbabilityMeasure.toMeasure pi.fst_eq

/-- The diagonal law is a self-coupling. -/
def TransportCoupling.diagonal (mu : ProbabilityMeasure S) :
    TransportCoupling mu mu where
  law := mu.map (measurable_id.prodMk measurable_id).aemeasurable
  fst_eq := by
    apply ProbabilityMeasure.toMeasure_injective
    simp only [ProbabilityMeasure.toMeasure_map]
    rw [Measure.map_map measurable_fst (measurable_id.prodMk measurable_id)]
    change Measure.map id mu.toMeasure = mu.toMeasure
    exact Measure.map_id
  snd_eq := by
    apply ProbabilityMeasure.toMeasure_injective
    simp only [ProbabilityMeasure.toMeasure_map]
    rw [Measure.map_map measurable_snd (measurable_id.prodMk measurable_id)]
    change Measure.map id mu.toMeasure = mu.toMeasure
    exact Measure.map_id

/-- Push both coordinates of a coupling through measurable maps. -/
def TransportCoupling.map
    {mu : ProbabilityMeasure S} {nu : ProbabilityMeasure T}
    (pi : TransportCoupling mu nu) (f : S → U) (g : T → U)
    (hf : Measurable f) (hg : Measurable g) :
    TransportCoupling (mu.map hf.aemeasurable) (nu.map hg.aemeasurable) where
  law := pi.law.map (hf.prodMap hg).aemeasurable
  fst_eq := by
    apply ProbabilityMeasure.toMeasure_injective
    simp only [ProbabilityMeasure.toMeasure_map]
    rw [Measure.map_map measurable_fst (hf.prodMap hg)]
    change Measure.map (f ∘ Prod.fst) pi.law.toMeasure = Measure.map f mu.toMeasure
    rw [← Measure.map_map hf measurable_fst]
    exact congrArg (Measure.map f) <| by
      simpa only [ProbabilityMeasure.toMeasure_map] using
        congrArg ProbabilityMeasure.toMeasure pi.fst_eq
  snd_eq := by
    apply ProbabilityMeasure.toMeasure_injective
    simp only [ProbabilityMeasure.toMeasure_map]
    rw [Measure.map_map measurable_snd (hf.prodMap hg)]
    change Measure.map (g ∘ Prod.snd) pi.law.toMeasure = Measure.map g nu.toMeasure
    rw [← Measure.map_map hg measurable_snd]
    exact congrArg (Measure.map g) <| by
      simpa only [ProbabilityMeasure.toMeasure_map] using
        congrArg ProbabilityMeasure.toMeasure pi.snd_eq

end Couplings

section Wasserstein

variable {S : Type*} [PseudoMetricSpace S] [MeasurableSpace S]
  [OpensMeasurableSpace S] [TopologicalSpace.SeparableSpace S]

/-- Root-mean-square transport cost of a coupling. -/
def transportL2Cost
    {mu nu : ProbabilityMeasure S} (pi : TransportCoupling mu nu) : ENNReal :=
  eLpNorm (fun xy : S × S => dist xy.1 xy.2) 2 pi.law.toMeasure

/-- Squaring the root-mean-square transport cost recovers the integral of
the squared pseudometric cost. -/
theorem transportL2Cost_sq_eq_lintegral
    {mu nu : ProbabilityMeasure S} (pi : TransportCoupling mu nu) :
    transportL2Cost pi ^ 2 =
      ∫⁻ xy : S × S, ENNReal.ofReal (dist xy.1 xy.2 ^ 2) ∂pi.law.toMeasure := by
  rw [transportL2Cost]
  calc
    eLpNorm (fun xy : S × S => dist xy.1 xy.2) 2 pi.law.toMeasure ^ 2 =
        eLpNorm (fun xy : S × S => dist xy.1 xy.2) 2 pi.law.toMeasure ^
          (2 : ℝ) :=
      (ENNReal.rpow_two _).symm
    _ = ∫⁻ xy : S × S, ‖dist xy.1 xy.2‖ₑ ^ (2 : ℝ) ∂pi.law.toMeasure :=
      eLpNorm_nnreal_pow_eq_lintegral (p := (2 : NNReal)) (by norm_num)
    _ = ∫⁻ xy : S × S,
        ENNReal.ofReal (dist xy.1 xy.2 ^ 2) ∂pi.law.toMeasure := by
      apply lintegral_congr
      intro xy
      simp only [Real.enorm_eq_ofReal_abs]
      rw [abs_of_nonneg (dist_nonneg : 0 ≤ dist xy.1 xy.2)]
      norm_num [ENNReal.rpow_two]

/-- The two-Wasserstein transport cost on a measurable pseudometric space. -/
def wasserstein2 (mu nu : ProbabilityMeasure S) : ENNReal :=
  ⨅ pi : TransportCoupling mu nu, transportL2Cost pi

/-- Wasserstein cost is nonnegative. -/
theorem wasserstein2_nonnegative (mu nu : ProbabilityMeasure S) :
    0 ≤ wasserstein2 mu nu :=
  bot_le

/-- Every coupling gives an upper bound on the Wasserstein cost. -/
theorem wasserstein2_le_transportL2Cost
    {mu nu : ProbabilityMeasure S} (pi : TransportCoupling mu nu) :
    wasserstein2 mu nu ≤ transportL2Cost pi :=
  iInf_le _ pi

/-- The diagonal coupling has zero transport cost.  This uses only the
pseudometric identity `dist x x = 0`; no quotient is involved. -/
theorem transportL2Cost_diagonal (mu : ProbabilityMeasure S) :
    transportL2Cost (TransportCoupling.diagonal mu) = 0 := by
  simp only [transportL2Cost, TransportCoupling.diagonal,
    ProbabilityMeasure.toMeasure_map]
  rw [eLpNorm_map_measure]
  · simp [Function.comp_def]
  · exact (measurable_fst.dist measurable_snd).aestronglyMeasurable
  · exact (measurable_id.prodMk measurable_id).aemeasurable

/-- The direct pseudometric Wasserstein cost vanishes on the diagonal. -/
@[simp] theorem wasserstein2_self (mu : ProbabilityMeasure S) :
    wasserstein2 mu mu = 0 := by
  apply le_antisymm
  · simpa [transportL2Cost_diagonal] using
      wasserstein2_le_transportL2Cost (TransportCoupling.diagonal mu)
  · exact bot_le

/-- Swapping a coupling does not alter its transport cost. -/
theorem transportL2Cost_swap
    {mu nu : ProbabilityMeasure S} (pi : TransportCoupling mu nu) :
    transportL2Cost pi.swap = transportL2Cost pi := by
  simp only [transportL2Cost, TransportCoupling.swap,
    ProbabilityMeasure.toMeasure_map]
  change eLpNorm (fun xy : S × S => dist xy.1 xy.2) 2
      (Measure.map Prod.swap pi.law.toMeasure) = _
  rw [eLpNorm_map_measure]
  · apply eLpNorm_congr_ae
    filter_upwards with xy
    simp only [Function.comp_apply]
    exact dist_comm _ _
  · exact (measurable_fst.dist measurable_snd).aestronglyMeasurable
  · exact measurable_swap.aemeasurable

/-- The two-Wasserstein cost is symmetric. -/
theorem wasserstein2_comm (mu nu : ProbabilityMeasure S) :
    wasserstein2 mu nu = wasserstein2 nu mu := by
  apply le_antisymm
  · refine le_iInf fun pi => ?_
    exact (wasserstein2_le_transportL2Cost pi.swap).trans_eq
      (transportL2Cost_swap pi)
  · refine le_iInf fun pi => ?_
    exact (wasserstein2_le_transportL2Cost pi.swap).trans_eq
      (transportL2Cost_swap pi)

end Wasserstein

end

end SequentialLearning
