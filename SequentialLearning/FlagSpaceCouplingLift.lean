import SequentialLearning.FlagSpace
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Lifting couplings through a finite equality-visible flag

An arbitrary coupling of the projected value laws can be decorated with the
conditional Boolean flag laws of its two marginals.  The resulting flagged
coupling projects back to the original coupling exactly.  Since the
pseudometric ignores the flags, its transport cost is unchanged.
-/

namespace SequentialLearning

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal MeasureTheory ProbabilityTheory

noncomputable section

namespace FlagSpace

variable {S : Type*}

/-- The flagged measurable space is measurably equivalent to the ordinary
product of the value space and `Bool`. -/
def measurableEquivProd [MeasurableSpace S] : FlagSpace S ≃ᵐ S × Bool where
  toFun x := (x.value, x.flag)
  invFun p := FlagSpace.mk p.1 p.2
  left_inv x := by cases x; rfl
  right_inv p := by cases p; rfl
  measurable_toFun := measurable_value.prodMk measurable_flag
  measurable_invFun := by
    apply Measurable.of_comap_le
    change MeasurableSpace.comap
        (fun p : S × Bool => FlagSpace.mk p.1 p.2)
        (MeasurableSpace.comap value inferInstance ⊔
          MeasurableSpace.comap flag (⊤ : MeasurableSpace Bool)) ≤ _
    rw [MeasurableSpace.comap_sup]
    rw [MeasurableSpace.comap_comp, MeasurableSpace.comap_comp]
    change MeasurableSpace.comap (fun p : S × Bool => p.1) inferInstance ⊔
        MeasurableSpace.comap (fun p : S × Bool => p.2)
          (⊤ : MeasurableSpace Bool) ≤ _
    exact sup_le measurable_fst.comap_le measurable_snd.comap_le

/-- A flagged law represented on the literal product `S × Bool`. -/
def productLaw [MeasurableSpace S]
    (mu : ProbabilityMeasure (FlagSpace S)) : Measure (S × Bool) :=
  Measure.map measurableEquivProd mu.toMeasure

instance productLaw.instIsProbabilityMeasure [MeasurableSpace S]
    (mu : ProbabilityMeasure (FlagSpace S)) :
    IsProbabilityMeasure (productLaw mu) := by
  rw [productLaw]
  exact Measure.isProbabilityMeasure_map
    measurableEquivProd.measurable.aemeasurable

/-- The first marginal of the product representation is the projected law. -/
theorem productLaw_fst [MeasurableSpace S]
    (mu : ProbabilityMeasure (FlagSpace S)) :
    (productLaw mu).fst = (projectLaw mu).toMeasure := by
  rw [productLaw, Measure.fst, Measure.map_map]
  rfl
  · exact measurable_fst
  · exact measurableEquivProd.measurable

/-- Conditional law of the Boolean flag given the value coordinate.  Only
the conditioned coordinate (`Bool`) needs to be standard Borel. -/
def conditionalFlagKernel [MeasurableSpace S]
    (mu : ProbabilityMeasure (FlagSpace S)) : Kernel S Bool :=
  (productLaw mu).condKernel

instance conditionalFlagKernel.instIsMarkovKernel [MeasurableSpace S]
    (mu : ProbabilityMeasure (FlagSpace S)) :
    IsMarkovKernel (conditionalFlagKernel mu) := by
  rw [conditionalFlagKernel]
  infer_instance

instance conditionalFlagKernel.instIsCondKernel [MeasurableSpace S]
    (mu : ProbabilityMeasure (FlagSpace S)) :
    (productLaw mu).IsCondKernel (conditionalFlagKernel mu) := by
  rw [conditionalFlagKernel]
  infer_instance

/-- Attach to each value its conditional flag law under `mu`. -/
def attachFlagKernel [MeasurableSpace S]
    (mu : ProbabilityMeasure (FlagSpace S)) : Kernel S (FlagSpace S) :=
  (Kernel.id ×ₖ conditionalFlagKernel mu).map measurableEquivProd.symm

instance attachFlagKernel.instIsMarkovKernel [MeasurableSpace S]
    (mu : ProbabilityMeasure (FlagSpace S)) :
    IsMarkovKernel (attachFlagKernel mu) := by
  rw [attachFlagKernel]
  exact Kernel.IsMarkovKernel.map _ measurableEquivProd.symm.measurable

/-- Attaching flags and then forgetting them is the identity kernel. -/
theorem attachFlagKernel_map_value [MeasurableSpace S]
    (mu : ProbabilityMeasure (FlagSpace S)) :
    (attachFlagKernel mu).map value = Kernel.id := by
  rw [attachFlagKernel, ← Kernel.map_comp_right]
  · have hcomp : value ∘ measurableEquivProd.symm =
        (Prod.fst : S × Bool → S) := by
      funext p
      cases p
      rfl
    rw [hcomp]
    exact (Kernel.fst_eq _).symm.trans
      (Kernel.fst_prod Kernel.id (conditionalFlagKernel mu))
  · exact measurableEquivProd.symm.measurable
  · exact measurable_value

/-- Integrating the conditional flag kernel against the projected value law
recovers the original flagged law. -/
theorem attachFlagKernel_comp_project [MeasurableSpace S]
    (mu : ProbabilityMeasure (FlagSpace S)) :
    attachFlagKernel mu ∘ₘ (projectLaw mu).toMeasure = mu.toMeasure := by
  rw [attachFlagKernel]
  rw [← Measure.map_comp (projectLaw mu).toMeasure
    (Kernel.id ×ₖ conditionalFlagKernel mu)
      measurableEquivProd.symm.measurable]
  rw [← Measure.compProd_eq_comp_prod]
  rw [← productLaw_fst mu]
  rw [(productLaw mu).disintegrate (conditionalFlagKernel mu)]
  rw [productLaw, Measure.map_map]
  · exact Measure.map_id
  · exact measurableEquivProd.symm.measurable
  · exact measurableEquivProd.measurable

/-- Independently attach the two conditional flag laws to a pair of value
coordinates. -/
def couplingFlagKernel [MeasurableSpace S]
    (mu nu : ProbabilityMeasure (FlagSpace S)) :
    Kernel (S × S) (FlagSpace S × FlagSpace S) :=
  (attachFlagKernel mu).comap Prod.fst measurable_fst ×ₖ
    (attachFlagKernel nu).comap Prod.snd measurable_snd

instance couplingFlagKernel.instIsMarkovKernel [MeasurableSpace S]
    (mu nu : ProbabilityMeasure (FlagSpace S)) :
    IsMarkovKernel (couplingFlagKernel mu nu) := by
  rw [couplingFlagKernel]
  infer_instance

/-- Projecting both decorated coordinates returns the input pair. -/
theorem couplingFlagKernel_map_values [MeasurableSpace S]
    (mu nu : ProbabilityMeasure (FlagSpace S)) :
    (couplingFlagKernel mu nu).map (Prod.map value value) = Kernel.id := by
  rw [couplingFlagKernel, ← Kernel.map_prod_map]
  rw [← Kernel.comap_map_comm, ← Kernel.comap_map_comm]
  rw [attachFlagKernel_map_value, attachFlagKernel_map_value]
  rw [Kernel.id_comap, Kernel.id_comap]
  rw [Kernel.deterministic_prod_deterministic]
  rfl
  all_goals exact measurable_value

/-- The first marginal kernel is the first conditional flag attachment. -/
theorem couplingFlagKernel_map_fst [MeasurableSpace S]
    (mu nu : ProbabilityMeasure (FlagSpace S)) :
    (couplingFlagKernel mu nu).map Prod.fst =
      (attachFlagKernel mu).comap Prod.fst measurable_fst := by
  rw [couplingFlagKernel]
  exact (Kernel.fst_eq _).symm.trans
    (Kernel.fst_prod _ _)

/-- The second marginal kernel is the second conditional flag attachment. -/
theorem couplingFlagKernel_map_snd [MeasurableSpace S]
    (mu nu : ProbabilityMeasure (FlagSpace S)) :
    (couplingFlagKernel mu nu).map Prod.snd =
      (attachFlagKernel nu).comap Prod.snd measurable_snd := by
  rw [couplingFlagKernel]
  exact (Kernel.snd_eq _).symm.trans
    (Kernel.snd_prod _ _)

/-- The flagged law obtained by decorating a coupling of projected laws. -/
def liftedCouplingMeasure [MeasurableSpace S]
    (mu nu : ProbabilityMeasure (FlagSpace S))
    (pi : TransportCoupling (projectLaw mu) (projectLaw nu)) :
    Measure (FlagSpace S × FlagSpace S) :=
  couplingFlagKernel mu nu ∘ₘ pi.law.toMeasure

instance liftedCouplingMeasure.instIsProbabilityMeasure [MeasurableSpace S]
    (mu nu : ProbabilityMeasure (FlagSpace S))
    (pi : TransportCoupling (projectLaw mu) (projectLaw nu)) :
    IsProbabilityMeasure (liftedCouplingMeasure mu nu pi) := by
  rw [liftedCouplingMeasure]
  infer_instance

/-- The decorated law projects exactly to the supplied value coupling. -/
theorem liftedCouplingMeasure_map_values [MeasurableSpace S]
    (mu nu : ProbabilityMeasure (FlagSpace S))
    (pi : TransportCoupling (projectLaw mu) (projectLaw nu)) :
    Measure.map (Prod.map value value) (liftedCouplingMeasure mu nu pi) =
      pi.law.toMeasure := by
  rw [liftedCouplingMeasure,
    Measure.map_comp _ _ (measurable_value.prodMap measurable_value),
    couplingFlagKernel_map_values]
  exact Measure.id_comp

/-- The first marginal of the decorated law is the original first flagged
law. -/
theorem liftedCouplingMeasure_fst [MeasurableSpace S]
    (mu nu : ProbabilityMeasure (FlagSpace S))
    (pi : TransportCoupling (projectLaw mu) (projectLaw nu)) :
    (liftedCouplingMeasure mu nu pi).fst = mu.toMeasure := by
  rw [Measure.fst, liftedCouplingMeasure,
    Measure.map_comp _ _ measurable_fst, couplingFlagKernel_map_fst]
  rw [← Kernel.comp_deterministic_eq_comap]
  rw [← Measure.comp_assoc]
  rw [Measure.deterministic_comp_eq_map]
  have hfst : Measure.map Prod.fst pi.law.toMeasure =
      (projectLaw mu).toMeasure := by
    simpa only [ProbabilityMeasure.toMeasure_map] using
      congrArg ProbabilityMeasure.toMeasure pi.fst_eq
  rw [hfst, attachFlagKernel_comp_project]

/-- The second marginal of the decorated law is the original second flagged
law. -/
theorem liftedCouplingMeasure_snd [MeasurableSpace S]
    (mu nu : ProbabilityMeasure (FlagSpace S))
    (pi : TransportCoupling (projectLaw mu) (projectLaw nu)) :
    (liftedCouplingMeasure mu nu pi).snd = nu.toMeasure := by
  rw [Measure.snd, liftedCouplingMeasure,
    Measure.map_comp _ _ measurable_snd, couplingFlagKernel_map_snd]
  rw [← Kernel.comp_deterministic_eq_comap]
  rw [← Measure.comp_assoc]
  rw [Measure.deterministic_comp_eq_map]
  have hsnd : Measure.map Prod.snd pi.law.toMeasure =
      (projectLaw nu).toMeasure := by
    simpa only [ProbabilityMeasure.toMeasure_map] using
      congrArg ProbabilityMeasure.toMeasure pi.snd_eq
  rw [hsnd, attachFlagKernel_comp_project]

/-- Constructive lift of any projected coupling to the two flagged laws. -/
def liftCoupling [MeasurableSpace S]
    (mu nu : ProbabilityMeasure (FlagSpace S))
    (pi : TransportCoupling (projectLaw mu) (projectLaw nu)) :
    TransportCoupling mu nu where
  law := ⟨liftedCouplingMeasure mu nu pi, inferInstance⟩
  fst_eq := ProbabilityMeasure.toMeasure_injective
    (liftedCouplingMeasure_fst mu nu pi)
  snd_eq := ProbabilityMeasure.toMeasure_injective
    (liftedCouplingMeasure_snd mu nu pi)

/-- Couplings with the same joint law are equal; the marginal certificates
are propositions. -/
theorem transportCoupling_ext [MeasurableSpace S]
    {mu nu : ProbabilityMeasure S} {pi rho : TransportCoupling mu nu}
    (h : pi.law = rho.law) : pi = rho := by
  cases pi
  cases rho
  cases h
  rfl

/-- Mapping the constructive lift back to value coordinates recovers the
supplied coupling, not merely a coupling of the same marginals. -/
theorem liftCoupling_map_values [MeasurableSpace S]
    (mu nu : ProbabilityMeasure (FlagSpace S))
    (pi : TransportCoupling (projectLaw mu) (projectLaw nu)) :
    (liftCoupling mu nu pi).map value value measurable_value measurable_value =
      pi := by
  apply transportCoupling_ext
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (Prod.map value value)
      (liftedCouplingMeasure mu nu pi) = pi.law.toMeasure
  exact liftedCouplingMeasure_map_values mu nu pi

/-- The constructive coupling lift preserves transport cost exactly. -/
theorem transportL2Cost_liftCoupling
    [PseudoMetricSpace S] [MeasurableSpace S] [Nonempty S]
    [OpensMeasurableSpace S] [TopologicalSpace.SeparableSpace S]
    (mu nu : ProbabilityMeasure (FlagSpace S))
    (pi : TransportCoupling (projectLaw mu) (projectLaw nu)) :
    transportL2Cost (liftCoupling mu nu pi) = transportL2Cost pi := by
  have hcost := transportL2Cost_map_value (liftCoupling mu nu pi)
  rw [liftCoupling_map_values] at hcost
  exact hcost.symm

/-- Every coupling of the projected laws lifts with the same cost. -/
theorem couplingsLift
    [PseudoMetricSpace S] [MeasurableSpace S] [Nonempty S]
    [OpensMeasurableSpace S] [TopologicalSpace.SeparableSpace S]
    (mu nu : ProbabilityMeasure (FlagSpace S)) :
    CouplingsLift mu nu := by
  intro pi
  exact ⟨liftCoupling mu nu pi,
    (transportL2Cost_liftCoupling mu nu pi).le⟩

/-- A finite equality-visible Boolean flag preserves the two-Wasserstein
distance exactly, with no coupling-lift hypothesis exposed. -/
theorem wasserstein2_eq_project
    [PseudoMetricSpace S] [MeasurableSpace S] [Nonempty S]
    [OpensMeasurableSpace S] [TopologicalSpace.SeparableSpace S]
    (mu nu : ProbabilityMeasure (FlagSpace S)) :
    wasserstein2 mu nu = wasserstein2 (projectLaw mu) (projectLaw nu) :=
  wasserstein2_eq_project_of_couplingsLift mu nu (couplingsLift mu nu)

end FlagSpace

end

end SequentialLearning
