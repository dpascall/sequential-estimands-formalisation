import SequentialLearning.PosteriorDisplacementInfrastructure
import SequentialLearning.PolishProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Measurability of the quadratic Wasserstein distance on Polish probability laws

The custom `wasserstein2` used by the manuscript is lower semicontinuous for weak convergence.
Together with the Polish probability-law measurable-structure theorem, this closes the temporary
`Wasserstein2LawMeasurable` interface without an external hypothesis.
-/

namespace SequentialLearning

open Filter MeasureTheory Set Topology
open scoped ENNReal MeasureTheory Topology

noncomputable section

variable {T : Type*} [MetricSpace T] [MeasurableSpace T]
  [BorelSpace T] [CompleteSpace T] [SecondCountableTopology T]

private lemma coupling_laws_isTight
    {p : ℕ → ProbabilityMeasure T × ProbabilityMeasure T}
    {q : ProbabilityMeasure T × ProbabilityMeasure T}
    (hp : Tendsto p atTop (𝓝 q))
    (pi : ℕ → ProbabilityMeasure (T × T))
    (hfst : ∀ n, (pi n).map measurable_fst.aemeasurable = (p n).1)
    (hsnd : ∀ n, (pi n).map measurable_snd.aemeasurable = (p n).2) :
    IsTightMeasureSet {((theta : ProbabilityMeasure (T × T)) : Measure (T × T)) |
      theta ∈ Set.range pi} := by
  have hp1 : Tendsto (fun n => (p n).1) atTop (𝓝 q.1) :=
    (continuous_fst.tendsto q).comp hp
  have hp2 : Tendsto (fun n => (p n).2) atTop (𝓝 q.2) :=
    (continuous_snd.tendsto q).comp hp
  have hK1 : IsCompact (insert q.1 (Set.range fun n => (p n).1)) :=
    hp1.isCompact_insert_range
  have hK2 : IsCompact (insert q.2 (Set.range fun n => (p n).2)) :=
    hp2.isCompact_insert_range
  have ht1 := isTightMeasureSet_of_isCompact_closure
    (S := insert q.1 (Set.range fun n => (p n).1)) (by simpa [hK1.isClosed.closure_eq] using hK1)
  have ht2 := isTightMeasureSet_of_isCompact_closure
    (S := insert q.2 (Set.range fun n => (p n).2)) (by simpa [hK2.isClosed.closure_eq] using hK2)
  apply IsTightMeasureSet.prodMk
  · apply ht1.subset
    rintro _ ⟨theta, ⟨n, hn, rfl⟩, rfl⟩
    rcases hn with ⟨k, rfl⟩
    refine ⟨(p k).1, Or.inr ⟨k, rfl⟩, ?_⟩
    simpa [Measure.fst, ProbabilityMeasure.toMeasure_map] using
      (congrArg ProbabilityMeasure.toMeasure (hfst k)).symm
  · apply ht2.subset
    rintro _ ⟨theta, ⟨n, hn, rfl⟩, rfl⟩
    rcases hn with ⟨k, rfl⟩
    refine ⟨(p k).2, Or.inr ⟨k, rfl⟩, ?_⟩
    simpa [Measure.snd, ProbabilityMeasure.toMeasure_map] using
      (congrArg ProbabilityMeasure.toMeasure (hsnd k)).symm

theorem wasserstein2_lowerSemicontinuous :
    LowerSemicontinuous fun p : ProbabilityMeasure T × ProbabilityMeasure T =>
      wasserstein2 p.1 p.2 := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro c
  rw [← isSeqClosed_iff_isClosed]
  intro p q hp hq
  simp only [mem_preimage, mem_Iic] at hp ⊢
  by_cases hc : c = ∞
  · simp [hc]
  have hWlt (n : ℕ) :
      wasserstein2 (p n).1 (p n).2 < c + ((n + 1 : ℕ) : ENNReal)⁻¹ := by
    exact (hp n).trans_lt <| ENNReal.lt_add_right hc (by simp)
  have hex (n : ℕ) : ∃ pi : TransportCoupling (p n).1 (p n).2,
      transportL2Cost pi < c + ((n + 1 : ℕ) : ENNReal)⁻¹ := by
    have hn := hWlt n
    rw [wasserstein2] at hn
    exact (ciInf_lt_iff ⟨0, by rintro _ ⟨thetaCoupling, rfl⟩; exact bot_le⟩).1 hn
  choose pi hpi using hex
  have hTight := coupling_laws_isTight hq (fun n => (pi n).law)
    (fun n => (pi n).fst_eq) (fun n => (pi n).snd_eq)
  have hCompact : IsCompact (closure (Set.range fun n => (pi n).law)) :=
    isCompact_closure_of_isTightMeasureSet hTight
  obtain ⟨theta, _, sub, hsub, htheta⟩ :=
    hCompact.isSeqCompact (fun n => subset_closure ⟨n, rfl⟩)
  have hp1 : Tendsto (fun n => (p n).1) atTop (𝓝 q.1) :=
    (continuous_fst.tendsto q).comp hq
  have hp2 : Tendsto (fun n => (p n).2) atTop (𝓝 q.2) :=
    (continuous_snd.tendsto q).comp hq
  have hthetaFst := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun n => (pi (sub n)).law) theta htheta continuous_fst
  have hthetaSnd := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun n => (pi (sub n)).law) theta htheta continuous_snd
  have hfst : theta.map measurable_fst.aemeasurable = q.1 := by
    apply tendsto_nhds_unique hthetaFst
    simpa only [(pi _).fst_eq, Function.comp_def] using hp1.comp hsub.tendsto_atTop
  have hsnd : theta.map measurable_snd.aemeasurable = q.2 := by
    apply tendsto_nhds_unique hthetaSnd
    simpa only [(pi _).snd_eq, Function.comp_def] using hp2.comp hsub.tendsto_atTop
  let piLimit : TransportCoupling q.1 q.2 := ⟨theta, hfst, hsnd⟩
  have hPort :=
    lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
      (μ := theta.toMeasure)
      (μs := fun n => (pi (sub n)).law.toMeasure)
      (f := fun xy : T × T => dist xy.1 xy.2 ^ 2)
      ((continuous_fst.dist continuous_snd).pow 2)
      (fun _ => sq_nonneg _)
      (fun G hG => ProbabilityMeasure.le_liminf_measure_open_of_tendsto htheta hG)
  have hPort' : transportL2Cost piLimit ^ 2 ≤
      atTop.liminf (fun n => transportL2Cost (pi (sub n)) ^ 2) := by
    simpa only [transportL2Cost_sq_eq_lintegral] using hPort
  have heps : Tendsto (fun n => ((sub n + 1 : ℕ) : ENNReal)⁻¹) atTop (𝓝 0) :=
    ENNReal.tendsto_inv_nat_nhds_zero.comp
      ((tendsto_add_atTop_nat 1).comp hsub.tendsto_atTop)
  have hbound : atTop.liminf (fun n => transportL2Cost (pi (sub n)) ^ 2) ≤ c ^ 2 := by
    calc
      atTop.liminf (fun n => transportL2Cost (pi (sub n)) ^ 2) ≤
          atTop.liminf (fun n => (c + ((sub n + 1 : ℕ) : ENNReal)⁻¹) ^ 2) :=
        Filter.liminf_le_liminf <| Eventually.of_forall fun n =>
          ENNReal.pow_le_pow_left (hpi (sub n)).le
      _ = c ^ 2 := by
        apply Tendsto.liminf_eq
        have hcconst : Tendsto (fun _ : ℕ => c) atTop (𝓝 c) := tendsto_const_nhds
        have hsum : Tendsto
            (fun n => c + ((sub n + 1 : ℕ) : ENNReal)⁻¹) atTop (𝓝 (c + 0)) :=
          hcconst.add heps
        simpa [Function.comp_def] using
          ((ENNReal.continuous_pow 2).tendsto (c + 0)).comp hsum
  have hCost : transportL2Cost piLimit ≤ c :=
    ENNReal.pow_le_pow_left_iff two_ne_zero |>.mp <| hPort'.trans hbound
  exact (wasserstein2_le_transportL2Cost piLimit).trans hCost

/-- On a Polish space, the custom quadratic Wasserstein distance is Giry measurable. -/
theorem wasserstein2LawMeasurable_of_polish : Wasserstein2LawMeasurable T := by
  letI : SecondCountableTopology (ProbabilityMeasure T) :=
    MeasureTheory.secondCountableTopology_probabilityMeasure
  letI : OpensMeasurableSpace (ProbabilityMeasure T) :=
    MeasureTheory.opensMeasurableSpace_probabilityMeasure
  exact wasserstein2_lowerSemicontinuous.measurable

end

end SequentialLearning
