import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Geometry.Convex.ConvexSpace.Topology

/-!
# Measurable structure of probability laws on Polish spaces

This module proves that weak convergence on probability laws over a Polish space is
second-countable and that its Borel sigma-algebra is contained in the Giry measurable structure.
The separability proof uses finite atomic laws and the Lévy--Prokhorov metric.
-/

namespace MeasureTheory

open Filter Set Topology TopologicalSpace
open scoped ENNReal NNReal MeasureTheory Topology BigOperators

noncomputable section

variable {T : Type*} [MetricSpace T] [MeasurableSpace T]
  [BorelSpace T] [SecondCountableTopology T]

private def finiteLaw {n : ℕ} (w : Convexity.StdSimplex ℝ (Fin n)) (x : Fin n → T) :
    ProbabilityMeasure T :=
  ⟨Measure.sum (fun i ↦ ENNReal.ofReal (w.weights i) • Measure.dirac (x i)),
    HasSum.isProbabilityMeasure_sum_dirac w.weights_nonneg (by
      simpa only [w.total_of_fintype] using hasSum_fintype (fun i => w.weights i))⟩

@[simp] private lemma finiteLaw_toMeasure {n : ℕ}
    (w : Convexity.StdSimplex ℝ (Fin n)) (x : Fin n → T) :
    ((finiteLaw w x : ProbabilityMeasure T) : Measure T) =
      Measure.sum (fun i ↦ ENNReal.ofReal (w.weights i) • Measure.dirac (x i)) := rfl

private lemma finiteLaw_integral {n : ℕ}
    (w : Convexity.StdSimplex ℝ (Fin n)) (x : Fin n → T)
    (f : BoundedContinuousFunction T ℝ) :
    ∫ t, f t ∂(finiteLaw w x : ProbabilityMeasure T) =
      ∑ i, w.weights i * f (x i) := by
  rw [finiteLaw_toMeasure, integral_sum_dirac]
  · simp [ENNReal.toReal_ofReal (w.weights_nonneg _)]
  · simp

private lemma continuous_finiteLaw {n : ℕ} :
    Continuous (fun p : Convexity.StdSimplex ℝ (Fin n) × (Fin n → T) ↦
      finiteLaw p.1 p.2) := by
  rw [ProbabilityMeasure.continuous_iff_forall_continuous_integral]
  intro f
  simp_rw [finiteLaw_integral]
  fun_prop

private lemma exists_finiteLaw_levyProkhorovDist_lt (mu : ProbabilityMeasure T)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ (n : ℕ) (w : Convexity.StdSimplex ℝ (Fin n)) (x : Fin n → T),
      levyProkhorovDist (finiteLaw w x : Measure T) mu.toMeasure < epsilon := by
  classical
  have hhalf : 0 < epsilon / 2 := half_pos hepsilon
  obtain ⟨E, hEmeas, hEbounded, hEdiam, hEcover, hEdisjoint⟩ :=
    SeparableSpace.exists_measurable_partition_diam_le T hhalf
  obtain ⟨N, hN⟩ : ∃ N, mu.toMeasure (⋃ j ∈ Iio N, E j)ᶜ < ENNReal.ofReal (epsilon / 2) := by
    have hexhaust := @tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint T _ mu.toMeasure _
      E (fun n ↦ (hEmeas n).nullMeasurableSet) hEdisjoint
    simp only [tendsto_atTop_nhds, Function.comp_apply] at hexhaust
    obtain ⟨N, hN⟩ := hexhaust (Iio (ENNReal.ofReal (epsilon / 2)))
      (ENNReal.ofReal_pos.mpr hhalf) isOpen_Iio
    refine ⟨N, ?_⟩
    have hre : ⋃ i, ⋃ (_ : N ≤ i), E i = (⋃ i, ⋃ (_ : i < N), E i)ᶜ := by
      simpa only [mem_Iio, compl_Iio, mem_Ici] using
        (biUnion_compl_eq_of_pairwise_disjoint_of_iUnion_eq_univ hEcover hEdisjoint
          (Iio N)).symm
    simpa only [mem_Iio, ← hre, gt_iff_lt] using hN N le_rfl
  let A : Set T := ⋃ j ∈ Iio N, E j
  have hAmeas : MeasurableSet A :=
    MeasurableSet.biUnion (finite_Iio N).countable fun i _ ↦ hEmeas i
  let x0 : T := mu.nonempty.some
  let y : ℕ → T := fun i ↦ if hi : (E i).Nonempty then hi.some else x0
  have hy (i : ℕ) (hi : (E i).Nonempty) : y i ∈ E i := by
    simp only [y, dif_pos hi]
    exact hi.some_mem
  let points : Fin (N + 1) → T := fun i ↦ if hi : i.val < N then y i.val else x0
  let coeff : Fin (N + 1) → ℝ := fun i ↦
    if hi : i.val < N then mu.toMeasure.real (E i.val) else mu.toMeasure.real Aᶜ
  have hcoeff_nonneg (i : Fin (N + 1)) : 0 ≤ coeff i := by
    simp only [coeff]
    split <;> positivity
  have hrealA : mu.toMeasure.real A = ∑ i ∈ Finset.range N, mu.toMeasure.real (E i) := by
    calc
      mu.toMeasure.real A = mu.toMeasure.real (⋃ i ∈ (Finset.range N : Set ℕ), E i) := by
        congr 1
        ext t
        simp only [A, mem_iUnion, mem_Iio, Finset.mem_range]
        constructor
        · rintro ⟨i, hi, ht⟩
          exact ⟨i, by simpa using hi, ht⟩
        · rintro ⟨i, hi, ht⟩
          exact ⟨i, by simpa using hi, ht⟩
      _ = ∑ i ∈ Finset.range N, mu.toMeasure.real (E i) :=
        measureReal_biUnion_finset
          (hEdisjoint.set_pairwise (Finset.range N)) (fun i _ ↦ hEmeas i)
          (fun i _ ↦ measure_ne_top _ _)
  have hrealA_fin : ∑ i : Fin N, mu.toMeasure.real (E i.val) = mu.toMeasure.real A := by
    rw [Finset.sum_fin_eq_sum_range]
    calc
      (∑ i ∈ Finset.range N,
          if h : i < N then mu.toMeasure.real (E i) else 0) =
          ∑ i ∈ Finset.range N, mu.toMeasure.real (E i) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp only [dif_pos (Finset.mem_range.mp hi)]
      _ = mu.toMeasure.real A := hrealA.symm
  have hcoeff_sum : ∑ i, coeff i = 1 := by
    rw [Fin.sum_univ_castSucc]
    simp only [coeff, Fin.val_castSucc, Fin.is_lt, ↓reduceDIte, Fin.val_last, lt_self_iff_false,
      not_false_eq_true]
    rw [hrealA_fin]
    change mu.toMeasure.real A + mu.toMeasure.real Aᶜ = 1
    exact probReal_add_probReal_compl hAmeas
  let w : Convexity.StdSimplex ℝ (Fin (N + 1)) :=
    { weights := Finsupp.equivFunOnFinite.symm coeff
      nonneg := fun i ↦ by change 0 ≤ coeff i; exact hcoeff_nonneg i
      total := by
        rw [Finsupp.sum_fintype _ _ (by simp)]
        simpa using hcoeff_sum }
  have hfiniteLaw_apply (C : Set T) (hC : MeasurableSet C) :
      ((finiteLaw w points : ProbabilityMeasure T) : Measure T) C =
        ∑ i : Fin (N + 1),
          if points i ∈ C then ENNReal.ofReal (coeff i) else 0 := by
    rw [finiteLaw_toMeasure, Measure.sum_apply _ hC]
    simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hC, tsum_fintype]
    change (∑ i, ENNReal.ofReal (coeff i) * C.indicator 1 (points i)) = _
    simp [Set.indicator_apply]
  refine ⟨N + 1, w, points, ?_⟩
  rw [levyProkhorovDist_comm]
  refine (levyProkhorovDist_le_of_forall_le mu.toMeasure
    (finiteLaw w points : ProbabilityMeasure T) (δ := epsilon / 2) hhalf.le ?_).trans_lt
      (by linarith)
  intro delta B hdelta hB
  let C : Set T := Metric.thickening delta B
  have hC : MeasurableSet C := Metric.isOpen_thickening.measurableSet
  let J : Finset ℕ := (Finset.range N).filter fun i ↦ (B ∩ E i).Nonempty
  have hJsub : J ⊆ Finset.range N := Finset.filter_subset _ _
  have hpoints_mem (i : ℕ) (hi : i ∈ J) :
      points ⟨i, (Finset.mem_range.mp (hJsub hi)).trans (Nat.lt_succ_self N)⟩ ∈ C := by
    have hiN : i < N := Finset.mem_range.mp (hJsub hi)
    have hiBE : (B ∩ E i).Nonempty := (Finset.mem_filter.mp hi).2
    obtain ⟨z, hzB, hzE⟩ := hiBE
    have hyE : y i ∈ E i := hy i ⟨z, hzE⟩
    have hdist : dist (y i) z ≤ epsilon / 2 :=
      (Metric.dist_le_diam_of_mem (hEbounded i) hyE hzE).trans (hEdiam i)
    have hpoint : points ⟨i, hiN.trans (Nat.lt_succ_self N)⟩ = y i := by
      simp only [points, hiN, dite_true]
    rw [hpoint, Metric.mem_thickening_iff]
    exact ⟨z, hzB, hdist.trans_lt hdelta⟩
  have hsum_reindex :
      ∑ i ∈ J, mu.toMeasure (E i) =
        ∑ i : Fin N, if i.val ∈ J then mu.toMeasure (E i.val) else 0 := by
    rw [Finset.sum_fin_eq_sum_range]
    symm
    calc
      (∑ i ∈ Finset.range N,
          if hi : i < N then (if i ∈ J then mu.toMeasure (E i) else 0) else 0) =
          ∑ i ∈ Finset.range N, if i ∈ J then mu.toMeasure (E i) else 0 := by
            apply Finset.sum_congr rfl
            intro i hi
            simp only [dif_pos (Finset.mem_range.mp hi)]
      _ = ∑ i ∈ J, mu.toMeasure (E i) := by
        rw [← Finset.sum_filter]
        apply Finset.sum_congr
        · ext i
          simp only [Finset.mem_filter, Finset.mem_range]
          constructor
          · exact fun h ↦ h.2
          · exact fun h ↦ ⟨Finset.mem_range.mp (hJsub h), h⟩
        · intro i hi
          rfl
  have hsum_le_law :
      ∑ i ∈ J, mu.toMeasure (E i) ≤
        ((finiteLaw w points : ProbabilityMeasure T) : Measure T) C := by
    rw [hfiniteLaw_apply C hC, Fin.sum_univ_castSucc, hsum_reindex]
    calc
      (∑ i : Fin N, if i.val ∈ J then mu.toMeasure (E i.val) else 0) ≤
          ∑ i : Fin N,
            if points i.castSucc ∈ C then ENNReal.ofReal (coeff i.castSucc) else 0 := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hiJ : i.val ∈ J
        · have hp := hpoints_mem i.val hiJ
          have hiN : i.val < N := i.isLt
          have hp' : points i.castSucc ∈ C := by
            have hiEq : i.castSucc =
                ⟨i.val, (Finset.mem_range.mp (hJsub hiJ)).trans (Nat.lt_succ_self N)⟩ :=
              Fin.ext rfl
            rw [hiEq]
            exact hp
          simp only [hiJ, hp', if_true, coeff, Fin.val_castSucc, hiN, dite_true]
          exact (ENNReal.ofReal_toReal (measure_ne_top mu.toMeasure (E i.val))).symm.le
        · simp only [hiJ, if_false]
          exact bot_le
      _ ≤ (∑ i : Fin N,
            if points i.castSucc ∈ C then ENNReal.ofReal (coeff i.castSucc) else 0) +
          (if points (Fin.last N) ∈ C then ENNReal.ofReal (coeff (Fin.last N)) else 0) :=
        le_add_right le_rfl
  have hBsub : B ⊆ (⋃ i ∈ (J : Set ℕ), E i) ∪ Aᶜ := by
    intro z hzB
    by_cases hzA : z ∈ A
    · left
      simp only [A, mem_iUnion, mem_Iio] at hzA
      obtain ⟨i, hiN, hzE⟩ := hzA
      exact mem_iUnion₂_of_mem (show i ∈ J by
        simp only [J, Finset.mem_filter, Finset.mem_range]
        exact ⟨hiN, ⟨z, hzB, hzE⟩⟩) hzE
    · exact Or.inr hzA
  have hmeasureJ : mu.toMeasure (⋃ i ∈ (J : Set ℕ), E i) =
      ∑ i ∈ J, mu.toMeasure (E i) := by
    calc
      mu.toMeasure (⋃ i ∈ (J : Set ℕ), E i) =
          mu.toMeasure (⋃ i ∈ (J : Finset ℕ), E i) := by rfl
      _ = ∑ i ∈ J, mu.toMeasure (E i) :=
        measure_biUnion_finset (hEdisjoint.set_pairwise J) (fun i _ ↦ hEmeas i)
  calc
    mu.toMeasure B ≤ mu.toMeasure ((⋃ i ∈ (J : Set ℕ), E i) ∪ Aᶜ) := measure_mono hBsub
    _ ≤ mu.toMeasure (⋃ i ∈ (J : Set ℕ), E i) + mu.toMeasure Aᶜ := measure_union_le _ _
    _ = (∑ i ∈ J, mu.toMeasure (E i)) + mu.toMeasure Aᶜ := by
      rw [hmeasureJ]
    _ ≤ ((finiteLaw w points : ProbabilityMeasure T) : Measure T) C +
        ENNReal.ofReal delta := by
      apply add_le_add hsum_le_law
      exact hN.le.trans (ENNReal.ofReal_le_ofReal hdelta.le)
    _ = ((finiteLaw w points : ProbabilityMeasure T) : Measure T)
        (Metric.thickening delta B) + ENNReal.ofReal delta := by rfl

theorem secondCountableTopology_probabilityMeasure :
    SecondCountableTopology (ProbabilityMeasure T) := by
  let S : Set (LevyProkhorov (ProbabilityMeasure T)) :=
    ⋃ n : ℕ, Set.range (fun p : Convexity.StdSimplex ℝ (Fin n) × (Fin n → T) ↦
      LevyProkhorov.ofMeasure (finiteLaw p.1 p.2))
  have hSseparable : IsSeparable S := by
    apply IsSeparable.iUnion
    intro n
    let hw := Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin n)
    letI : SecondCountableTopology (Convexity.StdSimplex ℝ (Fin n)) :=
      hw.secondCountableTopology
    apply isSeparable_range
    exact LevyProkhorov.continuous_ofMeasure_probabilityMeasure.comp continuous_finiteLaw
  have hSdense : Dense S := Metric.dense_iff.mpr fun mu r hr ↦ by
    obtain ⟨n, w, x, hx⟩ := exists_finiteLaw_levyProkhorovDist_lt mu.toMeasure hr
    refine ⟨LevyProkhorov.ofMeasure (finiteLaw w x), ?_, ?_⟩
    · simpa only [Metric.mem_ball, LevyProkhorov.dist_probabilityMeasure_def,
        levyProkhorovDist_comm] using hx
    · exact mem_iUnion_of_mem n ⟨(w, x), rfl⟩
  letI : SeparableSpace (LevyProkhorov (ProbabilityMeasure T)) :=
    (hSdense.isSeparable_iff.mp hSseparable)
  letI : SecondCountableTopology (LevyProkhorov (ProbabilityMeasure T)) :=
    UniformSpace.secondCountable_of_separable _
  exact LevyProkhorov.probabilityMeasureHomeomorph.isEmbedding.secondCountableTopology

private lemma probabilityMeasure_topology_eq_iInf :
    (inferInstance : TopologicalSpace (ProbabilityMeasure T)) =
      ⨅ f : BoundedContinuousFunction T ℝ≥0,
        TopologicalSpace.induced
          (fun mu : ProbabilityMeasure T ↦ mu.toWeakDualBCNN f) inferInstance := by
  change TopologicalSpace.induced ProbabilityMeasure.toFiniteMeasure
      (TopologicalSpace.induced FiniteMeasure.toWeakDualBCNN
        (TopologicalSpace.induced (fun x f ↦ x f) Pi.topologicalSpace)) = _
  rw [induced_compose, induced_compose, induced_to_pi]
  rfl

private lemma probabilityMeasure_topology_eq_generateFrom :
    (inferInstance : TopologicalSpace (ProbabilityMeasure T)) =
      TopologicalSpace.generateFrom
        (⋃ f : BoundedContinuousFunction T ℝ≥0,
          (fun U : Set ℝ≥0 ↦ (fun mu : ProbabilityMeasure T ↦ mu.toWeakDualBCNN f) ⁻¹' U) ''
            {U : Set ℝ≥0 | IsOpen U}) := by
  rw [probabilityMeasure_topology_eq_iInf]
  calc
    (⨅ f : BoundedContinuousFunction T ℝ≥0,
        TopologicalSpace.induced
          (fun mu : ProbabilityMeasure T ↦ mu.toWeakDualBCNN f) inferInstance) =
      ⨅ f : BoundedContinuousFunction T ℝ≥0,
        TopologicalSpace.induced
          (fun mu : ProbabilityMeasure T ↦ mu.toWeakDualBCNN f)
          (TopologicalSpace.generateFrom {U : Set ℝ≥0 | IsOpen U}) := by
            congr 1
            funext f
            rw [generateFrom_setOfPred_isOpen]
    _ = _ := by
      calc
        (⨅ f : BoundedContinuousFunction T ℝ≥0,
            TopologicalSpace.induced
              (fun mu : ProbabilityMeasure T ↦ mu.toWeakDualBCNN f)
              (TopologicalSpace.generateFrom {U : Set ℝ≥0 | IsOpen U})) =
          ⨅ f : BoundedContinuousFunction T ℝ≥0,
            TopologicalSpace.generateFrom
              ((fun U : Set ℝ≥0 ↦
                (fun mu : ProbabilityMeasure T ↦ mu.toWeakDualBCNN f) ⁻¹' U) ''
                  {U : Set ℝ≥0 | IsOpen U}) := by
                    congr 1
                    funext f
                    exact induced_generateFrom_eq
        _ = _ := generateFrom_iUnion.symm

private lemma measurable_toWeakDualBCNN_apply
    (f : BoundedContinuousFunction T ℝ≥0) :
    Measurable fun mu : ProbabilityMeasure T ↦ mu.toWeakDualBCNN f := by
  rw [measurable_iff_comap_le]
  change MeasurableSpace.comap
      (fun mu : ProbabilityMeasure T ↦
        (∫⁻ t, (f t : ℝ≥0∞) ∂(mu : Measure T)).toNNReal) inferInstance ≤ _
  rw [← measurable_iff_comap_le]
  exact ENNReal.measurable_toNNReal.comp
    ((Measure.measurable_lintegral f.measurable_coe_ennreal_comp).comp measurable_subtype_coe)

theorem opensMeasurableSpace_probabilityMeasure :
    OpensMeasurableSpace (ProbabilityMeasure T) := by
  letI : SecondCountableTopology (ProbabilityMeasure T) :=
    secondCountableTopology_probabilityMeasure
  refine ⟨?_⟩
  rw [borel_eq_generateFrom_of_subbasis probabilityMeasure_topology_eq_generateFrom]
  apply MeasurableSpace.generateFrom_le
  intro s hs
  simp only [mem_iUnion, mem_image] at hs
  obtain ⟨f, U, hUopen, rfl⟩ := hs
  change IsOpen U at hUopen
  exact (measurable_toWeakDualBCNN_apply f) hUopen.measurableSet

end

end MeasureTheory
