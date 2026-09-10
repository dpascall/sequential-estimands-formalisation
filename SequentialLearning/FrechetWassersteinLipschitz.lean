import SequentialLearning.FrechetRiskWellPosedness
import SequentialLearning.Wasserstein2

/-!
# Frechet risk is Lipschitz in centre and law

This file formalises Result 15.  It deliberately uses the direct coupling
definition of Wasserstein distance on the original measurable pseudometric
space.  Quotients and completions enter only later, when regular conditional
laws are transported to a Polish metric space.
-/

namespace SequentialLearning

open Filter MeasureTheory Set
open scoped ENNReal MeasureTheory

noncomputable section

variable {S : Type*} [PseudoMetricSpace S] [MeasurableSpace S] [Nonempty S]
  [OpensMeasurableSpace S] [TopologicalSpace.SeparableSpace S]

/-- Pull the first marginal's root risk back to a coupling. -/
theorem frechetRootRisk_eq_coupling_fst
    {mu nu : ProbabilityMeasure S} (pi : TransportCoupling mu nu) (s : S) :
    frechetRootRisk mu.toMeasure s =
      eLpNorm (fun xy : S × S => dist xy.1 s) 2 pi.law.toMeasure := by
  have hMarginal : Measure.map Prod.fst pi.law.toMeasure = mu.toMeasure := by
    simpa only [ProbabilityMeasure.toMeasure_map] using
      congrArg ProbabilityMeasure.toMeasure pi.fst_eq
  rw [frechetRootRisk, ← hMarginal, eLpNorm_map_measure]
  · rfl
  · exact (measurable_dist_to s).aestronglyMeasurable
  · exact measurable_fst.aemeasurable

/-- Pull the second marginal's root risk back to a coupling. -/
theorem frechetRootRisk_eq_coupling_snd
    {mu nu : ProbabilityMeasure S} (pi : TransportCoupling mu nu) (s : S) :
    frechetRootRisk nu.toMeasure s =
      eLpNorm (fun xy : S × S => dist xy.2 s) 2 pi.law.toMeasure := by
  have hMarginal : Measure.map Prod.snd pi.law.toMeasure = nu.toMeasure := by
    simpa only [ProbabilityMeasure.toMeasure_map] using
      congrArg ProbabilityMeasure.toMeasure pi.snd_eq
  rw [frechetRootRisk, ← hMarginal, eLpNorm_map_measure]
  · rfl
  · exact (measurable_dist_to s).aestronglyMeasurable
  · exact measurable_snd.aemeasurable

/-- A single coupling controls simultaneous movement of the probability law
and of the proposed centre. -/
theorem frechetRootRisk_le_of_coupling
    {mu nu : ProbabilityMeasure S} (pi : TransportCoupling mu nu) (s t : S) :
    frechetRootRisk mu.toMeasure s ≤
      frechetRootRisk nu.toMeasure t + transportL2Cost pi +
        ENNReal.ofReal (dist s t) := by
  let f : S × S → ℝ := fun xy => dist xy.2 t
  let g : S × S → ℝ := fun xy => dist xy.1 xy.2
  let h : S × S → ℝ := fun _ => dist s t
  have hf : AEStronglyMeasurable f pi.law.toMeasure := by
    exact (measurable_snd.dist measurable_const).aestronglyMeasurable
  have hg : AEStronglyMeasurable g pi.law.toMeasure := by
    exact (measurable_fst.dist measurable_snd).aestronglyMeasurable
  have hh : AEStronglyMeasurable h pi.law.toMeasure :=
    aestronglyMeasurable_const
  calc
    frechetRootRisk mu.toMeasure s =
        eLpNorm (fun xy : S × S => dist xy.1 s) 2 pi.law.toMeasure :=
      frechetRootRisk_eq_coupling_fst pi s
    _ ≤ eLpNorm (f + g + h) 2 pi.law.toMeasure := by
      apply eLpNorm_mono_ae
      filter_upwards with xy
      simp only [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg dist_nonneg,
        abs_of_nonneg (add_nonneg (add_nonneg dist_nonneg dist_nonneg) dist_nonneg),
        f, g, h]
      calc
        dist xy.1 s ≤ dist xy.1 xy.2 + dist xy.2 s := dist_triangle _ _ _
        _ ≤ (dist xy.2 t + dist xy.1 xy.2) + dist s t := by
          have hts : dist xy.2 s ≤ dist xy.2 t + dist s t := by
            simpa [dist_comm s t] using dist_triangle xy.2 t s
          linarith
    _ ≤ eLpNorm (f + g) 2 pi.law.toMeasure +
        eLpNorm h 2 pi.law.toMeasure := by
      exact eLpNorm_add_le (hf.add hg) hh (by norm_num)
    _ ≤ (eLpNorm f 2 pi.law.toMeasure + eLpNorm g 2 pi.law.toMeasure) +
        eLpNorm h 2 pi.law.toMeasure := by
      gcongr
      exact eLpNorm_add_le hf hg (by norm_num)
    _ = frechetRootRisk nu.toMeasure t + transportL2Cost pi +
        ENNReal.ofReal (dist s t) := by
      rw [frechetRootRisk_eq_coupling_snd pi t]
      rw [eLpNorm_const (dist s t) (by norm_num)
        (IsProbabilityMeasure.ne_zero pi.law.toMeasure)]
      simp only [transportL2Cost, f, g]
      simp [Real.enorm_eq_ofReal_abs, abs_of_nonneg dist_nonneg]

/-- The transport cost of any coupling is bounded by the two root risks at a
common centre.  In particular, finite second moments force `W₂ < ∞`. -/
theorem transportL2Cost_le_rootRisk_add
    {mu nu : ProbabilityMeasure S} (pi : TransportCoupling mu nu) (s : S) :
    transportL2Cost pi ≤
      frechetRootRisk mu.toMeasure s + frechetRootRisk nu.toMeasure s := by
  let f : S × S → ℝ := fun xy => dist xy.1 s
  let g : S × S → ℝ := fun xy => dist xy.2 s
  have hf : AEStronglyMeasurable f pi.law.toMeasure := by
    exact (measurable_fst.dist measurable_const).aestronglyMeasurable
  have hg : AEStronglyMeasurable g pi.law.toMeasure := by
    exact (measurable_snd.dist measurable_const).aestronglyMeasurable
  calc
    transportL2Cost pi ≤ eLpNorm (f + g) 2 pi.law.toMeasure := by
      apply eLpNorm_mono_ae
      filter_upwards with xy
      simp only [Pi.add_apply, Real.norm_eq_abs,
        abs_of_nonneg dist_nonneg,
        abs_of_nonneg (add_nonneg dist_nonneg dist_nonneg), f, g]
      simpa [dist_comm s xy.2] using dist_triangle xy.1 s xy.2
    _ ≤ eLpNorm f 2 pi.law.toMeasure + eLpNorm g 2 pi.law.toMeasure :=
      eLpNorm_add_le hf hg (by norm_num)
    _ = frechetRootRisk mu.toMeasure s + frechetRootRisk nu.toMeasure s := by
      rw [frechetRootRisk_eq_coupling_fst pi s,
        frechetRootRisk_eq_coupling_snd pi s]

/-- Result 15(i): root Frechet risk is jointly one-Lipschitz in the law
(for `W₂`) and the centre (for `d`). -/
theorem frechetRootRisk_le_add_wasserstein2_add_dist
    (mu nu : ProbabilityMeasure S) (s t : S) :
    frechetRootRisk mu.toMeasure s ≤
      frechetRootRisk nu.toMeasure t + wasserstein2 mu nu +
        ENNReal.ofReal (dist s t) := by
  rw [wasserstein2, ENNReal.add_iInf, ENNReal.iInf_add]
  exact le_iInf fun pi => frechetRootRisk_le_of_coupling pi s t

/-- Finite second moments imply finite direct pseudometric Wasserstein cost. -/
theorem wasserstein2_lt_top_of_finiteSecondMoment
    (mu nu : ProbabilityMeasure S)
    (hmu : HasFiniteSecondMoment mu.toMeasure)
    (hnu : HasFiniteSecondMoment nu.toMeasure) :
    wasserstein2 mu nu < ∞ := by
  obtain ⟨s, hs⟩ := hmu
  have hmuRoot : frechetRootRisk mu.toMeasure s < ∞ :=
    (frechetRisk_lt_top_iff_rootRisk_lt_top mu.toMeasure s).1 hs
  have hnuRoot : frechetRootRisk nu.toMeasure s < ∞ :=
    (frechetRootRisk_finite_everywhere_iff nu.toMeasure).1 hnu s
  let pi := TransportCoupling.independent mu nu
  refine (wasserstein2_le_transportL2Cost pi).trans_lt ?_
  refine (transportL2Cost_le_rootRisk_add pi s).trans_lt ?_
  exact ENNReal.add_lt_top.2 ⟨hmuRoot, hnuRoot⟩

/-- Result 15(ii), as an explicit absolute-value inequality. -/
theorem frechetRootRisk_toReal_abs_sub_le_dist
    (mu : ProbabilityMeasure S) (hmu : HasFiniteSecondMoment mu.toMeasure)
    (s t : S) :
    |(frechetRootRisk mu.toMeasure s).toReal -
        (frechetRootRisk mu.toMeasure t).toReal| ≤ dist s t := by
  have h := (frechetRootRisk_toReal_lipschitz mu.toMeasure hmu).dist_le_mul s t
  simpa [Real.dist_eq] using h

/-- The square-root Frechet variance, expressed directly as the infimum of
root risks.  A later bridge theorem identifies its square with
`frechetVariance`. -/
def frechetRootVariance (nu : Measure S) : ENNReal :=
  ⨅ s : S, frechetRootRisk nu s

/-- The infimum of root risks is exactly the square root of the infimum of
squared risks.  Stating this explicitly avoids hiding an interchange of
infimum and squaring. -/
theorem frechetRootVariance_sq (nu : Measure S) :
    frechetRootVariance nu ^ 2 = frechetVariance nu := by
  apply le_antisymm
  · rw [frechetRootVariance, frechetVariance]
    refine le_iInf fun s => ?_
    exact pow_le_pow_left₀ bot_le (iInf_le (fun t => frechetRootRisk nu t) s) 2
  · let r : ENNReal := frechetVariance nu ^ ((2 : ℝ)⁻¹)
    have hr_sq : r ^ 2 = frechetVariance nu := by
      dsimp [r]
      exact ENNReal.rpow_inv_natCast_pow (by norm_num) _
    have hr_le : r ≤ frechetRootVariance nu := by
      rw [frechetRootVariance]
      refine le_iInf fun s => ?_
      rw [← ENNReal.rpow_le_rpow_iff (z := (2 : ℝ)) (by norm_num)]
      rw [ENNReal.rpow_two, ENNReal.rpow_two, hr_sq]
      have hVs : frechetVariance nu ≤ frechetRisk nu s :=
        frechetVariance_le nu s
      simpa [frechetRisk] using hVs
    have hsq := ENNReal.rpow_le_rpow hr_le (show 0 ≤ (2 : ℝ) by norm_num)
    rw [ENNReal.rpow_two, ENNReal.rpow_two, hr_sq] at hsq
    exact hsq

/-- Real-valued form of `frechetRootVariance_sq`. -/
theorem frechetRootVariance_toReal_eq_sqrt (nu : Measure S) :
    (frechetRootVariance nu).toReal =
      Real.sqrt (frechetVariance nu).toReal := by
  have hsq : (frechetRootVariance nu).toReal ^ 2 =
      (frechetVariance nu).toReal := by
    simpa using congrArg ENNReal.toReal (frechetRootVariance_sq nu)
  rw [← hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]

/-- The square-root Frechet variance satisfies the one-sided `W₂` bound. -/
theorem frechetRootVariance_le_add_wasserstein2
    (mu nu : ProbabilityMeasure S) :
    frechetRootVariance mu.toMeasure ≤
      frechetRootVariance nu.toMeasure + wasserstein2 mu nu := by
  rw [frechetRootVariance, frechetRootVariance, ENNReal.iInf_add]
  refine le_iInf fun s => ?_
  exact (iInf_le_of_le s <| by
    simpa using frechetRootRisk_le_add_wasserstein2_add_dist mu nu s s)

/-- Finite Wasserstein cost is symmetric, so the two one-sided variance
bounds combine to an absolute-value estimate after conversion to reals. -/
theorem frechetRootVariance_toReal_abs_sub_le
    (mu nu : ProbabilityMeasure S)
    (hmu : frechetRootVariance mu.toMeasure ≠ ∞)
    (hnu : frechetRootVariance nu.toMeasure ≠ ∞)
    (hW : wasserstein2 mu nu ≠ ∞) :
    |(frechetRootVariance mu.toMeasure).toReal -
        (frechetRootVariance nu.toMeasure).toReal| ≤
      (wasserstein2 mu nu).toReal := by
  have hForward := frechetRootVariance_le_add_wasserstein2 mu nu
  have hBackward := frechetRootVariance_le_add_wasserstein2 nu mu
  rw [← wasserstein2_comm] at hBackward
  have hForwardReal := ENNReal.toReal_mono
    (ENNReal.add_ne_top.2 ⟨hnu, hW⟩) hForward
  have hBackwardReal := ENNReal.toReal_mono
    (ENNReal.add_ne_top.2 ⟨hmu, hW⟩) hBackward
  rw [ENNReal.toReal_add hnu hW] at hForwardReal
  rw [ENNReal.toReal_add hmu hW] at hBackwardReal
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- Result 15(iii), in the manuscript's square-root variance notation. -/
theorem sqrt_frechetVariance_abs_sub_le_wasserstein2
    (mu nu : ProbabilityMeasure S)
    (hmu : HasFiniteSecondMoment mu.toMeasure)
    (hnu : HasFiniteSecondMoment nu.toMeasure) :
    |Real.sqrt (frechetVariance mu.toMeasure).toReal -
        Real.sqrt (frechetVariance nu.toMeasure).toReal| ≤
      (wasserstein2 mu nu).toReal := by
  have hmuRoot : frechetRootVariance mu.toMeasure ≠ ∞ := by
    obtain ⟨s, hs⟩ := hmu
    have hsRoot : frechetRootRisk mu.toMeasure s < ∞ :=
      (frechetRisk_lt_top_iff_rootRisk_lt_top mu.toMeasure s).1 hs
    exact ne_of_lt ((iInf_le (fun t => frechetRootRisk mu.toMeasure t) s).trans_lt hsRoot)
  have hnuRoot : frechetRootVariance nu.toMeasure ≠ ∞ := by
    obtain ⟨s, hs⟩ := hnu
    have hsRoot : frechetRootRisk nu.toMeasure s < ∞ :=
      (frechetRisk_lt_top_iff_rootRisk_lt_top nu.toMeasure s).1 hs
    exact ne_of_lt ((iInf_le (fun t => frechetRootRisk nu.toMeasure t) s).trans_lt hsRoot)
  have hW : wasserstein2 mu nu ≠ ∞ :=
    (wasserstein2_lt_top_of_finiteSecondMoment mu nu hmu hnu).ne
  rw [← frechetRootVariance_toReal_eq_sqrt,
    ← frechetRootVariance_toReal_eq_sqrt]
  exact frechetRootVariance_toReal_abs_sub_le mu nu hmuRoot hnuRoot hW

end

end SequentialLearning
