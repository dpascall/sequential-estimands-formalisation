import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConditionalExpectation.LebesgueBochner
import Mathlib.MeasureTheory.Function.ConditionalLExpectation

/-!
# Well-posedness of Frechet risk and variance

This file formalises the foundational well-posedness lemma for the manuscript's
conditional Frechet variance on a separable pseudometric space.  The measurable
space on the target may be strictly finer than its Borel measurable space;
`OpensMeasurableSpace S` records precisely the inclusion needed to make squared
distance measurable.
-/

namespace SequentialLearning

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal MeasureTheory ProbabilityTheory

noncomputable section

section FrechetRisk

variable {S : Type*} [PseudoMetricSpace S] [MeasurableSpace S] [Nonempty S]
  [OpensMeasurableSpace S]

/-- Root mean-square distance from a measure to a proposed centre. -/
def frechetRootRisk (nu : Measure S) (s : S) : ENNReal :=
  eLpNorm (fun x : S => dist x s) 2 nu

/-- Squared Frechet risk of a proposed centre. -/
def frechetRisk (nu : Measure S) (s : S) : ENNReal :=
  frechetRootRisk nu s ^ 2

/-- Frechet variance, as an extended-real infimum over all centres. -/
def frechetVariance (nu : Measure S) : ENNReal :=
  iInf (frechetRisk nu)

omit [Nonempty S] in
theorem measurable_dist_to (s : S) : Measurable fun x : S => dist x s := by
  fun_prop

omit [Nonempty S] [OpensMeasurableSpace S] in
theorem frechetRisk_eq_lintegral (nu : Measure S) (s : S) :
    frechetRisk nu s = ∫⁻ x, ENNReal.ofReal (dist x s ^ 2) ∂nu := by
  rw [frechetRisk, frechetRootRisk]
  calc
    eLpNorm (fun x : S => dist x s) 2 nu ^ 2 =
        eLpNorm (fun x : S => dist x s) 2 nu ^ (2 : ℝ) :=
      (ENNReal.rpow_two _).symm
    _ = ∫⁻ x, ‖dist x s‖ₑ ^ (2 : ℝ) ∂nu :=
      eLpNorm_nnreal_pow_eq_lintegral (p := (2 : NNReal)) (by norm_num)
    _ = ∫⁻ x, ENNReal.ofReal (dist x s ^ 2) ∂nu := by
      apply lintegral_congr
      intro x
      simp only [Real.enorm_eq_ofReal_abs]
      rw [abs_of_nonneg (dist_nonneg : 0 ≤ dist x s)]
      norm_num [ENNReal.rpow_two]

/-- A probability measure has a finite second moment if its squared risk is
finite at at least one centre.  The centre-independence is proved below. -/
def HasFiniteSecondMoment (nu : Measure S) : Prop :=
  ∃ s : S, frechetRisk nu s < ∞

omit [Nonempty S] [OpensMeasurableSpace S] in
theorem frechetRisk_lt_top_iff_rootRisk_lt_top
    (nu : Measure S) (s : S) :
    frechetRisk nu s < ∞ ↔ frechetRootRisk nu s < ∞ := by
  simp [frechetRisk]

omit [Nonempty S] in
theorem frechetRootRisk_le_add_dist
    (nu : Measure S) [IsProbabilityMeasure nu] (s t : S) :
    frechetRootRisk nu s ≤
      frechetRootRisk nu t + ENNReal.ofReal (dist s t) := by
  have hDistS : AEStronglyMeasurable (fun x : S => dist x s) nu :=
    (measurable_dist_to s).aestronglyMeasurable
  have hDistT : AEStronglyMeasurable (fun x : S => dist x t) nu :=
    (measurable_dist_to t).aestronglyMeasurable
  have hConst : AEStronglyMeasurable (fun _ : S => dist s t) nu :=
    aestronglyMeasurable_const
  calc
    frechetRootRisk nu s ≤
        eLpNorm (fun x : S => dist x t + dist s t) 2 nu := by
      apply eLpNorm_mono_ae
      filter_upwards with x
      simpa only [Real.norm_eq_abs, abs_of_nonneg dist_nonneg,
        abs_of_nonneg (add_nonneg dist_nonneg dist_nonneg), dist_comm] using
          (dist_triangle x t s)
    _ ≤ eLpNorm (fun x : S => dist x t) 2 nu +
        eLpNorm (fun _ : S => dist s t) 2 nu := by
      exact eLpNorm_add_le hDistT hConst (by norm_num)
    _ = frechetRootRisk nu t + ENNReal.ofReal (dist s t) := by
      rw [frechetRootRisk,
        eLpNorm_const (dist s t) (by norm_num) (IsProbabilityMeasure.ne_zero nu)]
      simp [Real.enorm_eq_ofReal_abs, abs_of_nonneg dist_nonneg]

omit [Nonempty S] in
/-- Pseudometrically indistinguishable centres have identical risks. -/
theorem frechetRootRisk_eq_of_dist_eq_zero
    (nu : Measure S) [IsProbabilityMeasure nu] {s t : S}
    (hst : dist s t = 0) :
    frechetRootRisk nu s = frechetRootRisk nu t := by
  apply le_antisymm
  · simpa [hst] using frechetRootRisk_le_add_dist nu s t
  · simpa [dist_comm, hst] using frechetRootRisk_le_add_dist nu t s

omit [Nonempty S] in
theorem frechetRisk_eq_of_dist_eq_zero
    (nu : Measure S) [IsProbabilityMeasure nu] {s t : S}
    (hst : dist s t = 0) :
    frechetRisk nu s = frechetRisk nu t := by
  rw [frechetRisk, frechetRisk,
    frechetRootRisk_eq_of_dist_eq_zero nu hst]

omit [Nonempty S] in
theorem frechetRootRisk_absorbs_finiteness
    (nu : Measure S) [IsProbabilityMeasure nu] {s t : S}
    (hs : frechetRootRisk nu s < ∞) :
    frechetRootRisk nu t < ∞ := by
  refine (frechetRootRisk_le_add_dist nu t s).trans_lt ?_
  exact ENNReal.add_lt_top.2 ⟨hs, ENNReal.ofReal_lt_top⟩

/-- Root risks are either finite at every centre or infinite at every centre. -/
theorem frechetRootRisk_finite_everywhere_iff
    (nu : Measure S) [IsProbabilityMeasure nu] :
    HasFiniteSecondMoment nu ↔ ∀ s : S, frechetRootRisk nu s < ∞ := by
  constructor
  · rintro ⟨t, ht⟩ s
    exact frechetRootRisk_absorbs_finiteness nu
      ((frechetRisk_lt_top_iff_rootRisk_lt_top nu t).1 ht)
  · intro h
    exact ⟨Classical.arbitrary S,
      (frechetRisk_lt_top_iff_rootRisk_lt_top nu _).2 (h _)⟩

omit [Nonempty S] [OpensMeasurableSpace S] in
theorem frechetRootRisk_eq_top_everywhere_iff
    (nu : Measure S) [IsProbabilityMeasure nu] :
    (¬ HasFiniteSecondMoment nu) ↔
      ∀ s : S, frechetRootRisk nu s = ∞ := by
  constructor
  · intro h s
    exact top_unique (not_lt.mp fun hs => h ⟨s,
      (frechetRisk_lt_top_iff_rootRisk_lt_top nu s).2 hs⟩)
  · rintro h ⟨s, hs⟩
    have hsRoot := (frechetRisk_lt_top_iff_rootRisk_lt_top nu s).1 hs
    rw [h s] at hsRoot
    exact (lt_irrefl ∞ hsRoot)

/-- On the finite-second-moment branch, root risk is a real-valued
one-Lipschitz function of the centre. -/
theorem frechetRootRisk_toReal_lipschitz
    (nu : Measure S) [IsProbabilityMeasure nu]
    (hnu : HasFiniteSecondMoment nu) :
    LipschitzWith 1 (fun s : S => (frechetRootRisk nu s).toReal) := by
  have hFinite : ∀ s : S, frechetRootRisk nu s ≠ ∞ :=
    fun s => (frechetRootRisk_finite_everywhere_iff nu).1 hnu s |>.ne
  refine lipschitzWith_iff_dist_le_mul.2 fun s t => ?_
  have hst := frechetRootRisk_le_add_dist nu s t
  have hts := frechetRootRisk_le_add_dist nu t s
  have hstReal :
      (frechetRootRisk nu s).toReal ≤
        (frechetRootRisk nu t).toReal + dist s t := by
    have := ENNReal.toReal_mono
      (ENNReal.add_ne_top.2 ⟨hFinite t, ENNReal.ofReal_ne_top⟩) hst
    simpa [ENNReal.toReal_add (hFinite t) ENNReal.ofReal_ne_top] using this
  have htsReal :
      (frechetRootRisk nu t).toReal ≤
        (frechetRootRisk nu s).toReal + dist s t := by
    have := ENNReal.toReal_mono
      (ENNReal.add_ne_top.2 ⟨hFinite s, ENNReal.ofReal_ne_top⟩) hts
    simpa [ENNReal.toReal_add (hFinite s) ENNReal.ofReal_ne_top, dist_comm] using this
  rw [Real.dist_eq]
  simp only [NNReal.coe_one, one_mul]
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- Finite-second-moment Frechet risk is continuous in its centre. -/
theorem continuous_frechetRisk
    (nu : Measure S) [IsProbabilityMeasure nu]
    (hnu : HasFiniteSecondMoment nu) :
    Continuous (frechetRisk nu) := by
  have hFinite : ∀ s : S, frechetRootRisk nu s ≠ ∞ :=
    fun s => (frechetRootRisk_finite_everywhere_iff nu).1 hnu s |>.ne
  have hRoot : Continuous (fun s : S => (frechetRootRisk nu s).toReal) :=
    (frechetRootRisk_toReal_lipschitz nu hnu).continuous
  have hRepresentation :
      frechetRisk nu = fun s : S =>
        ENNReal.ofReal ((frechetRootRisk nu s).toReal ^ 2) := by
    funext s
    rw [frechetRisk]
    calc
      frechetRootRisk nu s ^ 2 =
          ENNReal.ofReal (frechetRootRisk nu s).toReal ^ 2 :=
        congrArg (fun x : ENNReal => x ^ 2)
          (ENNReal.ofReal_toReal (hFinite s)).symm
      _ = ENNReal.ofReal ((frechetRootRisk nu s).toReal ^ 2) :=
        (ENNReal.ofReal_pow ENNReal.toReal_nonneg 2).symm
  rw [hRepresentation]
  exact ENNReal.continuous_ofReal.comp (hRoot.pow 2)

omit [Nonempty S] [OpensMeasurableSpace S] in
theorem frechetVariance_nonneg (nu : Measure S) :
    0 ≤ frechetVariance nu :=
  bot_le

omit [Nonempty S] [OpensMeasurableSpace S] in
theorem frechetVariance_le (nu : Measure S) (s : S) :
    frechetVariance nu ≤ frechetRisk nu s :=
  iInf_le _ s

/-- The infimum over all centres can be replaced by the infimum over any
fixed dense sequence.  This is the countability fact used for posterior
measurability and version independence. -/
theorem frechetVariance_eq_iInf_dense
    (nu : Measure S) [IsProbabilityMeasure nu]
    (D : ℕ → S) (hD : DenseRange D) :
    frechetVariance nu = ⨅ k : ℕ, frechetRisk nu (D k) := by
  have hSubtype :
      (⨅ s : Set.range D, frechetRisk nu s) =
        ⨅ k : ℕ, frechetRisk nu (D k) := by
    apply le_antisymm
    · refine le_iInf fun k => ?_
      exact iInf_le_of_le ⟨D k, ⟨k, rfl⟩⟩ le_rfl
    · refine le_iInf fun s => ?_
      rcases s with ⟨s, ⟨k, hk⟩⟩
      change (⨅ k, frechetRisk nu (D k)) ≤ frechetRisk nu s
      rw [← hk]
      exact iInf_le _ k
  by_cases hnu : HasFiniteSecondMoment nu
  · have hDenseInf := hD.ciInf (continuous_frechetRisk nu hnu)
        (show BddBelow (Set.range (frechetRisk nu)) from
          ⟨0, by rintro z ⟨s, rfl⟩; exact bot_le⟩)
    rw [frechetVariance, ← hDenseInf, hSubtype]
  · have hTop := (frechetRootRisk_eq_top_everywhere_iff nu).1 hnu
    have hRiskTop : ∀ s : S, frechetRisk nu s = ∞ := fun s => by
      simp [frechetRisk, hTop s]
    rw [frechetVariance]
    rw [show frechetRisk nu = fun _ : S => ∞ from funext hRiskTop]
    simp

/-- In a separable target, Mathlib's canonical dense sequence gives the
countable representation without any further choice in later results. -/
theorem frechetVariance_eq_iInf_denseSeq
    [TopologicalSpace.SeparableSpace S]
    (nu : Measure S) [IsProbabilityMeasure nu] :
    frechetVariance nu =
      ⨅ k : ℕ, frechetRisk nu (TopologicalSpace.denseSeq S k) :=
  frechetVariance_eq_iInf_dense nu (TopologicalSpace.denseSeq S)
    (TopologicalSpace.denseRange_denseSeq S)

end FrechetRisk

section PosteriorFrechetRisk

variable {Omega S : Type*} {mOmega : MeasurableSpace Omega}
  [PseudoMetricSpace S] [MeasurableSpace S] [Nonempty S]
  [OpensMeasurableSpace S]

/-- A kernel is a regular conditional law of `X` given `m` when its
composition-product with the restricted base law is the joint law of the
conditioning state and `X`.  This disintegration formulation is equivalent
to the usual setwise definition and gives a clean uniqueness interface. -/
def IsRegularConditionalLaw
    (mu : Measure[mOmega] Omega) (m : MeasurableSpace Omega)
    (hm : m ≤ mOmega) (X : Omega → S)
    (kappa : Kernel[m, (inferInstance : MeasurableSpace S)] Omega S) : Prop :=
  (mu.trim hm) ⊗ₘ kappa =
    @Measure.map Omega (Omega × S) mOmega
      (m.prod (inferInstance : MeasurableSpace S))
      (fun omega => (omega, X omega)) mu

omit [PseudoMetricSpace S] [Nonempty S] [OpensMeasurableSpace S] in
/-- Countable generation of the target sigma-algebra makes a regular
conditional law unique as a kernel outside one common null set. -/
theorem regularConditionalLaw_ae_eq
    [MeasurableSpace.CountablyGenerated S]
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (m : MeasurableSpace Omega) (hm : m ≤ mOmega)
    (X : Omega → S)
    (kappa eta : Kernel[m, (inferInstance : MeasurableSpace S)] Omega S)
    [IsMarkovKernel kappa] [IsMarkovKernel eta]
    (hkappa : IsRegularConditionalLaw mu m hm X kappa)
    (heta : IsRegularConditionalLaw mu m hm X eta) :
    kappa =ᵐ[mu] eta := by
  apply ae_eq_of_ae_eq_trim
  apply Kernel.ae_eq_of_compProd_eq
  exact hkappa.trans heta.symm

omit [Nonempty S] [OpensMeasurableSpace S] in
/-- Posterior Frechet variance is independent of the chosen regular
conditional-law version. -/
theorem posteriorFrechetVariance_ae_eq
    [MeasurableSpace.CountablyGenerated S]
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (m : MeasurableSpace Omega) (hm : m ≤ mOmega)
    (X : Omega → S)
    (kappa eta : Kernel[m, (inferInstance : MeasurableSpace S)] Omega S)
    [IsMarkovKernel kappa] [IsMarkovKernel eta]
    (hkappa : IsRegularConditionalLaw mu m hm X kappa)
    (heta : IsRegularConditionalLaw mu m hm X eta) :
    (fun omega => frechetVariance (kappa omega)) =ᵐ[mu]
      fun omega => frechetVariance (eta omega) := by
  filter_upwards [regularConditionalLaw_ae_eq mu m hm X kappa eta hkappa heta]
    with omega homega
  rw [homega]

/-- Squared distance as a nonnegative extended-real integrand. -/
def squaredDistanceENN (s x : S) : ENNReal :=
  ENNReal.ofReal (dist x s ^ 2)

omit [Nonempty S] in
theorem measurable_squaredDistanceENN (s : S) :
    Measurable (squaredDistanceENN s) := by
  exact ((measurable_dist_to s).pow_const 2).ennreal_ofReal

omit [Nonempty S] in
/-- Posterior risk at a fixed centre is measurable in the conditioning
state. -/
theorem measurable_posteriorFrechetRisk
    (m : MeasurableSpace Omega)
    (kappa : Kernel[m, (inferInstance : MeasurableSpace S)] Omega S)
    [IsMarkovKernel kappa] (s : S) :
    Measurable[m] fun omega => frechetRisk (kappa omega) s := by
  have hIntegral : Measurable[m] fun omega =>
      ∫⁻ x, squaredDistanceENN s x ∂kappa omega := by
    exact (show Measurable[m.prod (inferInstance : MeasurableSpace S)]
        fun p : Omega × S => squaredDistanceENN s p.2 by
      exact (measurable_squaredDistanceENN s).comp
        (@measurable_snd Omega S m (inferInstance : MeasurableSpace S))
      ).lintegral_kernel_prod_right'
  simpa only [frechetRisk_eq_lintegral, squaredDistanceENN] using hIntegral

omit [Nonempty S] in
/-- The kernel integral defining fixed-centre posterior Frechet risk is a
version of conditional nonnegative expectation. -/
theorem posteriorFrechetRisk_ae_eq_condLExp
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (m : MeasurableSpace Omega) (hm : m ≤ mOmega)
    (X : Omega → S) (hX : Measurable[mOmega] X)
    (kappa : Kernel[m, (inferInstance : MeasurableSpace S)] Omega S)
    [IsMarkovKernel kappa]
    (hkappa : IsRegularConditionalLaw mu m hm X kappa)
    (s : S) :
    (fun omega => frechetRisk (kappa omega) s) =ᵐ[mu]
      mu⁻[fun omega => squaredDistanceENN s (X omega) | m] := by
  apply MeasureTheory.ae_eq_condLExp hm mu
    (fun omega => squaredDistanceENN s (X omega))
    (measurable_posteriorFrechetRisk m kappa s)
  intro A hA
  have hPost : Measurable[m] fun omega =>
      ∫⁻ x, squaredDistanceENN s x ∂kappa omega := by
    exact (show Measurable[m.prod (inferInstance : MeasurableSpace S)]
        fun p : Omega × S => squaredDistanceENN s p.2 by
      exact (measurable_squaredDistanceENN s).comp
        (@measurable_snd Omega S m (inferInstance : MeasurableSpace S))
      ).lintegral_kernel_prod_right'
  have hPair : Measurable[m.prod (inferInstance : MeasurableSpace S)]
      fun p : Omega × S => squaredDistanceENN s p.2 := by
    exact (measurable_squaredDistanceENN s).comp
      (@measurable_snd Omega S m (inferInstance : MeasurableSpace S))
  have hJoint : Measurable[mOmega, m.prod (inferInstance : MeasurableSpace S)]
      (fun omega : Omega => (omega, X omega)) :=
    (measurable_id'' hm).prodMk hX
  calc
    ∫⁻ omega in A, frechetRisk (kappa omega) s ∂mu =
        ∫⁻ omega in A, ∫⁻ x, squaredDistanceENN s x ∂kappa omega ∂mu := by
      apply setLIntegral_congr_fun (hm A hA)
      intro omega _
      exact frechetRisk_eq_lintegral (kappa omega) s
    _ = ∫⁻ omega in A, ∫⁻ x, squaredDistanceENN s x ∂kappa omega
          ∂mu.trim hm :=
      (setLIntegral_trim hm hPost hA).symm
    _ = ∫⁻ p in A ×ˢ (Set.univ : Set S), squaredDistanceENN s p.2
          ∂(mu.trim hm) ⊗ₘ kappa := by
      rw [Measure.setLIntegral_compProd hPair hA MeasurableSet.univ]
      simp
    _ = ∫⁻ p in A ×ˢ (Set.univ : Set S), squaredDistanceENN s p.2
          ∂@Measure.map Omega (Omega × S) mOmega
            (m.prod (inferInstance : MeasurableSpace S))
            (fun omega => (omega, X omega)) mu := by
      rw [← hkappa]
    _ = ∫⁻ omega in A, squaredDistanceENN s (X omega) ∂mu := by
      rw [@setLIntegral_map Omega (Omega × S) mOmega
        (m.prod (inferInstance : MeasurableSpace S)) mu
        (fun p => squaredDistanceENN s p.2)
        (fun omega => (omega, X omega))
        (A ×ˢ (Set.univ : Set S))
        (hA.prod MeasurableSet.univ) hPair hJoint]
      have hPreimage :
          (fun omega : Omega => (omega, X omega)) ⁻¹'
              (A ×ˢ (Set.univ : Set S)) = A := by
        ext omega
        simp
      rw [hPreimage]

/-- Posterior Frechet variance is measurable because separability replaces
the infimum over all centres by a countable infimum. -/
theorem measurable_posteriorFrechetVariance
    [TopologicalSpace.SeparableSpace S]
    (m : MeasurableSpace Omega)
    (kappa : Kernel[m, (inferInstance : MeasurableSpace S)] Omega S)
    [IsMarkovKernel kappa] :
    Measurable[m] fun omega => frechetVariance (kappa omega) := by
  have hRepresentation :
      (fun omega => frechetVariance (kappa omega)) =
        fun omega => ⨅ k : ℕ,
          frechetRisk (kappa omega) (TopologicalSpace.denseSeq S k) := by
    funext omega
    exact frechetVariance_eq_iInf_denseSeq (kappa omega)
  rw [hRepresentation]
  exact Measurable.iInf fun k =>
    measurable_posteriorFrechetRisk m kappa
      (TopologicalSpace.denseSeq S k)

omit [MeasurableSpace S] [Nonempty S] [OpensMeasurableSpace S] in
/-- Integrability of a real squared-distance variable is equivalent here to
finiteness of the nonnegative extended integral used by Frechet risk. -/
theorem lintegral_squaredDistanceENN_ne_top
    (mu : Measure[mOmega] Omega) (X : Omega → S) (s : S)
    (h : Integrable (fun omega => dist (X omega) s ^ 2) mu) :
    (∫⁻ omega, squaredDistanceENN s (X omega) ∂mu) ≠ ∞ := by
  have hMeas : AEMeasurable (fun omega => squaredDistanceENN s (X omega)) mu :=
    h.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hFinite : ∀ᵐ omega ∂mu, squaredDistanceENN s (X omega) ≠ ∞ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_ne_top
  apply (integrable_toReal_iff hMeas hFinite).mp
  convert h using 1
  funext omega
  simp [squaredDistanceENN]

omit [Nonempty S] in
/-- A second moment about one centre implies a second moment about every
centre.  This is the real-integrability counterpart of the root-risk
finiteness dichotomy. -/
theorem integrable_squaredDistance_of_reference
    (mu : Measure[mOmega] Omega) [IsFiniteMeasure mu]
    (X : Omega → S) (hX : Measurable[mOmega] X)
    (s0 : S)
    (hMoment : Integrable (fun omega => dist (X omega) s0 ^ 2) mu)
    (s : S) :
    Integrable (fun omega => dist (X omega) s ^ 2) mu := by
  have hMajorant : Integrable
      (fun omega => 2 * dist (X omega) s0 ^ 2 + 2 * dist s0 s ^ 2) mu := by
    exact (hMoment.const_mul 2).add (integrable_const (2 * dist s0 s ^ 2))
  apply hMajorant.mono'
  · exact ((measurable_dist_to s).comp hX).pow_const 2 |>.aestronglyMeasurable
  · filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hTriangle := dist_triangle (X omega) s0 s
    have hSquare : dist (X omega) s ^ 2 ≤
        (dist (X omega) s0 + dist s0 s) ^ 2 :=
      (sq_le_sq₀ dist_nonneg (add_nonneg dist_nonneg dist_nonneg)).2 hTriangle
    nlinarith [sq_nonneg (dist (X omega) s0 - dist s0 s)]

omit [Nonempty S] in
/-- Under a finite second moment, the real posterior risk at a fixed centre
is a version of the ordinary conditional expectation of squared distance. -/
theorem posteriorFrechetRisk_toReal_ae_eq_condExp
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (m : MeasurableSpace Omega) (hm : m ≤ mOmega)
    (X : Omega → S) (hX : Measurable[mOmega] X)
    (kappa : Kernel[m, (inferInstance : MeasurableSpace S)] Omega S)
    [IsMarkovKernel kappa]
    (hkappa : IsRegularConditionalLaw mu m hm X kappa)
    (s : S) (hMoment : Integrable (fun omega => dist (X omega) s ^ 2) mu) :
    (fun omega => (frechetRisk (kappa omega) s).toReal) =ᵐ[mu]
      mu[fun omega => dist (X omega) s ^ 2 | m] := by
  have hENNMeas : AEMeasurable
      (fun omega => squaredDistanceENN s (X omega)) mu := by
    exact (measurable_squaredDistanceENN s).comp_aemeasurable hX.aemeasurable
  have hENNFinite := lintegral_squaredDistanceENN_ne_top mu X s hMoment
  filter_upwards [posteriorFrechetRisk_ae_eq_condLExp
      mu m hm X hX kappa hkappa s,
    MeasureTheory.toReal_condLExp m hENNMeas hENNFinite]
    with omega hRisk hCond
  rw [hRisk, hCond]
  simp [squaredDistanceENN]

omit [Nonempty S] in
/-- The fixed-centre conditional-risk representation at every centre follows
from one reference-centre moment assumption. -/
theorem posteriorFrechetRisk_toReal_ae_eq_condExp_of_reference
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (m : MeasurableSpace Omega) (hm : m ≤ mOmega)
    (X : Omega → S) (hX : Measurable[mOmega] X)
    (kappa : Kernel[m, (inferInstance : MeasurableSpace S)] Omega S)
    [IsMarkovKernel kappa]
    (hkappa : IsRegularConditionalLaw mu m hm X kappa)
    (s0 : S)
    (hMoment : Integrable (fun omega => dist (X omega) s0 ^ 2) mu)
    (s : S) :
    (fun omega => (frechetRisk (kappa omega) s).toReal) =ᵐ[mu]
      mu[fun omega => dist (X omega) s ^ 2 | m] :=
  posteriorFrechetRisk_toReal_ae_eq_condExp mu m hm X hX kappa hkappa s
    (integrable_squaredDistance_of_reference mu X hX s0 hMoment s)

omit [Nonempty S] [OpensMeasurableSpace S] in
/-- Posterior variance is bounded by posterior risk at every chosen centre,
pointwise rather than merely almost surely. -/
theorem posteriorFrechetVariance_le_risk
    (m : MeasurableSpace Omega)
    (kappa : Kernel[m, (inferInstance : MeasurableSpace S)] Omega S)
    [IsMarkovKernel kappa] (s : S) (omega : Omega) :
    frechetVariance (kappa omega) ≤ frechetRisk (kappa omega) s :=
  frechetVariance_le (kappa omega) s

/-- Full finite-second-moment well-posedness.  Posterior risk at the reference
centre and posterior Frechet variance are finite almost surely, and their
real-valued forms are integrable. -/
theorem posteriorFrechet_finite_and_integrable
    [TopologicalSpace.SeparableSpace S]
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (m : MeasurableSpace Omega) (hm : m ≤ mOmega)
    (X : Omega → S) (hX : Measurable[mOmega] X)
    (kappa : Kernel[m, (inferInstance : MeasurableSpace S)] Omega S)
    [IsMarkovKernel kappa]
    (hkappa : IsRegularConditionalLaw mu m hm X kappa)
    (s0 : S)
    (hMoment : Integrable (fun omega => dist (X omega) s0 ^ 2) mu) :
    (∀ᵐ omega ∂mu, frechetRisk (kappa omega) s0 < ∞) ∧
      (∀ᵐ omega ∂mu, frechetVariance (kappa omega) < ∞) ∧
      Integrable (fun omega => (frechetRisk (kappa omega) s0).toReal) mu ∧
      Integrable (fun omega => (frechetVariance (kappa omega)).toReal) mu := by
  have hRiskMeasM := measurable_posteriorFrechetRisk m kappa s0
  have hRiskMeas : Measurable[mOmega]
      (fun omega => frechetRisk (kappa omega) s0) :=
    hRiskMeasM.mono hm le_rfl
  have hVarianceMeasM := measurable_posteriorFrechetVariance m kappa
  have hVarianceMeas : Measurable[mOmega]
      (fun omega => frechetVariance (kappa omega)) :=
    hVarianceMeasM.mono hm le_rfl
  have hENNFinite := lintegral_squaredDistanceENN_ne_top mu X s0 hMoment
  have hRiskAE := posteriorFrechetRisk_ae_eq_condLExp
    mu m hm X hX kappa hkappa s0
  have hRiskIntegral :
      (∫⁻ omega, frechetRisk (kappa omega) s0 ∂mu) ≠ ∞ := by
    rw [lintegral_congr_ae hRiskAE,
      MeasureTheory.lintegral_condLExp hm mu]
    exact hENNFinite
  have hVarianceIntegral :
      (∫⁻ omega, frechetVariance (kappa omega) ∂mu) ≠ ∞ := by
    apply ne_of_lt
    refine (lintegral_mono fun omega =>
      posteriorFrechetVariance_le_risk m kappa s0 omega).trans_lt ?_
    exact lt_top_iff_ne_top.2 hRiskIntegral
  refine ⟨ae_lt_top hRiskMeas hRiskIntegral,
    ae_lt_top hVarianceMeas hVarianceIntegral,
    integrable_toReal_of_lintegral_ne_top hRiskMeas.aemeasurable hRiskIntegral,
    integrable_toReal_of_lintegral_ne_top
      hVarianceMeas.aemeasurable hVarianceIntegral⟩

end PosteriorFrechetRisk

end

end SequentialLearning
