import SequentialLearning.MSEHierarchy
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Notation

/-!
# Conditional stochastic domination of a monotone discrepancy

This file formalises Proposition `tailorder`, including existence and
kernel-level uniqueness of real regular conditional laws, construction of the
joint conditional coupling, transfer to arbitrary selected marginal versions,
and iteration from adjacent to arbitrary later stages.  The formulation
preserves the important quantifier order: outside one null set, every tail
threshold is controlled simultaneously.
-/

namespace SequentialLearning

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal MeasureTheory ProbabilityTheory

noncomputable section

section ConditionalStochasticDomination

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- Usual stochastic order expressed through upper-tail probabilities.  The
first measure is the stochastically smaller one. -/
def TailStochasticLE (νSmall νLarge : Measure ℝ) : Prop :=
  ∀ t : ℝ, νSmall (Ioi t) ≤ νLarge (Ioi t)

/-- The order-support set for a coupling whose first coordinate is the older
discrepancy and whose second coordinate is the later discrepancy. -/
def decreasingPairSet : Set (ℝ × ℝ) :=
  {p | p.2 ≤ p.1}

theorem measurableSet_decreasingPairSet : MeasurableSet decreasingPairSet := by
  exact (isClosed_le continuous_snd continuous_fst).measurableSet

/-- A probability coupling concentrated on ordered pairs gives stochastic
domination of its second marginal by its first.  The same support statement
controls all thresholds, so there is no threshold-dependent exceptional set. -/
theorem tailStochasticLE_of_monotoneCoupling
    (π : Measure (ℝ × ℝ)) [IsProbabilityMeasure π]
    (hSupport : π decreasingPairSet = 1) :
    TailStochasticLE (π.map Prod.snd) (π.map Prod.fst) := by
  have hOrdered : ∀ᵐ p ∂π, p ∈ decreasingPairSet := by
    apply (ae_mem_iff_measure_eq
      measurableSet_decreasingPairSet.nullMeasurableSet).2
    simpa only [measure_univ] using hSupport
  intro t
  have hTailInclusion :
      (Prod.snd ⁻¹' Ioi t) ≤ᵐ[π] (Prod.fst ⁻¹' Ioi t) := by
    filter_upwards [hOrdered] with p hp hLater
    change p.2 ≤ p.1 at hp
    exact lt_of_lt_of_le hLater hp
  rw [Measure.map_apply measurable_snd measurableSet_Ioi,
    Measure.map_apply measurable_fst measurableSet_Ioi]
  exact measure_mono_ae hTailInclusion

/-- If an event holds almost surely, its conditional probability is one
almost surely. -/
theorem condProbability_eq_one_of_ae
    (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ m0) (A : Set Ω)
    (hA : ∀ᵐ ω ∂μ, ω ∈ A) :
    μ⟦A | m⟧ =ᵐ[μ] fun _ => (1 : ℝ) := by
  have hIndicator :
      A.indicator (fun _ => (1 : ℝ)) =ᵐ[μ] fun _ => (1 : ℝ) := by
    filter_upwards [hA] with ω hω
    simp [hω]
  exact (condExp_congr_ae hIndicator).trans
    (Filter.Eventually.of_forall fun ω => by
      rw [condExp_const hm])

/-- The part of the regular-conditional-distribution interface used here.  A
kernel from the conditioning measurable space gives the conditional law of
the pair `(ROld, RNew)` when its value on every measurable set agrees almost
surely with the corresponding conditional probability. -/
def IsRegularConditionalPairLaw
    (μ : Measure[m0] Ω) (m : MeasurableSpace Ω)
    (ROld RNew : Ω → ℝ)
    (π : Kernel[m, (inferInstance : MeasurableSpace (ℝ × ℝ))]
      Ω (ℝ × ℝ)) : Prop :=
  ∀ s : Set (ℝ × ℝ), MeasurableSet s →
    (fun ω => (π ω s).toReal) =ᵐ[μ]
      μ⟦{ω | (ROld ω, RNew ω) ∈ s} | m⟧

/-- A real-valued regular conditional law, expressed through agreement with
conditional probabilities on every Borel set.  The exceptional null set may
initially depend on the set; the uniqueness theorem below collapses these
setwise statements to kernel equality outside one null set. -/
def IsRegularConditionalRealLaw
    (μ : Measure[m0] Ω) (m : MeasurableSpace Ω)
    (R : Ω → ℝ)
    (ν : Kernel[m, (inferInstance : MeasurableSpace ℝ)] Ω ℝ) : Prop :=
  ∀ s : Set ℝ, MeasurableSet s →
    (fun ω => (ν ω s).toReal) =ᵐ[μ]
      μ⟦{ω | R ω ∈ s} | m⟧

/-- The first marginal of a joint regular conditional law is a regular
conditional law of the first coordinate. -/
theorem IsRegularConditionalPairLaw.fst
    (mu : Measure[m0] Ω) (m : MeasurableSpace Ω)
    (ROld RNew : Ω → ℝ)
    (pi : Kernel[m, (inferInstance : MeasurableSpace (ℝ × ℝ))]
      Ω (ℝ × ℝ))
    (hpi : IsRegularConditionalPairLaw mu m ROld RNew pi) :
    IsRegularConditionalRealLaw mu m ROld (Kernel.fst pi) := by
  intro s hs
  have h := hpi (Prod.fst ⁻¹' s) (measurable_fst hs)
  filter_upwards [h] with omega homega
  rw [Kernel.fst_apply' pi omega hs]
  exact homega

/-- The second marginal of a joint regular conditional law is a regular
conditional law of the second coordinate. -/
theorem IsRegularConditionalPairLaw.snd
    (mu : Measure[m0] Ω) (m : MeasurableSpace Ω)
    (ROld RNew : Ω → ℝ)
    (pi : Kernel[m, (inferInstance : MeasurableSpace (ℝ × ℝ))]
      Ω (ℝ × ℝ))
    (hpi : IsRegularConditionalPairLaw mu m ROld RNew pi) :
    IsRegularConditionalRealLaw mu m RNew (Kernel.snd pi) := by
  intro s hs
  have h := hpi (Prod.snd ⁻¹' s) (measurable_snd hs)
  filter_upwards [h] with omega homega
  rw [Kernel.snd_apply' pi omega hs]
  exact homega

/-- Any two real-valued regular conditional laws are equal as kernels outside
one common null set.  Countable generation of the Borel sigma-algebra on
`ℝ` is the essential ingredient: equality is first combined on rational
half-lines and then extended to every Borel set. -/
theorem regularConditionalRealLaw_ae_eq
    (mu : Measure[m0] Ω) (m : MeasurableSpace Ω)
    (R : Ω → ℝ)
    (nu eta : Kernel[m, (inferInstance : MeasurableSpace ℝ)] Ω ℝ)
    [IsMarkovKernel nu] [IsMarkovKernel eta]
    (hnu : IsRegularConditionalRealLaw mu m R nu)
    (heta : IsRegularConditionalRealLaw mu m R eta) :
    nu =ᵐ[mu] eta := by
  suffices hSets : ∀ᵐ omega ∂mu, ∀ {s : Set ℝ}, MeasurableSet s →
      nu omega s = eta omega s by
    filter_upwards [hSets] with omega homega
    ext s hs
    exact homega hs
  refine @MeasurableSpace.ae_induction_on_inter
    ℝ Ω m0 mu
    (fun omega s => nu omega s = eta omega s)
    (⋃ q : ℚ, {Iic (q : ℝ)}) (borel ℝ)
    Real.borel_eq_generateFrom_Iic_rat Real.isPiSystem_Iic_rat
    ?_ ?_ ?_ ?_
  · simp
  · simp only [iUnion_singleton_eq_range, mem_range, forall_exists_index,
      forall_apply_eq_imp_iff]
    exact ae_all_iff.2 fun q => by
      have hnuq := hnu (Iic (q : ℝ)) measurableSet_Iic
      have hetaQ := heta (Iic (q : ℝ)) measurableSet_Iic
      filter_upwards [hnuq, hetaQ] with omega hnuOmega hetaOmega
      apply (ENNReal.toReal_eq_toReal_iff'
        (measure_ne_top (nu omega) _) (measure_ne_top (eta omega) _)).mp
      exact hnuOmega.trans hetaOmega.symm
  · filter_upwards with omega s hs heq
    rw [measure_compl hs (measure_ne_top _ _),
      measure_compl hs (measure_ne_top _ _), heq,
      measure_univ, measure_univ]
  · refine ae_of_all mu (fun omega f hdisjoint hf heq => ?_)
    rw [measure_iUnion hdisjoint hf, measure_iUnion hdisjoint hf]
    exact tsum_congr heq

/-- Every measurable real random variable has a regular conditional law given
an arbitrary sub-sigma-algebra.  The construction conditions on the identity
map into the sample type equipped with the smaller measurable space; only the
real target needs to be standard Borel. -/
theorem exists_regularConditionalRealLaw
    (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ m0)
    (R : Ω → ℝ) (hR : Measurable[m0] R) :
    ∃ ν : Kernel[m, (inferInstance : MeasurableSpace ℝ)] Ω ℝ,
      IsMarkovKernel ν ∧ IsRegularConditionalRealLaw μ m R ν := by
  let ν : Kernel[m, (inferInstance : MeasurableSpace ℝ)] Ω ℝ :=
    condDistrib R id μ
  have hId : @Measurable Ω Ω m0 m id := measurable_id'' hm
  refine ⟨ν, inferInstance, ?_⟩
  intro s hs
  change (fun ω => (ν ω s).toReal) =ᵐ[μ] μ⟦R ⁻¹' s | m⟧
  have hConditional := condDistrib_ae_eq_condExp
    (μ := μ) (X := id) (Y := R) hId hR hs
  simpa only [ν, id_eq, MeasurableSpace.comap_id,
    measureReal_def] using hConditional

/-- A regular conditional pair law inherits concentration on the monotone
support from an almost-sure order of the original pair.  The hypothesis
`hConditionalSupport` is precisely the defining regular-conditional-law
identity evaluated at the closed order-support set. -/
theorem conditionalPairLaw_concentrated_on_decreasingSet
    (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ m0)
    (ROld RNew : Ω → ℝ)
    (π : Kernel[m, (inferInstance : MeasurableSpace (ℝ × ℝ))]
      Ω (ℝ × ℝ)) [IsMarkovKernel π]
    (hMonotone : ∀ᵐ ω ∂μ, RNew ω ≤ ROld ω)
    (hπ : IsRegularConditionalPairLaw μ m ROld RNew π) :
    ∀ᵐ ω ∂μ, π ω decreasingPairSet = 1 := by
  have hConditionalSupport :
      (fun ω => (π ω decreasingPairSet).toReal) =ᵐ[μ]
        μ⟦{ω | RNew ω ≤ ROld ω} | m⟧ := by
    simpa only [decreasingPairSet, mem_ofPred_eq] using
      hπ decreasingPairSet measurableSet_decreasingPairSet
  have hConditionalOne := condProbability_eq_one_of_ae μ m hm
    {ω | RNew ω ≤ ROld ω} hMonotone
  filter_upwards [hConditionalSupport, hConditionalOne] with
    ω hSupportω hOneω
  exact (ENNReal.toReal_eq_one_iff _).mp (hSupportω.trans hOneω)

/-- Conditional stochastic domination from a monotone discrepancy pair and a
regular conditional coupling.  For almost every conditioning state, the
later conditional law is below the earlier conditional law at every real
threshold simultaneously. -/
theorem conditional_stochastic_domination_of_discrepancy
    (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ m0)
    (ROld RNew : Ω → ℝ)
    (π : Kernel[m, (inferInstance : MeasurableSpace (ℝ × ℝ))]
      Ω (ℝ × ℝ)) [IsMarkovKernel π]
    (hMonotone : ∀ᵐ ω ∂μ, RNew ω ≤ ROld ω)
    (hπ : IsRegularConditionalPairLaw μ m ROld RNew π) :
    ∀ᵐ ω ∂μ,
      TailStochasticLE ((π ω).map Prod.snd) ((π ω).map Prod.fst) := by
  have hSupport := conditionalPairLaw_concentrated_on_decreasingSet
    μ m hm ROld RNew π hMonotone hπ
  filter_upwards [hSupport] with ω hSupportω
  exact tailStochasticLE_of_monotoneCoupling (π ω) hSupportω

/-- Expanded tail form of conditional stochastic domination.  The universal
threshold quantifier is inside the almost-sure quantifier. -/
theorem conditional_tail_order_simultaneously
    (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ m0)
    (ROld RNew : Ω → ℝ)
    (π : Kernel[m, (inferInstance : MeasurableSpace (ℝ × ℝ))]
      Ω (ℝ × ℝ)) [IsMarkovKernel π]
    (hMonotone : ∀ᵐ ω ∂μ, RNew ω ≤ ROld ω)
    (hπ : IsRegularConditionalPairLaw μ m ROld RNew π) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ,
      (π ω).map Prod.snd (Ioi t) ≤ (π ω).map Prod.fst (Ioi t) := by
  exact conditional_stochastic_domination_of_discrepancy
    μ m hm ROld RNew π hMonotone hπ

/-- Transfer the domination statement from the two marginals of the
conditional coupling to separately selected versions of the two conditional
laws.  Kernel-level almost-sure equality is what preserves the common null set
for all thresholds. -/
theorem conditional_stochastic_domination_for_versions
    (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ m0)
    (ROld RNew : Ω → ℝ)
    (π : Kernel[m, (inferInstance : MeasurableSpace (ℝ × ℝ))]
      Ω (ℝ × ℝ)) [IsMarkovKernel π]
    (νOld νNew : Kernel[m, (inferInstance : MeasurableSpace ℝ)] Ω ℝ)
    (hMonotone : ∀ᵐ ω ∂μ, RNew ω ≤ ROld ω)
    (hπ : IsRegularConditionalPairLaw μ m ROld RNew π)
    (hOldVersion :
      ∀ᵐ ω ∂μ, νOld ω = (π ω).map Prod.fst)
    (hNewVersion :
      ∀ᵐ ω ∂μ, νNew ω = (π ω).map Prod.snd) :
    ∀ᵐ ω ∂μ, TailStochasticLE (νNew ω) (νOld ω) := by
  have hMarginalOrder := conditional_stochastic_domination_of_discrepancy
    μ m hm ROld RNew π hMonotone hπ
  filter_upwards [hMarginalOrder, hOldVersion, hNewVersion] with
    ω hOrderω hOldω hNewω
  simpa only [hOldω, hNewω] using hOrderω

/-- The arbitrary-version theorem for a supplied joint regular conditional
law.  The marginal-version equalities are consequences, not hypotheses:
real-valued RCD uniqueness supplies both equalities on common full-measure
sets. -/
theorem conditional_stochastic_domination_for_regularConditionalLaws
    (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ m0)
    (ROld RNew : Ω → ℝ)
    (π : Kernel[m, (inferInstance : MeasurableSpace (ℝ × ℝ))]
      Ω (ℝ × ℝ)) [IsMarkovKernel π]
    (νOld νNew : Kernel[m, (inferInstance : MeasurableSpace ℝ)] Ω ℝ)
    [IsMarkovKernel νOld] [IsMarkovKernel νNew]
    (hMonotone : ∀ᵐ ω ∂μ, RNew ω ≤ ROld ω)
    (hπ : IsRegularConditionalPairLaw μ m ROld RNew π)
    (hOld : IsRegularConditionalRealLaw μ m ROld νOld)
    (hNew : IsRegularConditionalRealLaw μ m RNew νNew) :
    ∀ᵐ ω ∂μ, TailStochasticLE (νNew ω) (νOld ω) := by
  have hOldKernel : νOld =ᵐ[μ] Kernel.fst π :=
    regularConditionalRealLaw_ae_eq μ m ROld νOld (Kernel.fst π)
      hOld (hπ.fst μ m ROld RNew π)
  have hNewKernel : νNew =ᵐ[μ] Kernel.snd π :=
    regularConditionalRealLaw_ae_eq μ m RNew νNew (Kernel.snd π)
      hNew (hπ.snd μ m ROld RNew π)
  have hOldVersion : ∀ᵐ ω ∂μ, νOld ω = (π ω).map Prod.fst := by
    filter_upwards [hOldKernel] with ω hω
    simpa only [Kernel.fst_apply] using hω
  have hNewVersion : ∀ᵐ ω ∂μ, νNew ω = (π ω).map Prod.snd := by
    filter_upwards [hNewKernel] with ω hω
    simpa only [Kernel.snd_apply] using hω
  exact conditional_stochastic_domination_for_versions
    μ m hm ROld RNew π νOld νNew hMonotone hπ
      hOldVersion hNewVersion

/-- Existence of a joint regular conditional law for a real-valued pair.
Keeping this property explicit gives the theorem at the manuscript's natural
level of generality without imposing a standard-Borel structure on the sample
space itself. -/
def HasRegularConditionalPairLaw
    (μ : Measure[m0] Ω) (m : MeasurableSpace Ω)
    (ROld RNew : Ω → ℝ) : Prop :=
  ∃ π : Kernel[m, (inferInstance : MeasurableSpace (ℝ × ℝ))]
      Ω (ℝ × ℝ),
    IsMarkovKernel π ∧ IsRegularConditionalPairLaw μ m ROld RNew π

/-- Complete two-stage theorem for arbitrary selected versions of the two
regular conditional laws.  The only existence input is a joint RCD of the
pair, exactly as used in the manuscript proof. -/
theorem conditional_stochastic_domination_of_regularConditionalLaws
    (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ m0)
    (ROld RNew : Ω → ℝ)
    (νOld νNew : Kernel[m, (inferInstance : MeasurableSpace ℝ)] Ω ℝ)
    [IsMarkovKernel νOld] [IsMarkovKernel νNew]
    (hMonotone : ∀ᵐ ω ∂μ, RNew ω ≤ ROld ω)
    (hOld : IsRegularConditionalRealLaw μ m ROld νOld)
    (hNew : IsRegularConditionalRealLaw μ m RNew νNew)
    (hPair : HasRegularConditionalPairLaw μ m ROld RNew) :
    ∀ᵐ ω ∂μ, TailStochasticLE (νNew ω) (νOld ω) := by
  rcases hPair with ⟨π, hπMarkov, hπ⟩
  let _ : IsMarkovKernel π := hπMarkov
  exact conditional_stochastic_domination_for_regularConditionalLaws
    μ m hm ROld RNew π νOld νNew hMonotone hπ hOld hNew

/-- A measurable real pair has a joint regular conditional law given any
sub-sigma-algebra.  The conditioning variable is the identity from the
ambient measurable space to the same type equipped with `m`; only the target
`ℝ × ℝ`, not the sample space, needs to be standard Borel. -/
theorem hasRegularConditionalPairLaw_of_measurable
    (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ m0)
    (ROld RNew : Ω → ℝ)
    (hROld : Measurable[m0] ROld)
    (hRNew : Measurable[m0] RNew) :
    HasRegularConditionalPairLaw μ m ROld RNew := by
  let pair : Ω → ℝ × ℝ := fun ω => (ROld ω, RNew ω)
  let π : Kernel[m, (inferInstance : MeasurableSpace (ℝ × ℝ))]
      Ω (ℝ × ℝ) := condDistrib pair id μ
  have hPairMeasurable : Measurable[m0] (fun ω => (ROld ω, RNew ω)) :=
    hROld.prodMk hRNew
  have hId : @Measurable Ω Ω m0 m id := measurable_id'' hm
  refine ⟨π, inferInstance, ?_⟩
  intro s hs
  change (fun ω => (π ω s).toReal) =ᵐ[μ] μ⟦pair ⁻¹' s | m⟧
  have hConditional := condDistrib_ae_eq_condExp
    (μ := μ) (X := id) (Y := pair) hId
      (by simpa only [pair] using hPairMeasurable) hs
  simpa only [π, pair, id_eq, MeasurableSpace.comap_id,
    measureReal_def] using hConditional

/-- Fully constructed two-stage version: measurability of the two real
discrepancies supplies their joint RCD automatically. -/
theorem conditional_stochastic_domination_of_measurable_discrepancy
    (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ m0)
    (ROld RNew : Ω → ℝ)
    (hROld : Measurable[m0] ROld)
    (hRNew : Measurable[m0] RNew)
    (νOld νNew : Kernel[m, (inferInstance : MeasurableSpace ℝ)] Ω ℝ)
    [IsMarkovKernel νOld] [IsMarkovKernel νNew]
    (hMonotone : ∀ᵐ ω ∂μ, RNew ω ≤ ROld ω)
    (hOld : IsRegularConditionalRealLaw μ m ROld νOld)
    (hNew : IsRegularConditionalRealLaw μ m RNew νNew) :
    ∀ᵐ ω ∂μ, TailStochasticLE (νNew ω) (νOld ω) := by
  exact conditional_stochastic_domination_of_regularConditionalLaws
    μ m hm ROld RNew νOld νNew hMonotone hOld hNew
      (hasRegularConditionalPairLaw_of_measurable
        μ m hm ROld RNew hROld hRNew)

/-- Sequence form of the complete theorem.  Adjacent almost-sure decreases
are first iterated to any pair of stages; the arbitrary selected RCD versions
are then compared using the jointly constructed conditional coupling. -/
theorem conditional_stochastic_domination_sequence
    (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ m0)
    (R : ℕ → Ω → ℝ)
    (ν : ℕ → Kernel[m, (inferInstance : MeasurableSpace ℝ)] Ω ℝ)
    (hνMarkov : ∀ n, IsMarkovKernel (ν n))
    (hR : ∀ n, Measurable[m0] (R n))
    (hν : ∀ n, IsRegularConditionalRealLaw μ m (R n) (ν n))
    (hStep : ∀ n, R (n + 1) ≤ᵐ[μ] R n) :
    ∀ {n k : ℕ}, n ≤ k →
      ∀ᵐ ω ∂μ, TailStochasticLE (ν k ω) (ν n ω) := by
  have hPairwise : ∀ {n k : ℕ}, n ≤ k → R k ≤ᵐ[μ] R n := by
    intro n k hnk
    induction k, hnk using Nat.le_induction with
    | base => exact Filter.EventuallyLE.rfl
    | @succ k hnk ih => exact (hStep k).trans ih
  intro n k hnk
  let _ : IsMarkovKernel (ν n) := hνMarkov n
  let _ : IsMarkovKernel (ν k) := hνMarkov k
  exact conditional_stochastic_domination_of_measurable_discrepancy
    μ m hm (R n) (R k) (hR n) (hR k) (ν n) (ν k)
      (hPairwise hnk) (hν n) (hν k)

end ConditionalStochasticDomination

end

end SequentialLearning
