import SequentialLearning.PseudometricCompletion
import Mathlib.Probability.Kernel.Composition.Lemmas

/-!
# Posterior-displacement kernel infrastructure

This file begins Result 16(ii)--(iii).  It transports regular conditional
laws to the completed metric quotient and supplies the canonical coupling
bound for a conditional joint law.
-/

namespace SequentialLearning

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal MeasureTheory ProbabilityTheory Topology

noncomputable section

section KernelProbabilityLaws

variable {Omega T : Type*} {m : MeasurableSpace Omega}
  [MeasurableSpace T]

/-- Regard the value of a Markov kernel as a bundled probability measure. -/
def kernelProbabilityLaw
    (kappa : Kernel[m, (inferInstance : MeasurableSpace T)] Omega T)
    [IsMarkovKernel kappa] (omega : Omega) : ProbabilityMeasure T :=
  ⟨kappa omega, IsMarkovKernel.isProbabilityMeasure omega⟩

/-- A Markov kernel is a measurable probability-measure-valued map for the
Giry measurable structure. -/
theorem measurable_kernelProbabilityLaw
    (kappa : Kernel[m, (inferInstance : MeasurableSpace T)] Omega T)
    [IsMarkovKernel kappa] :
    Measurable[m] (kernelProbabilityLaw kappa) := by
  exact kappa.measurable.subtype_mk

end KernelProbabilityLaws

section RegularConditionalTransport

variable {Omega S T : Type*} {mOmega : MeasurableSpace Omega}
  [MeasurableSpace S] [MeasurableSpace T]

/-- A measurable image of a regular conditional law is a regular
conditional law of the corresponding image random element. -/
theorem regularConditionalLaw_map
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (m : MeasurableSpace Omega) (hm : m ≤ mOmega)
    (X : Omega → S) (hX : Measurable[mOmega] X)
    (kappa : Kernel[m, (inferInstance : MeasurableSpace S)] Omega S)
    [IsMarkovKernel kappa]
    (hkappa : IsRegularConditionalLaw mu m hm X kappa)
    (f : S → T) (hf : Measurable f) :
    IsRegularConditionalLaw mu m hm (f ∘ X) (kappa.map f) := by
  rw [IsRegularConditionalLaw, Measure.compProd_map hf, hkappa]
  have hPair : Measurable[mOmega, m.prod (inferInstance : MeasurableSpace S)]
      (fun omega : Omega => (omega, X omega)) :=
    (measurable_id'' hm).prodMk hX
  rw [Measure.map_map (measurable_id.prodMap hf) hPair]
  congr 1

/-- Integrating a nonnegative measurable function against an RCD gives a
version of its conditional Lebesgue expectation.  This general form is used
for the squared distance of a conditional joint law. -/
theorem kernelLIntegral_ae_eq_condLExp
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (m : MeasurableSpace Omega) (hm : m ≤ mOmega)
    (X : Omega → S) (hX : Measurable[mOmega] X)
    (kappa : Kernel[m, (inferInstance : MeasurableSpace S)] Omega S)
    [IsMarkovKernel kappa]
    (hkappa : IsRegularConditionalLaw mu m hm X kappa)
    (f : S → ENNReal) (hf : Measurable f) :
    (fun omega => ∫⁻ x, f x ∂kappa omega) =ᵐ[mu]
      mu⁻[fun omega => f (X omega) | m] := by
  have hPost : Measurable[m] fun omega => ∫⁻ x, f x ∂kappa omega := by
    exact (show Measurable[m.prod (inferInstance : MeasurableSpace S)]
        fun p : Omega × S => f p.2 by
      exact hf.comp
        (@measurable_snd Omega S m (inferInstance : MeasurableSpace S))
      ).lintegral_kernel_prod_right'
  have hPair : Measurable[m.prod (inferInstance : MeasurableSpace S)]
      fun p : Omega × S => f p.2 := by
    exact hf.comp
      (@measurable_snd Omega S m (inferInstance : MeasurableSpace S))
  have hJoint : Measurable[mOmega, m.prod (inferInstance : MeasurableSpace S)]
      (fun omega : Omega => (omega, X omega)) :=
    (measurable_id'' hm).prodMk hX
  apply MeasureTheory.ae_eq_condLExp hm mu
    (fun omega => f (X omega)) hPost
  intro A hA
  calc
    ∫⁻ omega in A, ∫⁻ x, f x ∂kappa omega ∂mu =
        ∫⁻ omega in A, ∫⁻ x, f x ∂kappa omega ∂mu.trim hm :=
      (setLIntegral_trim hm hPost hA).symm
    _ = ∫⁻ p in A ×ˢ (Set.univ : Set S), f p.2
          ∂(mu.trim hm) ⊗ₘ kappa := by
      rw [Measure.setLIntegral_compProd hPair hA MeasurableSet.univ]
      simp
    _ = ∫⁻ p in A ×ˢ (Set.univ : Set S), f p.2
          ∂@Measure.map Omega (Omega × S) mOmega
            (m.prod (inferInstance : MeasurableSpace S))
            (fun omega => (omega, X omega)) mu := by
      rw [← hkappa]
    _ = ∫⁻ omega in A, f (X omega) ∂mu := by
      rw [@setLIntegral_map Omega (Omega × S) mOmega
        (m.prod (inferInstance : MeasurableSpace S)) mu
        (fun p => f p.2) (fun omega => (omega, X omega))
        (A ×ˢ (Set.univ : Set S))
        (hA.prod MeasurableSet.univ) hPair hJoint]
      have hPreimage :
          (fun omega : Omega => (omega, X omega)) ⁻¹'
              (A ×ˢ (Set.univ : Set S)) = A := by
        ext omega
        simp
      rw [hPreimage]

end RegularConditionalTransport

section CompletedConditionalLaw

variable {Omega S : Type*} {mOmega : MeasurableSpace Omega}
  [PseudoMetricSpace S] [MeasurableSpace S] [Nonempty S]
  [OpensMeasurableSpace S] [TopologicalSpace.SeparableSpace S]

/-- Push a kernel pointwise to the completed metric quotient. -/
def completedKernel
    {m : MeasurableSpace Omega}
    (kappa : Kernel[m, (inferInstance : MeasurableSpace S)] Omega S) :
    Kernel[m, (inferInstance : MeasurableSpace (PseudometricCompletion S))]
      Omega (PseudometricCompletion S) :=
  kappa.map completionEmbedding

instance completedKernel.instIsMarkovKernel
    {m : MeasurableSpace Omega}
    (kappa : Kernel[m, (inferInstance : MeasurableSpace S)] Omega S)
    [IsMarkovKernel kappa] : IsMarkovKernel (completedKernel kappa) :=
  Kernel.IsMarkovKernel.map kappa measurable_completionEmbedding

/-- Result 16(ii), kernel form: pushforward preserves the RCD property. -/
theorem regularConditionalLaw_completedKernel
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (m : MeasurableSpace Omega) (hm : m ≤ mOmega)
    (X : Omega → S) (hX : Measurable[mOmega] X)
    (kappa : Kernel[m, (inferInstance : MeasurableSpace S)] Omega S)
    [IsMarkovKernel kappa]
    (hkappa : IsRegularConditionalLaw mu m hm X kappa) :
    IsRegularConditionalLaw mu m hm
      (completionEmbedding ∘ X) (completedKernel kappa) :=
  regularConditionalLaw_map mu m hm X hX kappa hkappa
    completionEmbedding measurable_completionEmbedding

/-- Any two completed-quotient versions of the same regular conditional law
agree outside one common null set.  Countable generation is required only for
the Polish completed target, not for the original (possibly finer) measurable
pseudometric space. -/
theorem completedKernel_ae_eq
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (m : MeasurableSpace Omega) (hm : m ≤ mOmega)
    (X : Omega → S) (hX : Measurable[mOmega] X)
    (kappa eta : Kernel[m, (inferInstance : MeasurableSpace S)] Omega S)
    [IsMarkovKernel kappa] [IsMarkovKernel eta]
    (hkappa : IsRegularConditionalLaw mu m hm X kappa)
    (heta : IsRegularConditionalLaw mu m hm X eta) :
    completedKernel kappa =ᵐ[mu] completedKernel eta := by
  exact regularConditionalLaw_ae_eq mu m hm
    (completionEmbedding ∘ X) (completedKernel kappa) (completedKernel eta)
    (regularConditionalLaw_completedKernel
      mu m hm X hX kappa hkappa)
    (regularConditionalLaw_completedKernel
      mu m hm X hX eta heta)

/-- Pointwise, the completed kernel law is exactly `completedLaw` applied to
the original kernel law. -/
theorem kernelProbabilityLaw_completedKernel
    {m : MeasurableSpace Omega}
    (kappa : Kernel[m, (inferInstance : MeasurableSpace S)] Omega S)
    [IsMarkovKernel kappa] (omega : Omega) :
    kernelProbabilityLaw (completedKernel kappa) omega =
      completedLaw (kernelProbabilityLaw kappa omega) := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [kernelProbabilityLaw, completedKernel, completedLaw,
    Kernel.map_apply _ measurable_completionEmbedding]
  change Measure.map completionEmbedding (kappa omega) =
    Measure.map completionEmbedding (kappa omega)
  rfl

/-- Fréchet variance of a conditional law is unchanged by completion,
pointwise for the chosen kernel version. -/
theorem frechetVariance_completedKernel
    {m : MeasurableSpace Omega}
    (kappa : Kernel[m, (inferInstance : MeasurableSpace S)] Omega S)
    [IsMarkovKernel kappa] (omega : Omega) :
    frechetVariance ((completedKernel kappa) omega) =
      frechetVariance (kappa omega) := by
  have h := congrArg
    (fun p : ProbabilityMeasure (PseudometricCompletion S) =>
      frechetVariance p.toMeasure)
    (kernelProbabilityLaw_completedKernel kappa omega)
  rw [frechetVariance_completedLaw] at h
  simpa [kernelProbabilityLaw] using h

end CompletedConditionalLaw

section JointCoupling

variable {Omega S : Type*} {m : MeasurableSpace Omega}
  [PseudoMetricSpace S] [MeasurableSpace S] [Nonempty S]
  [OpensMeasurableSpace S] [TopologicalSpace.SeparableSpace S]

/-- A joint Markov kernel gives a coupling of its two marginal laws at every
conditioning state. -/
def jointKernelCoupling
    (rho : Kernel[m, (inferInstance : MeasurableSpace (S × S))] Omega (S × S))
    [IsMarkovKernel rho] (omega : Omega) :
    TransportCoupling
      (kernelProbabilityLaw (Kernel.fst rho) omega)
      (kernelProbabilityLaw (Kernel.snd rho) omega) where
  law := kernelProbabilityLaw rho omega
  fst_eq := by
    apply ProbabilityMeasure.toMeasure_injective
    simp only [kernelProbabilityLaw]
    exact (Kernel.fst_apply rho omega).symm
  snd_eq := by
    apply ProbabilityMeasure.toMeasure_injective
    simp only [kernelProbabilityLaw]
    exact (Kernel.snd_apply rho omega).symm

/-- The completed image of the conditional joint law is the canonical
coupling used to bound posterior displacement. -/
def completedJointKernelCoupling
    (rho : Kernel[m, (inferInstance : MeasurableSpace (S × S))] Omega (S × S))
    [IsMarkovKernel rho] (omega : Omega) :
    TransportCoupling
      (completedLaw (kernelProbabilityLaw (Kernel.fst rho) omega))
      (completedLaw (kernelProbabilityLaw (Kernel.snd rho) omega)) :=
  (jointKernelCoupling rho omega).map
    completionEmbedding completionEmbedding
    measurable_completionEmbedding measurable_completionEmbedding

/-- The canonical completed joint coupling has exactly the original
pseudometric transport cost. -/
theorem transportL2Cost_completedJointKernelCoupling
    (rho : Kernel[m, (inferInstance : MeasurableSpace (S × S))] Omega (S × S))
    [IsMarkovKernel rho] (omega : Omega) :
    transportL2Cost (completedJointKernelCoupling rho omega) =
      transportL2Cost (jointKernelCoupling rho omega) := by
  simp only [completedJointKernelCoupling, transportL2Cost,
    TransportCoupling.map, ProbabilityMeasure.toMeasure_map]
  rw [eLpNorm_map_measure]
  · apply eLpNorm_congr_ae
    filter_upwards with xy
    simp
  · exact (measurable_fst.dist measurable_snd).aestronglyMeasurable
  · exact (measurable_completionEmbedding.prodMap
      measurable_completionEmbedding).aemeasurable

/-- The posterior Wasserstein displacement, bundled as an extended
nonnegative random variable before its a.s.-finite real version is taken. -/
def posteriorDisplacementENN
    (rho : Kernel[m, (inferInstance : MeasurableSpace (S × S))] Omega (S × S))
    [IsMarkovKernel rho] (omega : Omega) : ENNReal :=
  wasserstein2
    (completedLaw (kernelProbabilityLaw (Kernel.fst rho) omega))
    (completedLaw (kernelProbabilityLaw (Kernel.snd rho) omega))

/-- Real-valued posterior displacement.  Under the moment hypotheses below,
the extended value is finite almost surely, so this loses no information. -/
def posteriorDisplacement
    (rho : Kernel[m, (inferInstance : MeasurableSpace (S × S))] Omega (S × S))
    [IsMarkovKernel rho] (omega : Omega) : ℝ :=
  (posteriorDisplacementENN rho omega).toReal

/-- Squared distance on a pair, in the nonnegative extended-real form used
by conditional Lebesgue expectation. -/
def pairSquaredDistanceENN (xy : S × S) : ENNReal :=
  ENNReal.ofReal (dist xy.1 xy.2 ^ 2)

theorem measurable_pairSquaredDistanceENN :
    Measurable (pairSquaredDistanceENN : S × S → ENNReal) := by
  exact ((measurable_fst.dist measurable_snd).pow_const 2).ennreal_ofReal

/-- Pointwise coupling bound underlying Result 16(iii). -/
theorem posteriorDisplacementENN_sq_le
    (rho : Kernel[m, (inferInstance : MeasurableSpace (S × S))] Omega (S × S))
    [IsMarkovKernel rho] (omega : Omega) :
    posteriorDisplacementENN rho omega ^ 2 ≤
      ∫⁻ xy : S × S, ENNReal.ofReal (dist xy.1 xy.2 ^ 2) ∂rho omega := by
  let pi := completedJointKernelCoupling rho omega
  have hW : posteriorDisplacementENN rho omega ≤ transportL2Cost pi :=
    wasserstein2_le_transportL2Cost pi
  have hSq := pow_le_pow_left₀ bot_le hW 2
  calc
    posteriorDisplacementENN rho omega ^ 2 ≤
        transportL2Cost pi ^ 2 := hSq
    _ = transportL2Cost (jointKernelCoupling rho omega) ^ 2 := by
      rw [show transportL2Cost pi =
          transportL2Cost (jointKernelCoupling rho omega) by
        exact transportL2Cost_completedJointKernelCoupling rho omega]
    _ = ∫⁻ xy : S × S,
        ENNReal.ofReal (dist xy.1 xy.2 ^ 2) ∂rho omega := by
      rw [transportL2Cost_sq_eq_lintegral]
      rfl

/-- Result 15(iii) applied to the two completed conditional marginals.  This
is the metric input expected by the deterministic Result 17 module. -/
theorem posterior_root_variance_bound_from_jointKernel
    {mOmega : MeasurableSpace Omega}
    (rho : Kernel[m, (inferInstance : MeasurableSpace (S × S))] Omega (S × S))
    [IsMarkovKernel rho]
    (muOmega : Measure[mOmega] Omega)
    (hFst : ∀ᵐ omega ∂muOmega,
      HasFiniteSecondMoment ((Kernel.fst rho) omega))
    (hSnd : ∀ᵐ omega ∂muOmega,
      HasFiniteSecondMoment ((Kernel.snd rho) omega)) :
    ∀ᵐ omega ∂muOmega,
      |Real.sqrt (frechetVariance ((Kernel.snd rho) omega)).toReal -
          Real.sqrt (frechetVariance ((Kernel.fst rho) omega)).toReal| ≤
        (posteriorDisplacementENN rho omega).toReal := by
  filter_upwards [hFst, hSnd] with omega hFstOmega hSndOmega
  let mu := kernelProbabilityLaw (Kernel.fst rho) omega
  let nu := kernelProbabilityLaw (Kernel.snd rho) omega
  have h := sqrt_frechetVariance_abs_sub_le_wasserstein2
    (completedLaw mu) (completedLaw nu)
    ((finiteSecondMoment_completedLaw_iff mu).2 hFstOmega)
    ((finiteSecondMoment_completedLaw_iff nu).2 hSndOmega)
  rw [frechetVariance_completedLaw, frechetVariance_completedLaw] at h
  change
    |Real.sqrt (frechetVariance ((Kernel.fst rho) omega)).toReal -
        Real.sqrt (frechetVariance ((Kernel.snd rho) omega)).toReal| ≤
      (wasserstein2
        (completedLaw (kernelProbabilityLaw (Kernel.fst rho) omega))
        (completedLaw (kernelProbabilityLaw (Kernel.snd rho) omega))).toReal at h
  simpa only [posteriorDisplacementENN, abs_sub_comm] using h

/-- The sole remaining topological-measure-theoretic input for measurability
of posterior displacement: measurability of `W₂` for Mathlib's Giry
measurable structure on probability laws.  On a Polish space the standard
route is lower semicontinuity in the weak topology together with equality of
its Borel sigma-algebra and the Giry sigma-algebra.  This is isolated because
Mathlib currently has no Wasserstein library from which it can be imported. -/
def Wasserstein2LawMeasurable (T : Type*) [PseudoMetricSpace T]
    [MeasurableSpace T] [OpensMeasurableSpace T]
    [TopologicalSpace.SeparableSpace T] : Prop :=
  Measurable fun p : ProbabilityMeasure T × ProbabilityMeasure T =>
    wasserstein2 p.1 p.2

/-- Once the standard Polish-space measurability theorem for `W₂` is
supplied, posterior displacement is measurable. -/
theorem measurable_posteriorDisplacementENN
    (rho : Kernel[m, (inferInstance : MeasurableSpace (S × S))] Omega (S × S))
    [IsMarkovKernel rho]
    (hW : Wasserstein2LawMeasurable (PseudometricCompletion S)) :
    Measurable[m] (posteriorDisplacementENN rho) := by
  let F : Omega → ProbabilityMeasure (PseudometricCompletion S) ×
      ProbabilityMeasure (PseudometricCompletion S) := fun omega =>
    (kernelProbabilityLaw (completedKernel (Kernel.fst rho)) omega,
      kernelProbabilityLaw (completedKernel (Kernel.snd rho)) omega)
  have hF : Measurable[m] F :=
    (measurable_kernelProbabilityLaw (completedKernel (Kernel.fst rho))).prodMk
      (measurable_kernelProbabilityLaw (completedKernel (Kernel.snd rho)))
  have hEq : posteriorDisplacementENN rho =
      (fun p : ProbabilityMeasure (PseudometricCompletion S) ×
          ProbabilityMeasure (PseudometricCompletion S) =>
        wasserstein2 p.1 p.2) ∘ F := by
    funext omega
    simp only [posteriorDisplacementENN, F, Function.comp_apply]
    rw [kernelProbabilityLaw_completedKernel (Kernel.fst rho) omega,
      kernelProbabilityLaw_completedKernel (Kernel.snd rho) omega]
  rw [hEq]
  exact hW.comp hF

end JointCoupling

section ConditionalPosteriorDisplacement

variable {Omega S : Type*} {mOmega : MeasurableSpace Omega}
  [PseudoMetricSpace S] [MeasurableSpace S] [Nonempty S]
  [OpensMeasurableSpace S] [TopologicalSpace.SeparableSpace S]

/-- The two marginals of a joint RCD are RCDs of the two coordinate random
elements. -/
theorem regularConditionalLaw_fst_of_pair
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (m : MeasurableSpace Omega) (hm : m ≤ mOmega)
    (X Y : Omega → S) (hX : Measurable[mOmega] X)
    (hY : Measurable[mOmega] Y)
    (rho : Kernel[m, (inferInstance : MeasurableSpace (S × S))]
      Omega (S × S)) [IsMarkovKernel rho]
    (hrho : IsRegularConditionalLaw mu m hm
      (fun omega => (X omega, Y omega)) rho) :
    IsRegularConditionalLaw mu m hm X (Kernel.fst rho) := by
  have hPair : Measurable[mOmega] fun omega => (X omega, Y omega) :=
    hX.prodMk hY
  have h := regularConditionalLaw_map mu m hm
    (fun omega => (X omega, Y omega)) hPair rho hrho Prod.fst measurable_fst
  simpa only [Function.comp_def, Kernel.fst_eq] using h

theorem regularConditionalLaw_snd_of_pair
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (m : MeasurableSpace Omega) (hm : m ≤ mOmega)
    (X Y : Omega → S) (hX : Measurable[mOmega] X)
    (hY : Measurable[mOmega] Y)
    (rho : Kernel[m, (inferInstance : MeasurableSpace (S × S))]
      Omega (S × S)) [IsMarkovKernel rho]
    (hrho : IsRegularConditionalLaw mu m hm
      (fun omega => (X omega, Y omega)) rho) :
    IsRegularConditionalLaw mu m hm Y (Kernel.snd rho) := by
  have hPair : Measurable[mOmega] fun omega => (X omega, Y omega) :=
    hX.prodMk hY
  have h := regularConditionalLaw_map mu m hm
    (fun omega => (X omega, Y omega)) hPair rho hrho Prod.snd measurable_snd
  simpa only [Function.comp_def, Kernel.snd_eq] using h

/-- Result 16(ii), version independence for posterior displacement.  Two
joint RCD versions give the same completed marginal laws, and hence the same
Wasserstein displacement, outside one common null set. -/
theorem posteriorDisplacementENN_ae_eq_of_pairRCDs
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (m : MeasurableSpace Omega) (hm : m ≤ mOmega)
    (X Y : Omega → S) (hX : Measurable[mOmega] X)
    (hY : Measurable[mOmega] Y)
    (rho eta : Kernel[m, (inferInstance : MeasurableSpace (S × S))]
      Omega (S × S))
    [IsMarkovKernel rho] [IsMarkovKernel eta]
    (hrho : IsRegularConditionalLaw mu m hm
      (fun omega => (X omega, Y omega)) rho)
    (heta : IsRegularConditionalLaw mu m hm
      (fun omega => (X omega, Y omega)) eta) :
    posteriorDisplacementENN rho =ᵐ[mu] posteriorDisplacementENN eta := by
  have hrhoFst := regularConditionalLaw_fst_of_pair
    mu m hm X Y hX hY rho hrho
  have hetaFst := regularConditionalLaw_fst_of_pair
    mu m hm X Y hX hY eta heta
  have hrhoSnd := regularConditionalLaw_snd_of_pair
    mu m hm X Y hX hY rho hrho
  have hetaSnd := regularConditionalLaw_snd_of_pair
    mu m hm X Y hX hY eta heta
  have hFst := completedKernel_ae_eq mu m hm X hX
    (Kernel.fst rho) (Kernel.fst eta) hrhoFst hetaFst
  have hSnd := completedKernel_ae_eq mu m hm Y hY
    (Kernel.snd rho) (Kernel.snd eta) hrhoSnd hetaSnd
  filter_upwards [hFst, hSnd] with omega hFstOmega hSndOmega
  have hFstLaw :
      kernelProbabilityLaw (completedKernel (Kernel.fst rho)) omega =
        kernelProbabilityLaw (completedKernel (Kernel.fst eta)) omega := by
    apply ProbabilityMeasure.toMeasure_injective
    exact hFstOmega
  have hSndLaw :
      kernelProbabilityLaw (completedKernel (Kernel.snd rho)) omega =
        kernelProbabilityLaw (completedKernel (Kernel.snd eta)) omega := by
    apply ProbabilityMeasure.toMeasure_injective
    exact hSndOmega
  simp only [posteriorDisplacementENN]
  rw [← kernelProbabilityLaw_completedKernel (Kernel.fst rho) omega,
    ← kernelProbabilityLaw_completedKernel (Kernel.snd rho) omega,
    ← kernelProbabilityLaw_completedKernel (Kernel.fst eta) omega,
    ← kernelProbabilityLaw_completedKernel (Kernel.snd eta) omega,
    hFstLaw, hSndLaw]

/-- The joint-kernel squared transport cost is a version of the conditional
Lebesgue expectation of the realised squared displacement. -/
theorem jointKernelSquaredCost_ae_eq_condLExp
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (m : MeasurableSpace Omega) (hm : m ≤ mOmega)
    (X Y : Omega → S) (hX : Measurable[mOmega] X)
    (hY : Measurable[mOmega] Y)
    (rho : Kernel[m, (inferInstance : MeasurableSpace (S × S))]
      Omega (S × S)) [IsMarkovKernel rho]
    (hrho : IsRegularConditionalLaw mu m hm
      (fun omega => (X omega, Y omega)) rho) :
    (fun omega => ∫⁻ xy : S × S, pairSquaredDistanceENN xy ∂rho omega) =ᵐ[mu]
      mu⁻[fun omega => ENNReal.ofReal (dist (X omega) (Y omega) ^ 2) | m] := by
  have hPair : Measurable[mOmega] fun omega => (X omega, Y omega) :=
    hX.prodMk hY
  simpa only [pairSquaredDistanceENN] using
    kernelLIntegral_ae_eq_condLExp mu m hm
      (fun omega => (X omega, Y omega)) hPair rho hrho
      pairSquaredDistanceENN measurable_pairSquaredDistanceENN

/-- Extended-real conditional displacement bound in the exact form supplied
by the RCD. -/
theorem posteriorDisplacementENN_sq_le_condLExp
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (m : MeasurableSpace Omega) (hm : m ≤ mOmega)
    (X Y : Omega → S) (hX : Measurable[mOmega] X)
    (hY : Measurable[mOmega] Y)
    (rho : Kernel[m, (inferInstance : MeasurableSpace (S × S))]
      Omega (S × S)) [IsMarkovKernel rho]
    (hrho : IsRegularConditionalLaw mu m hm
      (fun omega => (X omega, Y omega)) rho) :
    ∀ᵐ omega ∂mu,
      posteriorDisplacementENN rho omega ^ 2 ≤
        mu⁻[fun omega => ENNReal.ofReal (dist (X omega) (Y omega) ^ 2) | m]
          omega := by
  filter_upwards [jointKernelSquaredCost_ae_eq_condLExp
    mu m hm X Y hX hY rho hrho] with omega hCost
  exact (posteriorDisplacementENN_sq_le rho omega).trans_eq hCost

/-- Integrability of the realised squared displacement is equivalent to
finiteness of its nonnegative extended integral. -/
theorem lintegral_pairSquaredDistance_ne_top
    (mu : Measure[mOmega] Omega) (X Y : Omega → S)
    (hX : Measurable[mOmega] X) (hY : Measurable[mOmega] Y)
    (hMoment : Integrable (fun omega => dist (X omega) (Y omega) ^ 2) mu) :
    (∫⁻ omega, ENNReal.ofReal (dist (X omega) (Y omega) ^ 2) ∂mu) ≠ ∞ := by
  have hMeas : AEMeasurable
      (fun omega => ENNReal.ofReal (dist (X omega) (Y omega) ^ 2)) mu :=
    ((((measurable_dist.comp (hX.prodMk hY)).pow_const 2).ennreal_ofReal).aemeasurable)
  have hFinite : ∀ᵐ omega ∂mu,
      ENNReal.ofReal (dist (X omega) (Y omega) ^ 2) ≠ ∞ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_ne_top
  apply (integrable_toReal_iff hMeas hFinite).mp
  convert hMoment using 1
  funext omega
  simp

/-- The extended posterior displacement is finite almost surely under the
realised squared-displacement moment assumption.  This conclusion does not
depend on the separate measurability theorem for `W₂`. -/
theorem posteriorDisplacementENN_ae_lt_top
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (m : MeasurableSpace Omega) (hm : m ≤ mOmega)
    (X Y : Omega → S) (hX : Measurable[mOmega] X)
    (hY : Measurable[mOmega] Y)
    (rho : Kernel[m, (inferInstance : MeasurableSpace (S × S))]
      Omega (S × S)) [IsMarkovKernel rho]
    (hrho : IsRegularConditionalLaw mu m hm
      (fun omega => (X omega, Y omega)) rho)
    (hMoment : Integrable (fun omega => dist (X omega) (Y omega) ^ 2) mu) :
    ∀ᵐ omega ∂mu, posteriorDisplacementENN rho omega < ∞ := by
  let cost : Omega → ENNReal := fun omega =>
    ENNReal.ofReal (dist (X omega) (Y omega) ^ 2)
  have hCostFinite : (∫⁻ omega, cost omega ∂mu) ≠ ∞ :=
    lintegral_pairSquaredDistance_ne_top mu X Y hX hY hMoment
  filter_upwards [posteriorDisplacementENN_sq_le_condLExp
      mu m hm X Y hX hY rho hrho,
    MeasureTheory.condLExp_ne_top hCostFinite]
      with omega hBound hCondFinite
  have hSqFinite : posteriorDisplacementENN rho omega ^ 2 ≠ ∞ :=
    ne_top_of_le_ne_top hCondFinite hBound
  have hDeltaFinite : posteriorDisplacementENN rho omega ≠ ∞ := by
    intro hTop
    apply hSqFinite
    simp [hTop]
  exact lt_top_iff_ne_top.2 hDeltaFinite

/-- Real conditional displacement bound. -/
theorem posteriorDisplacement_sq_le_condExp
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (m : MeasurableSpace Omega) (hm : m ≤ mOmega)
    (X Y : Omega → S) (hX : Measurable[mOmega] X)
    (hY : Measurable[mOmega] Y)
    (rho : Kernel[m, (inferInstance : MeasurableSpace (S × S))]
      Omega (S × S)) [IsMarkovKernel rho]
    (hrho : IsRegularConditionalLaw mu m hm
      (fun omega => (X omega, Y omega)) rho)
    (hMoment : Integrable (fun omega => dist (X omega) (Y omega) ^ 2) mu) :
    ∀ᵐ omega ∂mu,
      posteriorDisplacement rho omega ^ 2 ≤
        mu[fun omega => dist (X omega) (Y omega) ^ 2 | m] omega := by
  let cost : Omega → ENNReal := fun omega =>
    ENNReal.ofReal (dist (X omega) (Y omega) ^ 2)
  have hCostMeas : AEMeasurable cost mu := by
    exact ((((measurable_dist.comp (hX.prodMk hY)).pow_const 2).ennreal_ofReal).aemeasurable)
  have hCostFinite : (∫⁻ omega, cost omega ∂mu) ≠ ∞ := by
    exact lintegral_pairSquaredDistance_ne_top mu X Y hX hY hMoment
  filter_upwards [posteriorDisplacementENN_sq_le_condLExp
      mu m hm X Y hX hY rho hrho,
    MeasureTheory.condLExp_ne_top hCostFinite,
    MeasureTheory.toReal_condLExp m hCostMeas hCostFinite]
      with omega hBound hCondFinite hToReal
  have hReal := ENNReal.toReal_mono hCondFinite hBound
  rw [ENNReal.toReal_pow, hToReal] at hReal
  simpa only [posteriorDisplacement, cost, ENNReal.toReal_ofReal,
    sq_nonneg] using hReal

/-- Under the manuscript's second-moment assumption, posterior displacement
is square integrable. -/
theorem posteriorDisplacement_memLp_two
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (m : MeasurableSpace Omega) (hm : m ≤ mOmega)
    (X Y : Omega → S) (hX : Measurable[mOmega] X)
    (hY : Measurable[mOmega] Y)
    (rho : Kernel[m, (inferInstance : MeasurableSpace (S × S))]
      Omega (S × S)) [IsMarkovKernel rho]
    (hrho : IsRegularConditionalLaw mu m hm
      (fun omega => (X omega, Y omega)) rho)
    (hW : Wasserstein2LawMeasurable (PseudometricCompletion S))
    (hMoment : Integrable (fun omega => dist (X omega) (Y omega) ^ 2) mu) :
    MemLp (posteriorDisplacement rho) 2 mu := by
  have hDeltaMeasM : Measurable[m] (posteriorDisplacement rho) :=
    (measurable_posteriorDisplacementENN rho hW).ennreal_toReal
  have hDeltaMeas : Measurable[mOmega] (posteriorDisplacement rho) :=
    hDeltaMeasM.mono hm le_rfl
  rw [memLp_two_iff_integrable_sq hDeltaMeas.aestronglyMeasurable]
  have hCondInt : Integrable
      (mu[fun omega => dist (X omega) (Y omega) ^ 2 | m]) mu :=
    MeasureTheory.integrable_condExp (μ := mu)
  apply hCondInt.mono' (hDeltaMeas.pow_const 2).aestronglyMeasurable
  filter_upwards [posteriorDisplacement_sq_le_condExp
      mu m hm X Y hX hY rho hrho hMoment] with omega hBound
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hBound

/-- The unconditional squared-displacement inequality in Result 16(iii). -/
theorem integral_posteriorDisplacement_sq_le
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (m : MeasurableSpace Omega) (hm : m ≤ mOmega)
    (X Y : Omega → S) (hX : Measurable[mOmega] X)
    (hY : Measurable[mOmega] Y)
    (rho : Kernel[m, (inferInstance : MeasurableSpace (S × S))]
      Omega (S × S)) [IsMarkovKernel rho]
    (hrho : IsRegularConditionalLaw mu m hm
      (fun omega => (X omega, Y omega)) rho)
    (hW : Wasserstein2LawMeasurable (PseudometricCompletion S))
    (hMoment : Integrable (fun omega => dist (X omega) (Y omega) ^ 2) mu) :
    ∫ omega, posteriorDisplacement rho omega ^ 2 ∂mu ≤
      ∫ omega, dist (X omega) (Y omega) ^ 2 ∂mu := by
  have hDeltaLp := posteriorDisplacement_memLp_two
    mu m hm X Y hX hY rho hrho hW hMoment
  have hDeltaInt : Integrable
      (fun omega => posteriorDisplacement rho omega ^ 2) mu := by
    exact (memLp_two_iff_integrable_sq
      ((measurable_posteriorDisplacementENN rho hW).ennreal_toReal.mono hm le_rfl
        |>.aestronglyMeasurable)).1 hDeltaLp
  have hCondInt : Integrable
      (mu[fun omega => dist (X omega) (Y omega) ^ 2 | m]) mu :=
    MeasureTheory.integrable_condExp (μ := mu)
  calc
    ∫ omega, posteriorDisplacement rho omega ^ 2 ∂mu ≤
        ∫ omega, mu[fun omega => dist (X omega) (Y omega) ^ 2 | m] omega ∂mu :=
      integral_mono_ae hDeltaInt hCondInt
        (posteriorDisplacement_sq_le_condExp
          mu m hm X Y hX hY rho hrho hMoment)
    _ = ∫ omega, dist (X omega) (Y omega) ^ 2 ∂mu :=
      integral_condExp hm

end ConditionalPosteriorDisplacement

end

end SequentialLearning
