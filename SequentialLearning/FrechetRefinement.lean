import SequentialLearning.FrechetRiskWellPosedness
import SequentialLearning.ThreeWayRefinement

/-!
# Frechet variance under refinement

This file formalises the manuscript's geometric refinement lemma.  For nested
information states `mCoarse ≤ mFine`, the posterior Frechet variance at the
coarse state dominates the conditional expectation of the posterior Frechet
variance at the fine state.  Their difference is the refinement gain `Gamma`.

The proof deliberately uses a countable dense family of centres.  For each
centre, the fixed-centre posterior risk obeys the tower property; a common
almost-sure statement over the dense sequence then permits taking the
infimum.  This is the substantive measure-theoretic step that cannot be
replaced merely by scalar conditional-expectation algebra.
-/

namespace SequentialLearning

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal MeasureTheory ProbabilityTheory

noncomputable section

section FrechetRefinement

variable {Omega S : Type*} {mOmega : MeasurableSpace Omega}
  [PseudoMetricSpace S] [MeasurableSpace S] [Nonempty S]
  [OpensMeasurableSpace S] [TopologicalSpace.SeparableSpace S]

/-- The real-valued posterior Frechet variance represented by a conditional
law kernel.  Under the moment hypotheses below, the extended-real variance is
finite almost surely, so `toReal` loses no information on the relevant common
full-measure set. -/
def posteriorFrechetVarianceReal
    (m : MeasurableSpace Omega)
    (kappa : Kernel[m, (inferInstance : MeasurableSpace S)] Omega S) :
    Omega → ℝ :=
  fun omega => (frechetVariance (kappa omega)).toReal

/-- Posterior Frechet variance is measurable in the conditioning
sigma-algebra. -/
theorem stronglyMeasurable_posteriorFrechetVarianceReal
    (m : MeasurableSpace Omega)
    (kappa : Kernel[m, (inferInstance : MeasurableSpace S)] Omega S)
    [IsMarkovKernel kappa] :
    StronglyMeasurable[m] (posteriorFrechetVarianceReal m kappa) := by
  exact (measurable_posteriorFrechetVariance m kappa).ennreal_toReal
    |>.stronglyMeasurable

/-- The Frechet refinement gain

`Gamma(X; mCoarse, mFine) = V(X | mCoarse) -
  E[V(X | mFine) | mCoarse]`,

represented using selected regular conditional-law kernels. -/
def frechetRefinementGain
    (mu : Measure[mOmega] Omega)
    (mCoarse mFine : MeasurableSpace Omega)
    (kappaCoarse :
      Kernel[mCoarse, (inferInstance : MeasurableSpace S)] Omega S)
    (kappaFine :
      Kernel[mFine, (inferInstance : MeasurableSpace S)] Omega S) :
    Omega → ℝ :=
  refinementGain mu mCoarse
    (posteriorFrechetVarianceReal mCoarse kappaCoarse)
    (posteriorFrechetVarianceReal mFine kappaFine)

omit [Nonempty S] [OpensMeasurableSpace S]
  [TopologicalSpace.SeparableSpace S] in
/-- The refinement gain is independent, almost surely, of the selected
regular conditional-law versions. -/
theorem frechetRefinementGain_ae_eq
    [MeasurableSpace.CountablyGenerated S]
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (mCoarse mFine : MeasurableSpace Omega)
    (hCoarseFine : mCoarse ≤ mFine) (hFineAmbient : mFine ≤ mOmega)
    (X : Omega → S)
    (kappaCoarse etaCoarse :
      Kernel[mCoarse, (inferInstance : MeasurableSpace S)] Omega S)
    (kappaFine etaFine :
      Kernel[mFine, (inferInstance : MeasurableSpace S)] Omega S)
    [IsMarkovKernel kappaCoarse] [IsMarkovKernel etaCoarse]
    [IsMarkovKernel kappaFine] [IsMarkovKernel etaFine]
    (hkappaCoarse : IsRegularConditionalLaw mu mCoarse
      (hCoarseFine.trans hFineAmbient) X kappaCoarse)
    (hetaCoarse : IsRegularConditionalLaw mu mCoarse
      (hCoarseFine.trans hFineAmbient) X etaCoarse)
    (hkappaFine : IsRegularConditionalLaw mu mFine
      hFineAmbient X kappaFine)
    (hetaFine : IsRegularConditionalLaw mu mFine
      hFineAmbient X etaFine) :
    frechetRefinementGain mu mCoarse mFine kappaCoarse kappaFine =ᵐ[mu]
      frechetRefinementGain mu mCoarse mFine etaCoarse etaFine := by
  have hCoarseENN := posteriorFrechetVariance_ae_eq
    mu mCoarse (hCoarseFine.trans hFineAmbient) X
      kappaCoarse etaCoarse hkappaCoarse hetaCoarse
  have hFineENN := posteriorFrechetVariance_ae_eq
    mu mFine hFineAmbient X kappaFine etaFine hkappaFine hetaFine
  have hCoarseReal :
      posteriorFrechetVarianceReal mCoarse kappaCoarse =ᵐ[mu]
        posteriorFrechetVarianceReal mCoarse etaCoarse := by
    filter_upwards [hCoarseENN] with omega homega
    simp only [posteriorFrechetVarianceReal]
    rw [homega]
  have hFineReal :
      posteriorFrechetVarianceReal mFine kappaFine =ᵐ[mu]
        posteriorFrechetVarianceReal mFine etaFine := by
    filter_upwards [hFineENN] with omega homega
    simp only [posteriorFrechetVarianceReal]
    rw [homega]
  have hFineConditional :=
    (condExp_congr_ae (m := mCoarse) hFineReal)
  filter_upwards [hCoarseReal, hFineConditional] with
      omega hCoarse hFine
  change posteriorFrechetVarianceReal mCoarse kappaCoarse omega -
      mu[posteriorFrechetVarianceReal mFine kappaFine | mCoarse] omega =
    posteriorFrechetVarianceReal mCoarse etaCoarse omega -
      mu[posteriorFrechetVarianceReal mFine etaFine | mCoarse] omega
  rw [hCoarse, hFine]

/-- Finiteness of posterior risk at one reference centre gives, on one common
full-measure set, finiteness at every centre.  The universal quantifier is
inside the almost-sure statement; no uncountable union of null sets is used. -/
theorem posteriorFrechetRisk_finite_everywhere_ae
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (m : MeasurableSpace Omega) (hm : m ≤ mOmega)
    (X : Omega → S) (hX : Measurable[mOmega] X)
    (kappa : Kernel[m, (inferInstance : MeasurableSpace S)] Omega S)
    [IsMarkovKernel kappa]
    (hkappa : IsRegularConditionalLaw mu m hm X kappa)
    (s0 : S)
    (hMoment : Integrable (fun omega => dist (X omega) s0 ^ 2) mu) :
    ∀ᵐ omega ∂mu, ∀ s : S, frechetRisk (kappa omega) s < ∞ := by
  have hFiniteAtReference :=
    (posteriorFrechet_finite_and_integrable
      mu m hm X hX kappa hkappa s0 hMoment).1
  filter_upwards [hFiniteAtReference] with omega hReference
  have hSecondMoment : HasFiniteSecondMoment (kappa omega) :=
    ⟨s0, hReference⟩
  intro s
  exact (frechetRisk_lt_top_iff_rootRisk_lt_top (kappa omega) s).2
    ((frechetRootRisk_finite_everywhere_iff (kappa omega)).1
      hSecondMoment s)

omit [Nonempty S] [TopologicalSpace.SeparableSpace S] in
/-- Fixed-centre posterior real risk is integrable at every centre when a
single reference-centre second moment exists. -/
theorem integrable_posteriorFrechetRiskReal_of_reference
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (m : MeasurableSpace Omega) (hm : m ≤ mOmega)
    (X : Omega → S) (hX : Measurable[mOmega] X)
    (kappa : Kernel[m, (inferInstance : MeasurableSpace S)] Omega S)
    [IsMarkovKernel kappa]
    (hkappa : IsRegularConditionalLaw mu m hm X kappa)
    (s0 : S)
    (hMoment : Integrable (fun omega => dist (X omega) s0 ^ 2) mu)
    (s : S) :
    Integrable (fun omega => (frechetRisk (kappa omega) s).toReal) mu := by
  have hVersion :=
    posteriorFrechetRisk_toReal_ae_eq_condExp_of_reference
      mu m hm X hX kappa hkappa s0 hMoment s
  exact integrable_condExp.congr hVersion.symm

/-- The conditional expectation of the fine posterior Frechet variance is at
most the coarse posterior Frechet variance.  This is the geometric core of
the refinement theorem. -/
theorem condExp_posteriorFrechetVarianceReal_le
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (mCoarse mFine : MeasurableSpace Omega)
    (hCoarseFine : mCoarse ≤ mFine) (hFineAmbient : mFine ≤ mOmega)
    (X : Omega → S) (hX : Measurable[mOmega] X)
    (kappaCoarse :
      Kernel[mCoarse, (inferInstance : MeasurableSpace S)] Omega S)
    (kappaFine :
      Kernel[mFine, (inferInstance : MeasurableSpace S)] Omega S)
    [IsMarkovKernel kappaCoarse] [IsMarkovKernel kappaFine]
    (hkappaCoarse : IsRegularConditionalLaw mu mCoarse
      (hCoarseFine.trans hFineAmbient) X kappaCoarse)
    (hkappaFine : IsRegularConditionalLaw mu mFine
      hFineAmbient X kappaFine)
    (s0 : S)
    (hMoment : Integrable (fun omega => dist (X omega) s0 ^ 2) mu) :
    mu[posteriorFrechetVarianceReal mFine kappaFine | mCoarse] ≤ᵐ[mu]
      posteriorFrechetVarianceReal mCoarse kappaCoarse := by
  let D : ℕ → S := TopologicalSpace.denseSeq S
  let VCoarse : Omega → ℝ :=
    posteriorFrechetVarianceReal mCoarse kappaCoarse
  let VFine : Omega → ℝ :=
    posteriorFrechetVarianceReal mFine kappaFine

  have hCoarseBundle := posteriorFrechet_finite_and_integrable
    mu mCoarse (hCoarseFine.trans hFineAmbient) X hX
      kappaCoarse hkappaCoarse s0 hMoment
  have hFineBundle := posteriorFrechet_finite_and_integrable
    mu mFine hFineAmbient X hX kappaFine hkappaFine s0 hMoment
  have hVCoarseFinite :
      ∀ᵐ omega ∂mu, frechetVariance (kappaCoarse omega) < ∞ :=
    hCoarseBundle.2.1
  have hVFineIntegrable : Integrable VFine mu := by
    change Integrable
      (fun omega => (frechetVariance (kappaFine omega)).toReal) mu
    exact hFineBundle.2.2.2
  have hCoarseRiskFinite :
      ∀ᵐ omega ∂mu, ∀ s : S, frechetRisk (kappaCoarse omega) s < ∞ :=
    posteriorFrechetRisk_finite_everywhere_ae
      mu mCoarse (hCoarseFine.trans hFineAmbient) X hX
        kappaCoarse hkappaCoarse s0 hMoment
  have hFineRiskFinite :
      ∀ᵐ omega ∂mu, ∀ s : S, frechetRisk (kappaFine omega) s < ∞ :=
    posteriorFrechetRisk_finite_everywhere_ae
      mu mFine hFineAmbient X hX kappaFine hkappaFine s0 hMoment

  have hCentreBound : ∀ k : ℕ,
      mu[VFine | mCoarse] ≤ᵐ[mu]
        fun omega => (frechetRisk (kappaCoarse omega) (D k)).toReal := by
    intro k
    have hRiskFineIntegrable : Integrable
        (fun omega => (frechetRisk (kappaFine omega) (D k)).toReal) mu :=
      integrable_posteriorFrechetRiskReal_of_reference
        mu mFine hFineAmbient X hX kappaFine hkappaFine s0 hMoment (D k)
    have hVarianceLeRiskFine : VFine ≤ᵐ[mu]
        fun omega => (frechetRisk (kappaFine omega) (D k)).toReal := by
      filter_upwards [hFineRiskFinite] with omega hFinite
      exact ENNReal.toReal_mono (hFinite (D k)).ne
        (posteriorFrechetVariance_le_risk
          mFine kappaFine (D k) omega)
    have hConditionalMono :
        mu[VFine | mCoarse] ≤ᵐ[mu]
          mu[(fun omega =>
            (frechetRisk (kappaFine omega) (D k)).toReal) | mCoarse] :=
      condExp_mono hVFineIntegrable
        hRiskFineIntegrable hVarianceLeRiskFine
    have hRiskFineVersion :=
      posteriorFrechetRisk_toReal_ae_eq_condExp_of_reference
        mu mFine hFineAmbient X hX kappaFine hkappaFine
          s0 hMoment (D k)
    have hRiskCoarseVersion :=
      posteriorFrechetRisk_toReal_ae_eq_condExp_of_reference
        mu mCoarse (hCoarseFine.trans hFineAmbient) X hX
          kappaCoarse hkappaCoarse s0 hMoment (D k)
    have hRiskTower :
        mu[(fun omega =>
          (frechetRisk (kappaFine omega) (D k)).toReal) | mCoarse] =ᵐ[mu]
          fun omega =>
            (frechetRisk (kappaCoarse omega) (D k)).toReal := by
      calc
        mu[(fun omega =>
            (frechetRisk (kappaFine omega) (D k)).toReal) | mCoarse]
            =ᵐ[mu]
          mu[mu[(fun omega => dist (X omega) (D k) ^ 2) | mFine] |
            mCoarse] :=
              condExp_congr_ae hRiskFineVersion
        _ =ᵐ[mu] mu[(fun omega => dist (X omega) (D k) ^ 2) |
            mCoarse] :=
          condExp_condExp_of_le hCoarseFine hFineAmbient
        _ =ᵐ[mu] (fun omega =>
            (frechetRisk (kappaCoarse omega) (D k)).toReal) :=
          hRiskCoarseVersion.symm
    filter_upwards [hConditionalMono, hRiskTower] with omega hMono hTower
    rw [hTower] at hMono
    exact hMono

  have hAllCentreBounds : ∀ᵐ omega ∂mu, ∀ k : ℕ,
      mu[VFine | mCoarse] omega ≤
        (frechetRisk (kappaCoarse omega) (D k)).toReal :=
    ae_all_iff.2 hCentreBound
  have hConditionalNonnegative :
      0 ≤ᵐ[mu] mu[VFine | mCoarse] := by
    apply condExp_nonneg
    filter_upwards with omega
    exact ENNReal.toReal_nonneg

  filter_upwards [hAllCentreBounds, hConditionalNonnegative,
      hCoarseRiskFinite, hVCoarseFinite] with
      omega hBounds hNonnegative hRiskFinite hVarianceFinite
  have hENNBound :
      ENNReal.ofReal (mu[VFine | mCoarse] omega) ≤
        frechetVariance (kappaCoarse omega) := by
    rw [frechetVariance_eq_iInf_denseSeq]
    apply le_iInf
    intro k
    exact (ENNReal.ofReal_le_iff_le_toReal
      (hRiskFinite (D k)).ne).2 (hBounds k)
  have hRealBound :
      mu[VFine | mCoarse] omega ≤
        (frechetVariance (kappaCoarse omega)).toReal := by
    have hToReal := ENNReal.toReal_mono hVarianceFinite.ne hENNBound
    simpa [ENNReal.toReal_ofReal hNonnegative] using hToReal
  exact hRealBound

/-- The complete Frechet refinement theorem.  The gain `Gamma` is measurable
in the coarse information state, integrable, and nonnegative almost surely. -/
theorem frechetRefinementGain_wellPosed
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (mCoarse mFine : MeasurableSpace Omega)
    (hCoarseFine : mCoarse ≤ mFine) (hFineAmbient : mFine ≤ mOmega)
    (X : Omega → S) (hX : Measurable[mOmega] X)
    (kappaCoarse :
      Kernel[mCoarse, (inferInstance : MeasurableSpace S)] Omega S)
    (kappaFine :
      Kernel[mFine, (inferInstance : MeasurableSpace S)] Omega S)
    [IsMarkovKernel kappaCoarse] [IsMarkovKernel kappaFine]
    (hkappaCoarse : IsRegularConditionalLaw mu mCoarse
      (hCoarseFine.trans hFineAmbient) X kappaCoarse)
    (hkappaFine : IsRegularConditionalLaw mu mFine
      hFineAmbient X kappaFine)
    (s0 : S)
    (hMoment : Integrable (fun omega => dist (X omega) s0 ^ 2) mu) :
    StronglyMeasurable[mCoarse]
        (frechetRefinementGain mu mCoarse mFine kappaCoarse kappaFine) ∧
      Integrable
        (frechetRefinementGain mu mCoarse mFine kappaCoarse kappaFine) mu ∧
      0 ≤ᵐ[mu]
        frechetRefinementGain mu mCoarse mFine kappaCoarse kappaFine := by
  have hCoarseBundle := posteriorFrechet_finite_and_integrable
    mu mCoarse (hCoarseFine.trans hFineAmbient) X hX
      kappaCoarse hkappaCoarse s0 hMoment
  have hFineBundle := posteriorFrechet_finite_and_integrable
    mu mFine hFineAmbient X hX kappaFine hkappaFine s0 hMoment
  have hVCoarseIntegrable :
      Integrable (posteriorFrechetVarianceReal mCoarse kappaCoarse) mu := by
    change Integrable
      (fun omega => (frechetVariance (kappaCoarse omega)).toReal) mu
    exact hCoarseBundle.2.2.2
  have hVFineIntegrable :
      Integrable (posteriorFrechetVarianceReal mFine kappaFine) mu := by
    change Integrable
      (fun omega => (frechetVariance (kappaFine omega)).toReal) mu
    exact hFineBundle.2.2.2
  have hMeasurable : StronglyMeasurable[mCoarse]
      (frechetRefinementGain mu mCoarse mFine
        kappaCoarse kappaFine) := by
    exact (stronglyMeasurable_posteriorFrechetVarianceReal
      mCoarse kappaCoarse).sub stronglyMeasurable_condExp
  have hIntegrable : Integrable
      (frechetRefinementGain mu mCoarse mFine
        kappaCoarse kappaFine) mu := by
    exact refinementGain_integrable mu mCoarse
      (posteriorFrechetVarianceReal mCoarse kappaCoarse)
      (posteriorFrechetVarianceReal mFine kappaFine)
      hVCoarseIntegrable hVFineIntegrable
  have hNonnegative : 0 ≤ᵐ[mu]
      frechetRefinementGain mu mCoarse mFine
        kappaCoarse kappaFine := by
    have hDomination := condExp_posteriorFrechetVarianceReal_le
      mu mCoarse mFine hCoarseFine hFineAmbient X hX
        kappaCoarse kappaFine hkappaCoarse hkappaFine s0 hMoment
    filter_upwards [hDomination] with omega homega
    exact sub_nonneg.2 homega
  exact ⟨hMeasurable, hIntegrable, hNonnegative⟩

end FrechetRefinement

end

end SequentialLearning
