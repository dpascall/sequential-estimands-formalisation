import SequentialLearning.AbsorptionOracle
import SequentialLearning.TerminalThreeWayRefinement
import SequentialLearning.ClosedBinaryOracleRCD
import SequentialLearning.ClosedHilbertOracleRCD

/-!
# Master-facing absorption-oracle results

This module joins the generic refinement and binary-oracle machinery to the
specific absorption event from the manuscript.  The public theorems are named
after the manuscript labels `threeway`, `oraclestrict`, and `oraclehilbert`.

The branch-kernel implementation is hidden behind `AbsorptionOracleRCDs`, whose
two fields state exactly that the coarse mixture and revealed-status laws are
regular conditional laws.  No branch-finiteness or branch-`L²` premise occurs
in any public wrapper.
-/

namespace SequentialLearning

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal MeasureTheory ProbabilityTheory RealInnerProductSpace

noncomputable section

variable {Omega : Type*} {mOmega : MeasurableSpace Omega}

/-- The terminal observational information enlarged by the absorption status
at the realised final observation stage. -/
abbrev absorptionOracleSpace
    (FInf : MeasurableSpace Omega) (E : ℕ → Set Omega) (f : Omega → ℕ) :
    MeasurableSpace Omega :=
  absorptionOracleMeasurableSpace FInf (absorptionEvent E f)

/-- Manuscript notation `p_infinity = P(A | F_infinity)`, represented by the
everywhere-bounded version of the conditional event probability. -/
def pInfinity
    (mu : Measure[mOmega] Omega) (FInf : MeasurableSpace Omega)
    (E : ℕ → Set Omega) (f : Omega → ℕ) : Omega → ℝ :=
  boundedBinaryEventProbability mu FInf (absorptionEvent E f)

/-- Canonical Fréchet-variance gain from revealing the absorption status. -/
def absorptionOracleGap
    (mu : Measure[mOmega] Omega) (FInf : MeasurableSpace Omega)
    (E : ℕ → Set Omega) (f : Omega → ℕ)
    {S : Type*} [PseudoMetricSpace S] [MeasurableSpace S]
    (muA muAc : Kernel[FInf] Omega S) : Omega → ℝ :=
  binaryOracleFrechetGain mu FInf (absorptionOracleSpace FInf E f)
    (le_absorptionOracleMeasurableSpace FInf (absorptionEvent E f))
    (absorptionEvent E f)
    (measurableSet_absorptionOracle FInf (absorptionEvent E f))
    muA muAc

/-- The measurable strict-value event selected by the oracle gap itself. -/
def absorptionOracleStrictEvent
    (mu : Measure[mOmega] Omega) (FInf : MeasurableSpace Omega)
    (E : ℕ → Set Omega) (f : Omega → ℕ)
    {S : Type*} [PseudoMetricSpace S] [MeasurableSpace S]
    (muA muAc : Kernel[FInf] Omega S) : Set Omega :=
  frechetBinaryOracleStrictEvent mu FInf (absorptionOracleSpace FInf E f)
    (le_absorptionOracleMeasurableSpace FInf (absorptionEvent E f))
    (absorptionEvent E f)
    (measurableSet_absorptionOracle FInf (absorptionEvent E f))
    muA muAc

/-- The manuscript's sequence-form event, written directly in terms of
`p_infinity`, `mu_A`, and `mu_Ac`.  The master theorem identifies it almost
surely with the selected measurable strict event. -/
def absorptionOracleSequenceEvent
    (mu : Measure[mOmega] Omega) (FInf : MeasurableSpace Omega)
    (E : ℕ → Set Omega) (f : Omega → ℕ)
    {S : Type*} [PseudoMetricSpace S] [MeasurableSpace S]
    [Nonempty S] [OpensMeasurableSpace S]
    (muA muAc : Kernel[FInf] Omega S) : Set Omega :=
  {omega |
    0 < pInfinity mu FInf E f omega ∧
    pInfinity mu FInf E f omega < 1 ∧
    ¬HasCommonApproxMinimizingSequence
      (excessAboveInfimum (frechetRiskReal (muA omega)))
      (excessAboveInfimum (frechetRiskReal (muAc omega)))}

/-- A regular conditional law together with the probability-kernel property
that is part of being such a law.  Master-facing theorems quantify over this
bundle rather than exposing Lean's kernel typeclass separately. -/
structure RegularConditionalLawData
    (mu : Measure[mOmega] Omega)
    (m : MeasurableSpace Omega) (hm : m ≤ mOmega)
    {S : Type*} [MeasurableSpace S] (K : Omega → S) where
  kernel : Kernel[m] Omega S
  markov : IsMarkovKernel kernel
  isRCD : IsRegularConditionalLaw mu m hm K kernel

/-- The exact RCD content of saying that `mu_A` and `mu_Ac` are the two
conditional branch laws for the absorption oracle.  The first field says their
`p_infinity` mixture is the `F_infinity`-conditional law; the second says their
status-selected kernel is the oracle-conditional law. -/
structure AbsorptionOracleRCDs
    (mu : Measure[mOmega] Omega)
    (FInf : MeasurableSpace Omega) (hFInfAmbient : FInf ≤ mOmega)
    (E : ℕ → Set Omega) (f : Omega → ℕ)
    (hA : MeasurableSet[mOmega] (absorptionEvent E f))
    {S : Type*} [MeasurableSpace S]
    (K : Omega → S) (muA muAc : Kernel[FInf] Omega S) : Prop where
  markovA : IsMarkovKernel muA
  markovAc : IsMarkovKernel muAc
  coarse : IsRegularConditionalLaw mu FInf hFInfAmbient K
    (binaryEventMixtureKernel mu FInf (absorptionEvent E f) muA muAc)
  oracle : IsRegularConditionalLaw mu (absorptionOracleSpace FInf E f)
    (absorptionOracleMeasurableSpace_le hFInfAmbient hA) K
    (binaryOracleKernel
      (le_absorptionOracleMeasurableSpace FInf (absorptionEvent E f))
      (absorptionEvent E f)
      (measurableSet_absorptionOracle FInf (absorptionEvent E f))
      muA muAc)

/-- **`threeway`**: the terminal-target three-way refinement specialised to the
concrete absorption oracle. -/
theorem threeway
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (mCurrent FInf : MeasurableSpace Omega)
    (hCurrentInf : mCurrent ≤ FInf) (hFInfAmbient : FInf ≤ mOmega)
    (E : ℕ → Set Omega) (f : Omega → ℕ)
    (hE : ∀ k, MeasurableSet[mOmega] (E k))
    (hf : ∀ k, MeasurableSet[mOmega] {omega | f omega = k})
    {S : Type*} [PseudoMetricSpace S] [MeasurableSpace S] [Nonempty S]
    [OpensMeasurableSpace S] [TopologicalSpace.SeparableSpace S]
    (KInf : Omega → S) (hKInf : Measurable[mOmega] KInf)
    (lawCurrent : RegularConditionalLawData mu mCurrent
      (hCurrentInf.trans hFInfAmbient) KInf)
    (lawInf : RegularConditionalLawData mu FInf hFInfAmbient KInf)
    (lawOracle : RegularConditionalLawData mu
      (absorptionOracleSpace FInf E f)
      (absorptionOracleMeasurableSpace_le hFInfAmbient
        (@measurableSet_absorptionEvent Omega mOmega E f hE hf)) KInf)
    (s0 : S)
    (hMoment : Integrable (fun omega ↦ dist (KInf omega) s0 ^ 2) mu) :
    ((posteriorFrechetVarianceReal mCurrent lawCurrent.kernel) =ᵐ[mu]
      fun omega ↦
        terminalReducibleGain mu mCurrent FInf
            lawCurrent.kernel lawInf.kernel omega +
          terminalEnlargementGain mu mCurrent FInf
              (absorptionOracleSpace FInf E f)
              lawInf.kernel lawOracle.kernel omega +
            terminalResidualRisk mu mCurrent
              (absorptionOracleSpace FInf E f) lawOracle.kernel omega) ∧
    (0 ≤ᵐ[mu]
      terminalReducibleGain mu mCurrent FInf
        lawCurrent.kernel lawInf.kernel) ∧
    (0 ≤ᵐ[mu]
      terminalEnlargementGain mu mCurrent FInf
        (absorptionOracleSpace FInf E f) lawInf.kernel lawOracle.kernel) ∧
    (0 ≤ᵐ[mu]
      terminalResidualRisk mu mCurrent
        (absorptionOracleSpace FInf E f) lawOracle.kernel) := by
  let A := absorptionEvent E f
  have hA : MeasurableSet[mOmega] A :=
    @measurableSet_absorptionEvent Omega mOmega E f hE hf
  have hInfOracle : FInf ≤ absorptionOracleSpace FInf E f :=
    le_absorptionOracleMeasurableSpace FInf A
  have hOracleAmbient : absorptionOracleSpace FInf E f ≤ mOmega :=
    absorptionOracleMeasurableSpace_le hFInfAmbient hA
  let _ : IsMarkovKernel lawCurrent.kernel := lawCurrent.markov
  let _ : IsMarkovKernel lawInf.kernel := lawInf.markov
  let _ : IsMarkovKernel lawOracle.kernel := lawOracle.markov
  exact terminalThreeWay_refinement mu mCurrent FInf
    (absorptionOracleSpace FInf E f) hCurrentInf hInfOracle hOracleAmbient
    KInf hKInf lawCurrent.kernel lawInf.kernel lawOracle.kernel
    lawCurrent.isRCD lawInf.isRCD lawOracle.isRCD s0 hMoment

/-- **`oraclestrict`**: strict value, the exact sequence-event
characterisation, the expectation criterion, and the quantitative separated-
sublevel bound for the concrete absorption oracle. -/
theorem oraclestrict
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (FInf : MeasurableSpace Omega) (hFInfAmbient : FInf ≤ mOmega)
    (E : ℕ → Set Omega) (f : Omega → ℕ)
    (hE : ∀ k, MeasurableSet[mOmega] (E k))
    (hf : ∀ k, MeasurableSet[mOmega] {omega | f omega = k})
    {S : Type*} [PseudoMetricSpace S] [MeasurableSpace S] [Nonempty S]
    [OpensMeasurableSpace S] [TopologicalSpace.SeparableSpace S]
    (KInf : Omega → S) (hKInf : Measurable[mOmega] KInf)
    (muA muAc : Kernel[FInf] Omega S)
    (hRCD : AbsorptionOracleRCDs mu FInf hFInfAmbient E f
      (@measurableSet_absorptionEvent Omega mOmega E f hE hf)
      KInf muA muAc)
    (s0 : S)
    (hMoment : Integrable (fun omega ↦ dist (KInf omega) s0 ^ 2) mu) :
    (absorptionOracleGap mu FInf E f muA muAc =ᵐ[mu]
      actualFrechetBinaryOracleGapRCD mu FInf
        (absorptionEvent E f) muA muAc) ∧
    StronglyMeasurable[FInf]
      (absorptionOracleGap mu FInf E f muA muAc) ∧
    Integrable (absorptionOracleGap mu FInf E f muA muAc) mu ∧
    (0 ≤ᵐ[mu] absorptionOracleGap mu FInf E f muA muAc) ∧
    MeasurableSet[FInf]
      (absorptionOracleStrictEvent mu FInf E f muA muAc) ∧
    (∀ᵐ omega ∂mu,
      omega ∈ absorptionOracleStrictEvent mu FInf E f muA muAc ↔
        omega ∈ absorptionOracleSequenceEvent mu FInf E f muA muAc) ∧
    (∀ᵐ omega ∂mu,
      omega ∉ absorptionOracleStrictEvent mu FInf E f muA muAc →
        absorptionOracleGap mu FInf E f muA muAc omega = 0) ∧
    ((0 < ∫ omega, absorptionOracleGap mu FInf E f muA muAc omega ∂mu) ↔
      0 < mu (absorptionOracleStrictEvent mu FInf E f muA muAc)) ∧
    ∀ epsilon : ℝ, 0 < epsilon →
      (∀ᵐ omega ∂mu,
        Disjoint
          {s | excessAboveInfimum (frechetRiskReal (muA omega)) s < epsilon}
          {s | excessAboveInfimum (frechetRiskReal (muAc omega)) s < epsilon}) →
      (fun omega ↦ min (pInfinity mu FInf E f omega)
          (1 - pInfinity mu FInf E f omega) * epsilon) ≤ᵐ[mu]
        absorptionOracleGap mu FInf E f muA muAc := by
  let A := absorptionEvent E f
  have hA : MeasurableSet[mOmega] A :=
    @measurableSet_absorptionEvent Omega mOmega E f hE hf
  have hInfOracle : FInf ≤ absorptionOracleSpace FInf E f :=
    le_absorptionOracleMeasurableSpace FInf A
  have hAOracle : MeasurableSet[absorptionOracleSpace FInf E f] A :=
    measurableSet_absorptionOracle FInf A
  have hOracleAmbient : absorptionOracleSpace FInf E f ≤ mOmega :=
    absorptionOracleMeasurableSpace_le hFInfAmbient hA
  let _ : IsMarkovKernel muA := hRCD.markovA
  let _ : IsMarkovKernel muAc := hRCD.markovAc
  have hClosed := actual_binary_oracle_frechet_refinement_closed
    mu FInf (absorptionOracleSpace FInf E f)
      (le_absorptionOracleMeasurableSpace FInf (absorptionEvent E f))
      hOracleAmbient (absorptionEvent E f)
      (measurableSet_absorptionOracle FInf (absorptionEvent E f)) KInf hKInf
      muA muAc hRCD.coarse hRCD.oracle s0 hMoment
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hClosed.1
  · exact hClosed.2.1
  · exact hClosed.2.2.1
  · exact hClosed.2.2.2.1
  · exact hClosed.2.2.2.2.1
  · filter_upwards [hClosed.2.2.2.2.2.1] with omega hOmega
    simpa only [absorptionOracleStrictEvent,
      absorptionOracleSequenceEvent, pInfinity, A,
      Set.mem_ofPred_eq] using hOmega
  · exact hClosed.2.2.2.2.2.2.1
  · exact hClosed.2.2.2.2.2.2.2
  · intro epsilon hEpsilon hDisjoint
    exact binaryOracleFrechetGain_lower_bound_of_disjoint_sublevels_closed
      mu FInf (absorptionOracleSpace FInf E f)
      (le_absorptionOracleMeasurableSpace FInf (absorptionEvent E f))
      (absorptionEvent E f)
      (measurableSet_absorptionOracle FInf (absorptionEvent E f))
      muA muAc hClosed.1 epsilon hEpsilon hDisjoint

/-- Hilbert strict-value event in manuscript notation. -/
def absorptionOracleHilbertStrictEvent
    (mu : Measure[mOmega] Omega) (FInf : MeasurableSpace Omega)
    (E : ℕ → Set Omega) (f : Omega → ℕ)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [MeasurableSpace H] [OpensMeasurableSpace H]
    [TopologicalSpace.SeparableSpace H]
    (muA muAc : Kernel[FInf] Omega H) : Set Omega :=
  hilbertBinaryOracleRCDStrictEvent mu FInf (absorptionEvent E f) muA muAc

/-- **`oraclehilbert`**: exact between-branch formula and strict-event
characterisation for the concrete absorption oracle, with branch `L²` derived
internally rather than required from the caller. -/
theorem oraclehilbert
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (FInf : MeasurableSpace Omega) (hFInfAmbient : FInf ≤ mOmega)
    (E : ℕ → Set Omega) (f : Omega → ℕ)
    (hE : ∀ k, MeasurableSet[mOmega] (E k))
    (hf : ∀ k, MeasurableSet[mOmega] {omega | f omega = k})
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [MeasurableSpace H] [OpensMeasurableSpace H]
    [TopologicalSpace.SeparableSpace H]
    (KInf : Omega → H) (hKInf : Measurable[mOmega] KInf)
    (muA muAc : Kernel[FInf] Omega H)
    (hRCD : AbsorptionOracleRCDs mu FInf hFInfAmbient E f
      (@measurableSet_absorptionEvent Omega mOmega E f hE hf)
      KInf muA muAc)
    (s0 : H)
    (hMoment : Integrable (fun omega ↦ dist (KInf omega) s0 ^ 2) mu) :
    (absorptionOracleGap mu FInf E f muA muAc =ᵐ[mu]
      fun omega ↦
        pInfinity mu FInf E f omega *
        (1 - pInfinity mu FInf E f omega) *
        ‖hilbertKernelMean FInf muA omega -
          hilbertKernelMean FInf muAc omega‖ ^ 2) ∧
    StronglyMeasurable[FInf]
      (absorptionOracleGap mu FInf E f muA muAc) ∧
    Integrable (absorptionOracleGap mu FInf E f muA muAc) mu ∧
    (0 ≤ᵐ[mu] absorptionOracleGap mu FInf E f muA muAc) ∧
    MeasurableSet[FInf]
      (absorptionOracleHilbertStrictEvent mu FInf E f muA muAc) ∧
    (∀ᵐ omega ∂mu,
      0 < absorptionOracleGap mu FInf E f muA muAc omega ↔
        omega ∈ absorptionOracleHilbertStrictEvent
          mu FInf E f muA muAc) ∧
    ((0 < ∫ omega, absorptionOracleGap mu FInf E f muA muAc omega ∂mu) ↔
      0 < mu (absorptionOracleHilbertStrictEvent
        mu FInf E f muA muAc)) ∧
    (∀ᵐ omega ∂mu,
      omega ∈ absorptionOracleStrictEvent mu FInf E f muA muAc ↔
        omega ∈ absorptionOracleHilbertStrictEvent
          mu FInf E f muA muAc) := by
  let A := absorptionEvent E f
  have hA : MeasurableSet[mOmega] A :=
    @measurableSet_absorptionEvent Omega mOmega E f hE hf
  have hInfOracle : FInf ≤ absorptionOracleSpace FInf E f :=
    le_absorptionOracleMeasurableSpace FInf A
  have hAOracle : MeasurableSet[absorptionOracleSpace FInf E f] A :=
    measurableSet_absorptionOracle FInf A
  have hOracleAmbient : absorptionOracleSpace FInf E f ≤ mOmega :=
    absorptionOracleMeasurableSpace_le hFInfAmbient hA
  let _ : IsMarkovKernel muA := hRCD.markovA
  let _ : IsMarkovKernel muAc := hRCD.markovAc
  have hClosed := actual_probabilistic_hilbert_oracle_closed
    mu FInf (absorptionOracleSpace FInf E f)
      (le_absorptionOracleMeasurableSpace FInf (absorptionEvent E f))
      hOracleAmbient (absorptionEvent E f)
      (measurableSet_absorptionOracle FInf (absorptionEvent E f)) KInf hKInf
      muA muAc hRCD.coarse hRCD.oracle s0 hMoment
  have hFormula : hilbertBinaryOracleRCDFormula mu FInf
      (absorptionEvent E f) muA muAc =
      fun omega ↦
        pInfinity mu FInf E f omega *
        (1 - pInfinity mu FInf E f omega) *
        ‖hilbertKernelMean FInf muA omega -
          hilbertKernelMean FInf muAc omega‖ ^ 2 := by
    rfl
  rw [hFormula] at hClosed
  simpa only [absorptionOracleGap, pInfinity,
    absorptionOracleHilbertStrictEvent,
    absorptionOracleStrictEvent] using hClosed

end

end SequentialLearning
