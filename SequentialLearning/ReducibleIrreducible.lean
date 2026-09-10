import SequentialLearning.HilbertLevyUpward

/-!
# Reducible and irreducible posterior uncertainty

For a square-integrable Hilbert-valued target, posterior variance at a finite
information state splits into uncertainty reducible by the limiting
information state and uncertainty remaining even there.  The reducible term
is exhausted by the successive posterior-mean innovations.
-/

namespace SequentialLearning

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal MeasureTheory ProbabilityTheory RealInnerProductSpace

noncomputable section

section ReducibleIrreducible

variable {Omega H : Type*} {mOmega : MeasurableSpace Omega}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Portion of stage-`n` posterior variance reducible by all information in
the limiting sigma-algebra. -/
def hilbertLimitRefinementGain
    (mu : Measure[mOmega] Omega)
    (filtration : Filtration ℕ mOmega)
    (K : Omega → H) (n : ℕ) : Omega → ℝ :=
  mu[(fun omega =>
    ‖oldTargetInnovation mu (filtration n)
      (filtrationLimit filtration) K omega‖ ^ 2) | filtration n]

/-- Predictable energy in the next posterior-mean innovation. -/
def predictableInnovationEnergy
    (mu : Measure[mOmega] Omega)
    (filtration : Filtration ℕ mOmega)
    (K : Omega → H) (n : ℕ) : Omega → ℝ :=
  mu[(fun omega =>
    ‖oldTargetInnovation mu (filtration n) (filtration (n + 1))
      K omega‖ ^ 2) | filtration n]

/-- At stage `n`, the predictable reducible variance left after the next
innovation. -/
def predictableResidualVariance
    (mu : Measure[mOmega] Omega)
    (filtration : Filtration ℕ mOmega)
    (K : Omega → H) (n : ℕ) : Omega → ℝ :=
  mu[hilbertLimitRefinementGain mu filtration K (n + 1) | filtration n]

/-- Posterior uncertainty that remains after all information in the limiting
sigma-algebra has been used, viewed from stage `n`. -/
def predictableIrreducibleVariance
    (mu : Measure[mOmega] Omega)
    (filtration : Filtration ℕ mOmega)
    (K : Omega → H) (n : ℕ) : Omega → ℝ :=
  mu[posteriorVariance mu (filtrationLimit filtration) K | filtration n]

/-- The stage-`m` posterior-mean innovation energy, viewed from the fixed
earlier information state `n`.  In uses below `n ≤ m`. -/
def conditionalInnovationEnergy
    (mu : Measure[mOmega] Omega)
    (filtration : Filtration ℕ mOmega)
    (K : Omega → H) (n m : ℕ) : Omega → ℝ :=
  mu[(fun omega =>
    ‖oldTargetInnovation mu (filtration m) (filtration (m + 1))
      K omega‖ ^ 2) | filtration n]

/-- The first `k` innovation energies after stage `n`, all conditioned on
the information available at stage `n`. -/
def conditionalInnovationPartialSum
    (mu : Measure[mOmega] Omega)
    (filtration : Filtration ℕ mOmega)
    (K : Omega → H) (n k : ℕ) : Omega → ℝ :=
  fun omega => ∑ j ∈ Finset.range k,
    conditionalInnovationEnergy mu filtration K n (n + j) omega

/-- Reducible variance left at stage `n + k`, viewed from stage `n`. -/
def conditionalInnovationResidual
    (mu : Measure[mOmega] Omega)
    (filtration : Filtration ℕ mOmega)
    (K : Omega → H) (n k : ℕ) : Omega → ℝ :=
  mu[hilbertLimitRefinementGain mu filtration K (n + k) | filtration n]

/-- Exact reducible/irreducible decomposition. -/
theorem hilbert_reducible_irreducible_decomposition
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration ℕ mOmega)
    (K : Omega → H) (hK : MemLp K 2 mu) (n : ℕ) :
    posteriorVariance mu (filtration n) K =ᵐ[mu]
      fun omega =>
        predictableIrreducibleVariance mu filtration K n omega +
          hilbertLimitRefinementGain mu filtration K n omega := by
  simpa only [predictableIrreducibleVariance,
    hilbertLimitRefinementGain] using
    posteriorVariance_refinement_hilbert mu
      (filtration n) (filtrationLimit filtration)
      (filtration_le_limit filtration n)
      (filtrationLimit_le_ambient filtration) K hK

/-- Reducible variance is nonnegative. -/
theorem hilbertLimitRefinementGain_nonnegative
    (mu : Measure[mOmega] Omega)
    (filtration : Filtration ℕ mOmega)
    (K : Omega → H) (n : ℕ) :
    0 ≤ᵐ[mu] hilbertLimitRefinementGain mu filtration K n := by
  apply condExp_nonneg
  filter_upwards with omega
  exact sq_nonneg _

/-- The limiting refinement gain is integrable. -/
theorem integrable_hilbertLimitRefinementGain
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration ℕ mOmega)
    (K : Omega → H) (hK : MemLp K 2 mu) (n : ℕ) :
    Integrable (hilbertLimitRefinementGain mu filtration K n) mu := by
  exact integrable_condExp

/-- The one-step innovation energy is integrable. -/
theorem integrable_predictableInnovationEnergy
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration ℕ mOmega)
    (K : Omega → H) (hK : MemLp K 2 mu) (n : ℕ) :
    Integrable (predictableInnovationEnergy mu filtration K n) mu := by
  exact integrable_condExp

/-- The unconditioned squared stage innovation is integrable. -/
theorem integrable_squared_oldTargetInnovation
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration ℕ mOmega)
    (K : Omega → H) (hK : MemLp K 2 mu) (m : ℕ) :
    Integrable (fun omega =>
      ‖oldTargetInnovation mu (filtration m) (filtration (m + 1))
        K omega‖ ^ 2) mu := by
  have hOneTwo : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hInnovation : MemLp
      (oldTargetInnovation mu (filtration m) (filtration (m + 1)) K)
      2 mu := by
    exact (hK.condExp hOneTwo).sub (hK.condExp hOneTwo)
  exact (memLp_two_iff_integrable_sq_norm hInnovation.1).mp hInnovation

/-- A stage-`n` conditional innovation energy is integrable. -/
theorem integrable_conditionalInnovationEnergy
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration ℕ mOmega)
    (K : Omega → H) (hK : MemLp K 2 mu) (n m : ℕ) :
    Integrable (conditionalInnovationEnergy mu filtration K n m) mu := by
  exact integrable_condExp

/-- A stage-`n` conditional residual is integrable. -/
theorem integrable_conditionalInnovationResidual
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration ℕ mOmega)
    (K : Omega → H) (hK : MemLp K 2 mu) (n k : ℕ) :
    Integrable (conditionalInnovationResidual mu filtration K n k) mu := by
  exact integrable_condExp

/-- Conditional innovation energies are nonnegative. -/
theorem conditionalInnovationEnergy_nonnegative
    (mu : Measure[mOmega] Omega)
    (filtration : Filtration ℕ mOmega)
    (K : Omega → H) (n m : ℕ) :
    0 ≤ᵐ[mu] conditionalInnovationEnergy mu filtration K n m := by
  apply condExp_nonneg
  filter_upwards with omega
  exact sq_nonneg _

/-- Conditional residuals are nonnegative. -/
theorem conditionalInnovationResidual_nonnegative
    (mu : Measure[mOmega] Omega)
    (filtration : Filtration ℕ mOmega)
    (K : Omega → H) (n k : ℕ) :
    0 ≤ᵐ[mu] conditionalInnovationResidual mu filtration K n k := by
  apply condExp_nonneg
  exact hilbertLimitRefinementGain_nonnegative mu filtration K (n + k)

/-- Conditioning the stage-`m` predictable energy back to stage `n` gives
the direct stage-`n` conditional innovation energy. -/
theorem condExp_predictableInnovationEnergy_eq
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration ℕ mOmega)
    (K : Omega → H) (n m : ℕ) (hnm : n ≤ m) :
    mu[predictableInnovationEnergy mu filtration K m | filtration n]
        =ᵐ[mu]
      conditionalInnovationEnergy mu filtration K n m := by
  simpa only [predictableInnovationEnergy, conditionalInnovationEnergy] using
    condExp_condExp_of_le (μ := mu)
      (f := fun omega =>
        ‖oldTargetInnovation mu (filtration m) (filtration (m + 1))
          K omega‖ ^ 2)
      (filtration.mono hnm) (filtration.le m)

/-- One innovation is removed from the reducible variance at each step. -/
theorem predictable_innovation_step
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration ℕ mOmega)
    (K : Omega → H) (hK : MemLp K 2 mu) (n : ℕ) :
    hilbertLimitRefinementGain mu filtration K n =ᵐ[mu]
      fun omega =>
        predictableInnovationEnergy mu filtration K n omega +
          predictableResidualVariance mu filtration K n omega := by
  have hFinite := posteriorVariance_refinement_hilbert mu
    (filtration n) (filtration (n + 1))
    (filtration.mono (Nat.le_succ n)) (filtration.le (n + 1)) K hK
  have hLimitN := hilbert_reducible_irreducible_decomposition
    mu filtration K hK n
  have hLimitNext := hilbert_reducible_irreducible_decomposition
    mu filtration K hK (n + 1)
  have hLimitVarianceIntegrable : Integrable
      (posteriorVariance mu (filtrationLimit filtration) K) mu := by
    dsimp only [posteriorVariance, posteriorMSE]
    exact integrable_condExp
  have hIrreducibleNextIntegrable : Integrable
      (predictableIrreducibleVariance mu filtration K (n + 1)) mu := by
    exact integrable_condExp
  have hGainNextIntegrable : Integrable
      (hilbertLimitRefinementGain mu filtration K (n + 1)) mu :=
    integrable_hilbertLimitRefinementGain mu filtration K hK (n + 1)
  have hCondDecomposition :
      mu[posteriorVariance mu (filtration (n + 1)) K | filtration n]
          =ᵐ[mu]
        fun omega =>
          mu[predictableIrreducibleVariance mu filtration K (n + 1) |
              filtration n] omega +
            predictableResidualVariance mu filtration K n omega := by
    have hCongr := condExp_congr_ae (m := filtration n) hLimitNext
    have hAdd := condExp_add hIrreducibleNextIntegrable
      hGainNextIntegrable (filtration n)
    refine hCongr.trans (hAdd.trans ?_)
    filter_upwards with omega
    rfl
  have hIrreducibleTower :
      mu[predictableIrreducibleVariance mu filtration K (n + 1) |
          filtration n] =ᵐ[mu]
        predictableIrreducibleVariance mu filtration K n := by
    simpa only [predictableIrreducibleVariance] using
      condExp_condExp_of_le (μ := mu)
        (f := posteriorVariance mu (filtrationLimit filtration) K)
        (filtration.mono (Nat.le_succ n)) (filtration.le (n + 1))
  filter_upwards [hFinite, hLimitN, hCondDecomposition,
      hIrreducibleTower] with omega hFiniteOmega hLimitNOmega
      hCondOmega hTowerOmega
  rw [hLimitNOmega, hCondOmega, hTowerOmega] at hFiniteOmega
  change
    predictableIrreducibleVariance mu filtration K n omega +
        hilbertLimitRefinementGain mu filtration K n omega =
      predictableIrreducibleVariance mu filtration K n omega +
        predictableResidualVariance mu filtration K n omega +
          predictableInnovationEnergy mu filtration K n omega
    at hFiniteOmega
  linarith

/-- The one-step innovation identity, viewed from any earlier stage `n`. -/
theorem conditional_innovation_step
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration ℕ mOmega)
    (K : Omega → H) (hK : MemLp K 2 mu) (n m : ℕ) (hnm : n ≤ m) :
    mu[hilbertLimitRefinementGain mu filtration K m | filtration n]
        =ᵐ[mu]
      fun omega =>
        conditionalInnovationEnergy mu filtration K n m omega +
          mu[hilbertLimitRefinementGain mu filtration K (m + 1) |
            filtration n] omega := by
  have hStep := predictable_innovation_step mu filtration K hK m
  have hCongr := condExp_congr_ae (m := filtration n) hStep
  have hEnergyInt := integrable_predictableInnovationEnergy
    mu filtration K hK m
  have hResidualInt : Integrable
      (predictableResidualVariance mu filtration K m) mu := by
    exact integrable_condExp
  have hAdd := condExp_add hEnergyInt hResidualInt (filtration n)
  have hEnergyTower := condExp_predictableInnovationEnergy_eq
    mu filtration K n m hnm
  have hResidualTower :
      mu[predictableResidualVariance mu filtration K m | filtration n]
          =ᵐ[mu]
        mu[hilbertLimitRefinementGain mu filtration K (m + 1) |
          filtration n] := by
    simpa only [predictableResidualVariance] using
      condExp_condExp_of_le (μ := mu)
        (f := hilbertLimitRefinementGain mu filtration K (m + 1))
        (filtration.mono hnm) (filtration.le m)
  refine hCongr.trans (hAdd.trans ?_)
  filter_upwards [hEnergyTower, hResidualTower] with omega hEnergy hResidual
  simp only [Pi.add_apply]
  rw [hEnergy, hResidual]

/-- Integrated one-step innovation identity. -/
theorem integral_predictable_innovation_step
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration ℕ mOmega)
    (K : Omega → H) (hK : MemLp K 2 mu) (n : ℕ) :
    ∫ omega, hilbertLimitRefinementGain mu filtration K n omega ∂mu =
      (∫ omega, predictableInnovationEnergy mu filtration K n omega ∂mu) +
        ∫ omega, hilbertLimitRefinementGain mu filtration K (n + 1) omega ∂mu := by
  have hStep := predictable_innovation_step mu filtration K hK n
  have hEnergyInt := integrable_predictableInnovationEnergy
    mu filtration K hK n
  have hGainNextInt := integrable_hilbertLimitRefinementGain
    mu filtration K hK (n + 1)
  calc
    ∫ omega, hilbertLimitRefinementGain mu filtration K n omega ∂mu =
        ∫ omega, (predictableInnovationEnergy mu filtration K n omega +
          predictableResidualVariance mu filtration K n omega) ∂mu :=
      integral_congr_ae hStep
    _ = (∫ omega, predictableInnovationEnergy mu filtration K n omega ∂mu) +
        ∫ omega, predictableResidualVariance mu filtration K n omega ∂mu :=
      integral_add hEnergyInt integrable_condExp
    _ = (∫ omega, predictableInnovationEnergy mu filtration K n omega ∂mu) +
        ∫ omega, hilbertLimitRefinementGain mu filtration K (n + 1) omega ∂mu := by
      change
        (∫ omega, predictableInnovationEnergy mu filtration K n omega ∂mu) +
            ∫ omega,
              mu[hilbertLimitRefinementGain mu filtration K (n + 1) |
                filtration n] omega ∂mu = _
      rw [integral_condExp (filtration.le n)]

/-- Finite telescoping form of the innovation decomposition. -/
theorem finite_predictable_innovation_telescope
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration ℕ mOmega)
    (K : Omega → H) (hK : MemLp K 2 mu) (n k : ℕ) :
    ∫ omega, hilbertLimitRefinementGain mu filtration K n omega ∂mu =
      (∑ j ∈ Finset.range k,
        ∫ omega,
          predictableInnovationEnergy mu filtration K (n + j) omega ∂mu) +
        ∫ omega,
          hilbertLimitRefinementGain mu filtration K (n + k) omega ∂mu := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ]
      have hStep := integral_predictable_innovation_step
        mu filtration K hK (n + k)
      rw [ih, hStep]
      simp only [Nat.add_assoc]
      ring

/-- Conditional finite telescope.  Unlike the integrated telescope above,
this is an almost-sure identity of stage-`n` random variables. -/
theorem finite_conditional_innovation_telescope
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration ℕ mOmega)
    (K : Omega → H) (hK : MemLp K 2 mu) (n k : ℕ) :
    hilbertLimitRefinementGain mu filtration K n =ᵐ[mu]
      fun omega =>
        conditionalInnovationPartialSum mu filtration K n k omega +
          conditionalInnovationResidual mu filtration K n k omega := by
  induction k with
  | zero =>
      have hSelf :
          mu[hilbertLimitRefinementGain mu filtration K n | filtration n] =
            hilbertLimitRefinementGain mu filtration K n := by
        exact condExp_of_stronglyMeasurable (filtration.le n)
          stronglyMeasurable_condExp
          (integrable_hilbertLimitRefinementGain mu filtration K hK n)
      filter_upwards with omega
      simp [conditionalInnovationPartialSum, conditionalInnovationResidual,
        hSelf]
  | succ k ih =>
      have hStep := conditional_innovation_step
        mu filtration K hK n (n + k) (Nat.le_add_right n k)
      filter_upwards [ih, hStep] with omega hTelescope hStepOmega
      rw [hTelescope]
      change
        conditionalInnovationPartialSum mu filtration K n k omega +
            mu[hilbertLimitRefinementGain mu filtration K (n + k) |
              filtration n] omega =
          conditionalInnovationPartialSum mu filtration K n (k + 1) omega +
            mu[hilbertLimitRefinementGain mu filtration K (n + (k + 1)) |
              filtration n] omega
      rw [hStepOmega]
      simp only [conditionalInnovationPartialSum, Finset.sum_range_succ]
      simp only [Nat.add_assoc]
      ring

/-- If the expected reducible residual vanishes, then its stage-`n`
conditional version vanishes almost surely.  Monotonicity of the residual is
essential here: convergence merely in mean would not by itself imply
pointwise almost-sure convergence of the full sequence. -/
theorem conditionalInnovationResidual_tendsto_zero_of_integral_tendsto
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration ℕ mOmega)
    (K : Omega → H) (hK : MemLp K 2 mu) (n : ℕ)
    (hResidual : Tendsto
      (fun k => ∫ omega,
        hilbertLimitRefinementGain mu filtration K (n + k) omega ∂mu)
      atTop (nhds 0)) :
    ∀ᵐ omega ∂mu, Tendsto
      (fun k => conditionalInnovationResidual mu filtration K n k omega)
      atTop (nhds 0) := by
  have hIntegrable : ∀ k, Integrable
      (conditionalInnovationResidual mu filtration K n k) mu := fun k =>
    integrable_conditionalInnovationResidual mu filtration K hK n k
  have hIntegralEq : ∀ k,
      ∫ omega, conditionalInnovationResidual mu filtration K n k omega ∂mu =
        ∫ omega,
          hilbertLimitRefinementGain mu filtration K (n + k) omega ∂mu := by
    intro k
    change
      ∫ omega,
          mu[hilbertLimitRefinementGain mu filtration K (n + k) |
            filtration n] omega ∂mu = _
    exact integral_condExp (filtration.le n)
  have hIntegralTendsto : Tendsto
      (fun k => ∫ omega,
        conditionalInnovationResidual mu filtration K n k omega ∂mu)
      atTop (nhds 0) := by
    simpa only [hIntegralEq] using hResidual
  have hStep : ∀ k,
      conditionalInnovationResidual mu filtration K n k =ᵐ[mu]
        fun omega =>
          conditionalInnovationEnergy mu filtration K n (n + k) omega +
            conditionalInnovationResidual mu filtration K n (k + 1) omega := by
    intro k
    simpa only [conditionalInnovationResidual, Nat.add_assoc] using
      conditional_innovation_step mu filtration K hK n (n + k)
        (Nat.le_add_right n k)
  have hStepAll : ∀ᵐ omega ∂mu, ∀ k,
      conditionalInnovationResidual mu filtration K n k omega =
        conditionalInnovationEnergy mu filtration K n (n + k) omega +
          conditionalInnovationResidual mu filtration K n (k + 1) omega := by
    rw [ae_all_iff]
    exact hStep
  have hEnergyAll : ∀ᵐ omega ∂mu, ∀ k,
      0 ≤ conditionalInnovationEnergy mu filtration K n (n + k) omega := by
    rw [ae_all_iff]
    exact fun k => conditionalInnovationEnergy_nonnegative
      mu filtration K n (n + k)
  have hAntitone : ∀ᵐ omega ∂mu, Antitone
      (fun k => conditionalInnovationResidual mu filtration K n k omega) := by
    filter_upwards [hStepAll, hEnergyAll] with omega hStepOmega hEnergyOmega
    apply antitone_nat_of_succ_le
    intro k
    have hEq := hStepOmega k
    have hNonnegative := hEnergyOmega k
    linarith
  have hLower : ∀ᵐ omega ∂mu, ∀ k,
      (0 : ℝ) ≤ conditionalInnovationResidual mu filtration K n k omega := by
    rw [ae_all_iff]
    exact fun k => conditionalInnovationResidual_nonnegative
      mu filtration K n k
  apply tendsto_of_integral_tendsto_of_antitone hIntegrable
    (integrable_zero Omega ℝ mu) (hf_mono := hAntitone)
    (hf_bound := hLower)
  simpa using hIntegralTendsto

/-- Conditional almost-sure innovation-series identity, under vanishing of
the expected residual.  This is the pointwise conditional version of the
manuscript display: its partial sums converge to the reducible variance at
the conditioning stage. -/
theorem conditional_innovation_series_of_residual_convergence
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration ℕ mOmega)
    (K : Omega → H) (hK : MemLp K 2 mu) (n : ℕ)
    (hResidual : Tendsto
      (fun k => ∫ omega,
        hilbertLimitRefinementGain mu filtration K (n + k) omega ∂mu)
      atTop (nhds 0)) :
    ∀ᵐ omega ∂mu, Tendsto
      (fun k => conditionalInnovationPartialSum mu filtration K n k omega)
      atTop
      (nhds (hilbertLimitRefinementGain mu filtration K n omega)) := by
  have hTelescope : ∀ k,
      hilbertLimitRefinementGain mu filtration K n =ᵐ[mu]
        fun omega =>
          conditionalInnovationPartialSum mu filtration K n k omega +
            conditionalInnovationResidual mu filtration K n k omega :=
    finite_conditional_innovation_telescope mu filtration K hK n
  have hTelescopeAll : ∀ᵐ omega ∂mu, ∀ k,
      hilbertLimitRefinementGain mu filtration K n omega =
        conditionalInnovationPartialSum mu filtration K n k omega +
          conditionalInnovationResidual mu filtration K n k omega := by
    rw [ae_all_iff]
    exact hTelescope
  have hResidualZero :=
    conditionalInnovationResidual_tendsto_zero_of_integral_tendsto
      mu filtration K hK n hResidual
  filter_upwards [hTelescopeAll, hResidualZero] with omega hEq hZero
  have hPartialEq :
      (fun k => conditionalInnovationPartialSum mu filtration K n k omega) =
        fun k => hilbertLimitRefinementGain mu filtration K n omega -
          conditionalInnovationResidual mu filtration K n k omega := by
    funext k
    linarith [hEq k]
  rw [hPartialEq]
  simpa using tendsto_const_nhds.sub hZero

/-- The integral of the limiting refinement gain is exactly the squared
`L²` distance between the finite-stage and limiting posterior means. -/
theorem integral_hilbertLimitRefinementGain_eq_mean_error
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration ℕ mOmega)
    (K : Omega → H) (hK : MemLp K 2 mu) (m : ℕ) :
    ∫ omega, hilbertLimitRefinementGain mu filtration K m omega ∂mu =
      ∫ omega,
        ‖posteriorMean mu (filtrationLimit filtration) K omega -
          posteriorMean mu (filtration m) K omega‖ ^ 2 ∂mu := by
  change
    ∫ omega,
        mu[(fun a =>
          ‖oldTargetInnovation mu (filtration m)
            (filtrationLimit filtration) K a‖ ^ 2) |
          filtration m] omega ∂mu = _
  rw [integral_condExp (filtration.le m)]
  rfl

/-- Conditional innovation series from the Hilbert-valued `L²` form of
Lévy's upward theorem.  The premise is precisely convergence of finite-stage
posterior means to the limiting posterior mean in mean square. -/
theorem conditional_innovation_series_of_hilbert_levy_upward
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration ℕ mOmega)
    (K : Omega → H) (hK : MemLp K 2 mu)
    (hLevy : Tendsto
      (fun m => ∫ omega,
        ‖posteriorMean mu (filtrationLimit filtration) K omega -
          posteriorMean mu (filtration m) K omega‖ ^ 2 ∂mu)
      atTop (nhds 0))
    (n : ℕ) :
    ∀ᵐ omega ∂mu, Tendsto
      (fun k => conditionalInnovationPartialSum mu filtration K n k omega)
      atTop
      (nhds (hilbertLimitRefinementGain mu filtration K n omega)) := by
  have hShift : Tendsto
      (fun k => ∫ omega,
        ‖posteriorMean mu (filtrationLimit filtration) K omega -
          posteriorMean mu (filtration (n + k)) K omega‖ ^ 2 ∂mu)
      atTop (nhds 0) := by
    have h := hLevy.comp (tendsto_add_atTop_nat n)
    change Tendsto
      (fun k => ∫ omega,
        ‖posteriorMean mu (filtrationLimit filtration) K omega -
          posteriorMean mu (filtration (k + n)) K omega‖ ^ 2 ∂mu)
      atTop (nhds 0) at h
    simpa only [Nat.add_comm] using h
  apply conditional_innovation_series_of_residual_convergence
    mu filtration K hK n
  simpa only [integral_hilbertLimitRefinementGain_eq_mean_error
    mu filtration K hK] using hShift

/-- Full conditional almost-sure innovation-series theorem.  Hilbert-valued
Lévy upward convergence is supplied by `hilbert_posteriorMean_L2_upward`, so
no residual-convergence hypothesis remains. -/
theorem conditional_innovation_series
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration ℕ mOmega)
    (K : Omega → H) (hK : MemLp K 2 mu) (n : ℕ) :
    ∀ᵐ omega ∂mu, Tendsto
      (fun k => conditionalInnovationPartialSum mu filtration K n k omega)
      atTop
      (nhds (hilbertLimitRefinementGain mu filtration K n omega)) := by
  exact conditional_innovation_series_of_hilbert_levy_upward
    mu filtration K hK
      (hilbert_posteriorMean_L2_upward mu filtration K hK) n

/-- If expected residual reducible variance vanishes, the expected limiting
gain is the convergent series of expected innovation energies. -/
theorem predictable_innovation_series_of_residual_convergence
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration ℕ mOmega)
    (K : Omega → H) (hK : MemLp K 2 mu) (n : ℕ)
    (hResidual : Tendsto
      (fun k => ∫ omega,
        hilbertLimitRefinementGain mu filtration K (n + k) omega ∂mu)
      atTop (𝓝 0)) :
    Tendsto
      (fun k => ∑ j ∈ Finset.range k,
        ∫ omega,
          predictableInnovationEnergy mu filtration K (n + j) omega ∂mu)
      atTop
      (𝓝 (∫ omega,
        hilbertLimitRefinementGain mu filtration K n omega ∂mu)) := by
  have hTelescope := finite_predictable_innovation_telescope
    mu filtration K hK n
  have hPartial : (fun k => ∑ j ∈ Finset.range k,
      ∫ omega,
        predictableInnovationEnergy mu filtration K (n + j) omega ∂mu) =
      fun k =>
        (∫ omega, hilbertLimitRefinementGain mu filtration K n omega ∂mu) -
          ∫ omega,
            hilbertLimitRefinementGain mu filtration K (n + k) omega ∂mu := by
    funext k
    have := hTelescope k
    linarith
  rw [hPartial]
  simpa using tendsto_const_nhds.sub hResidual

/-- Zero limiting posterior variance is equivalent to measurability of the
target with respect to the limiting information state. -/
theorem posteriorVariance_limit_eq_zero_iff_aestronglyMeasurable
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration ℕ mOmega)
    (K : Omega → H) (hK : MemLp K 2 mu) :
    posteriorVariance mu (filtrationLimit filtration) K =ᵐ[mu] 0 ↔
      AEStronglyMeasurable[filtrationLimit filtration] K mu := by
  let mLimit := filtrationLimit filtration
  let R : Omega → H := K - posteriorMean mu mLimit K
  let Q : Omega → ℝ := fun omega => ‖R omega‖ ^ 2
  have hOneTwo : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hKInt : Integrable K mu := hK.integrable hOneTwo
  have hR : MemLp R 2 mu := by
    exact hK.sub (hK.condExp hOneTwo)
  have hQInt : Integrable Q mu :=
    (memLp_two_iff_integrable_sq_norm hR.1).mp hR
  have hVariance : posteriorVariance mu mLimit K = mu[Q | mLimit] := by
    rfl
  constructor
  · intro hZero
    have hCondZero : mu[Q | mLimit] =ᵐ[mu] 0 := by
      rw [← hVariance]
      exact hZero
    have hIntegralZero : ∫ omega, Q omega ∂mu = 0 := by
      calc
        ∫ omega, Q omega ∂mu =
            ∫ omega, mu[Q | mLimit] omega ∂mu :=
          (integral_condExp (filtrationLimit_le_ambient filtration)).symm
        _ = ∫ _omega, (0 : ℝ) ∂mu := integral_congr_ae hCondZero
        _ = 0 := by simp
    have hQZero : Q =ᵐ[mu] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae
        (Filter.Eventually.of_forall fun omega => sq_nonneg _) hQInt).1
        hIntegralZero
    have hRZero : R =ᵐ[mu] 0 := by
      filter_upwards [hQZero] with omega homega
      change Q omega = (0 : ℝ) at homega
      have : ‖R omega‖ = 0 := by nlinarith [norm_nonneg (R omega)]
      exact norm_eq_zero.mp this
    have hKCond : K =ᵐ[mu] posteriorMean mu mLimit K := by
      filter_upwards [hRZero] with omega homega
      change K omega - posteriorMean mu mLimit K omega = 0 at homega
      exact sub_eq_zero.mp homega
    exact stronglyMeasurable_condExp.aestronglyMeasurable.congr hKCond.symm
  · intro hMeasurable
    have hCondK : posteriorMean mu mLimit K =ᵐ[mu] K :=
      condExp_of_aestronglyMeasurable'
        (filtrationLimit_le_ambient filtration) hMeasurable hKInt
    have hQZero : Q =ᵐ[mu] 0 := by
      filter_upwards [hCondK] with omega homega
      have hRomega : R omega = 0 := by
        change K omega - posteriorMean mu mLimit K omega = 0
        exact sub_eq_zero.mpr homega.symm
      simp [Q, hRomega]
    rw [hVariance]
    simpa only [condExp_zero] using condExp_congr_ae hQZero

/-- Predictable irreducible variance vanishes exactly when the terminal
target is measurable from the limiting information state. -/
theorem predictableIrreducibleVariance_eq_zero_iff
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration ℕ mOmega)
    (K : Omega → H) (hK : MemLp K 2 mu) (n : ℕ) :
    predictableIrreducibleVariance mu filtration K n =ᵐ[mu] 0 ↔
      AEStronglyMeasurable[filtrationLimit filtration] K mu := by
  let V := posteriorVariance mu (filtrationLimit filtration) K
  have hVInt : Integrable V mu := by
    dsimp only [V, posteriorVariance, posteriorMSE]
    exact integrable_condExp
  have hVNonnegative : 0 ≤ᵐ[mu] V := by
    dsimp only [V]
    exact posteriorMSE_nonnegative mu (filtrationLimit filtration) K K
  have hFaithful : mu[V | filtration n] =ᵐ[mu] 0 ↔ V =ᵐ[mu] 0 := by
    constructor
    · intro hCondZero
      have hIntegralZero : ∫ omega, V omega ∂mu = 0 := by
        calc
          ∫ omega, V omega ∂mu =
              ∫ omega, mu[V | filtration n] omega ∂mu :=
            (integral_condExp (filtration.le n)).symm
          _ = ∫ _omega, (0 : ℝ) ∂mu := integral_congr_ae hCondZero
          _ = 0 := by simp
      exact (integral_eq_zero_iff_of_nonneg_ae hVNonnegative hVInt).1
        hIntegralZero
    · intro hZero
      simpa only [condExp_zero] using condExp_congr_ae hZero
  change mu[V | filtration n] =ᵐ[mu] 0 ↔ _
  rw [hFaithful]
  exact posteriorVariance_limit_eq_zero_iff_aestronglyMeasurable
    mu filtration K hK

end ReducibleIrreducible

end

end SequentialLearning
