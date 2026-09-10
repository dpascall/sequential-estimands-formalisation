import SequentialLearning.NoisyObservationModels
import SequentialLearning.RotationFamilyProperties
import SequentialLearning.StructuralWitnesses
import SequentialLearning.HilbertOracleRCD
import SequentialLearning.PosteriorDisplacementInfrastructure
import SequentialLearning.ProbabilisticExactCriterion
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Probability.CondVar
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# Same-estimand impossibility construction

This module repairs the separation in the earlier Phase 3 endpoint.  It puts a
rotation-family value path inside every non-fixed structural witness, uses the
same flag-valued estimand under an uninformative and a noisy generated
filtration, constructs its canonical regular conditional laws, and computes
the corresponding Frechet variances.  The existing spare branch bit is the
unobserved orthogonal Rademacher coordinate, so no enlargement of the finite
256-state latent space is required.
-/

namespace SequentialLearning

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal MeasureTheory ProbabilityTheory

noncomputable section

section HilbertProbabilityVariance

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Real H]
  [CompleteSpace H] [MeasurableSpace H] [OpensMeasurableSpace H]

/-- A Hilbert-valued probability law supported on the unit sphere has
variance `1 - ‖mean‖²`.  This is the convenient kernel-level form used by the
finite rotation counterexample. -/
theorem hilbertMeasureVarianceReal_eq_one_sub_norm_sq
    (nu : Measure H) [IsProbabilityMeasure nu]
    (hnu : MemLp (id : H -> H) 2 nu)
    (hunit : ∀ᵐ x ∂nu, ‖x‖ = 1) :
    hilbertMeasureVarianceReal nu = 1 - ‖hilbertMeasureMean nu‖ ^ 2 := by
  have hrisk := frechetRiskReal_eq_hilbertBranchRisk nu hnu (0 : H)
  have hriskOne : frechetRiskReal nu (0 : H) = 1 := by
    rw [frechetRiskReal, frechetRisk_eq_lintegral]
    have hintegral :
        (∫⁻ x, ENNReal.ofReal (dist x (0 : H) ^ 2) ∂nu) = 1 := by
      calc
        _ = ∫⁻ _x : H, (1 : ENNReal) ∂nu := by
          apply lintegral_congr_ae
          filter_upwards [hunit] with x hx
          simp [dist_eq_norm, hx]
        _ = 1 := by simp
    rw [hintegral]
    norm_num
  rw [hriskOne] at hrisk
  simp only [hilbertBranchRisk, zero_sub, norm_neg] at hrisk
  linarith

end HilbertProbabilityVariance

section CanonicalConditionalLaw

variable {Omega S : Type*} [mOmega : MeasurableSpace Omega]
  [sbOmega : StandardBorelSpace Omega] [mS : MeasurableSpace S]

/-- The canonical regular conditional law obtained by mapping Mathlib's
conditional-expectation kernel. -/
def canonicalConditionalLaw (mu : Measure[mOmega] Omega) [IsFiniteMeasure mu]
    (m : MeasurableSpace Omega) (X : Omega -> S) : Kernel[m] Omega S :=
  @Kernel.map Omega Omega m mOmega S
    mS
    (@condExpKernel Omega mOmega sbOmega
      mu (inferInstance : IsFiniteMeasure mu) m) X

theorem canonicalConditionalLaw_isRCD
    (mu : Measure[mOmega] Omega) [IsProbabilityMeasure mu]
    (m : MeasurableSpace Omega) (hm : m ≤ mOmega)
    (X : Omega -> S) (hX : Measurable[mOmega] X) :
    @IsRegularConditionalLaw Omega S mOmega
      mS mu m hm X
      (canonicalConditionalLaw (mOmega := mOmega) mu m X) := by
  rw [IsRegularConditionalLaw]
  change (mu.trim hm) ⊗ₘ
      (@Kernel.map Omega Omega m mOmega S
        mS
        (@condExpKernel Omega mOmega
          sbOmega mu
          (inferInstance : IsFiniteMeasure mu) m) X) = _
  rw [@Measure.compProd_map Omega Omega S m mOmega
    mS (mu.trim hm)
    (@condExpKernel Omega mOmega
      sbOmega mu
      (inferInstance : IsFiniteMeasure mu) m)
    (inferInstance : SFinite (mu.trim hm))
    (inferInstance : IsSFiniteKernel
      (@condExpKernel Omega mOmega
        sbOmega mu
        (inferInstance : IsFiniteMeasure mu) m)) X hX]
  rw [@compProd_trim_condExpKernel Omega m mOmega sbOmega mu
    (inferInstance : IsFiniteMeasure mu) hm]
  have hdiag : Measurable[mOmega, m.prod mOmega]
      (fun omega : Omega => (omega, omega)) :=
    (measurable_id'' hm).prodMk measurable_id
  rw [@Measure.map_map Omega (Omega × Omega) (Omega × S)
    mOmega (m.prod mOmega) (m.prod mS) mu
    (Prod.map id X) (Function.diag : Omega -> Omega × Omega)
    (measurable_id.prodMap hX) hdiag]
  rfl

end CanonicalConditionalLaw

section

variable {Omega : Type*} [Fintype Omega] [Nonempty Omega]
  [mOmega : MeasurableSpace Omega] [MeasurableSingletonClass Omega]

variable {Beta : Type*} [Fintype Beta] [DecidableEq Beta]

def fiber (Y : Omega -> Beta) (b : Beta) : Finset Omega :=
  Finset.univ.filter fun x => Y x = b

def fiberMeanAt (Y : Omega -> Beta) (f : Omega -> Real) (b : Beta) : Real :=
  ((fiber Y b).card : Real)⁻¹ * (fiber Y b).sum f

def fiberMean (Y : Omega -> Beta) (f : Omega -> Real) (x : Omega) : Real :=
  fiberMeanAt Y f (Y x)

theorem finite_fiberMean_sum (Y : Omega -> Beta) (f : Omega -> Real)
    (t : Finset Beta) :
    (∑ x ∈ Finset.univ with Y x ∈ t, fiberMean Y f x) =
      ∑ x ∈ Finset.univ with Y x ∈ t, f x := by
  simp only [fiberMean]
  rw [← Finset.sum_fiberwise_eq_sum_filter' Finset.univ t Y
      (fiberMeanAt Y f),
    ← Finset.sum_fiberwise_eq_sum_filter Finset.univ t Y f]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_const]
  simp only [nsmul_eq_mul, fiberMeanAt, fiber]
  by_cases hcard : (Finset.univ.filter fun x => Y x = b).card = 0
  · have hempty : (Finset.univ.filter fun x => Y x = b) = ∅ :=
      Finset.card_eq_zero.mp hcard
    simp [hempty]
  · rw [← mul_assoc, mul_inv_cancel₀]
    · simp
    · exact_mod_cast hcard

theorem integral_uniformOn_univ (f : Omega -> Real) :
    (∫ x, f x ∂uniformOn (Set.univ : Set Omega)) =
      (Fintype.card Omega : Real)⁻¹ * Finset.univ.sum f := by
  have hf : Integrable f (uniformOn (Set.univ : Set Omega)) :=
    MeasureTheory.Integrable.of_finite
  rw [integral_fintype hf]
  simp_rw [measureReal_def, uniformOn_univ]
  simp [ENNReal.toReal_div, Finset.mul_sum]

theorem setIntegral_uniformOn_univ (f : Omega -> Real) (s : Finset Omega) :
    (∫ x in (s : Set Omega), f x ∂uniformOn (Set.univ : Set Omega)) =
      (Fintype.card Omega : Real)⁻¹ *
        (s.sum f) := by
  have hf : IntegrableOn f (s : Set Omega)
      (uniformOn (Set.univ : Set Omega)) :=
    MeasureTheory.Integrable.of_finite
  rw [setIntegral_finset s hf]
  simp_rw [measureReal_def, uniformOn_univ]
  simp [Finset.mul_sum]

theorem fiberMean_ae_eq_condExp
    (Y : Omega -> Beta)
    (hY : @Measurable Omega Beta inferInstance (⊤ : MeasurableSpace Beta) Y)
    (f : Omega -> Real) :
    fiberMean Y f =ᵐ[uniformOn (Set.univ : Set Omega)]
      (uniformOn (Set.univ : Set Omega))[f |
        MeasurableSpace.comap Y (⊤ : MeasurableSpace Beta)] := by
  classical
  let mu : Measure Omega := uniformOn Set.univ
  let m : MeasurableSpace Omega :=
    MeasurableSpace.comap Y (⊤ : MeasurableSpace Beta)
  have hf : Integrable f mu := Integrable.of_finite
  change fiberMean Y f =ᵐ[mu] mu[f | m]
  refine ae_eq_condExp_of_forall_setIntegral_eq (μ := mu) (m := m)
    (g := fiberMean Y f) hY.comap_le hf ?_ ?_ ?_
  · intro s hs hfinite
    exact Integrable.of_finite
  · intro s hs hfinite
    rcases (MeasurableSpace.measurableSet_comap.mp hs) with ⟨t, ht, rfl⟩
    let tf : Finset Beta := Finset.univ.filter fun b => b ∈ t
    let sf : Finset Omega := Finset.univ.filter fun x => Y x ∈ t
    have hpreimage : Y ⁻¹' t = (sf : Set Omega) := by
      ext x
      simp [sf]
    rw [hpreimage]
    have hleft :
        (∫ x in (sf : Set Omega), fiberMean Y f x ∂mu) =
          (Fintype.card Omega : Real)⁻¹ * sf.sum (fiberMean Y f) := by
      dsimp only [mu]
      exact @setIntegral_uniformOn_univ Omega inferInstance inferInstance
        mOmega inferInstance (fiberMean Y f) sf
    have hright :
        (∫ x in (sf : Set Omega), f x ∂mu) =
          (Fintype.card Omega : Real)⁻¹ * sf.sum f := by
      dsimp only [mu]
      exact @setIntegral_uniformOn_univ Omega inferInstance inferInstance
        mOmega inferInstance f sf
    rw [hleft, hright]
    congr 1
    change (Finset.univ.filter fun x => Y x ∈ t).sum (fiberMean Y f) =
      (Finset.univ.filter fun x => Y x ∈ t).sum f
    have htf : (Finset.univ.filter fun x => Y x ∈ t) =
        Finset.univ.filter fun x => Y x ∈ tf := by
      ext x
      simp [tf]
    rw [htf]
    exact @finite_fiberMean_sum Omega inferInstance inferInstance mOmega
      inferInstance Beta inferInstance inferInstance Y f tf
  · have havg : @Measurable Beta Real (⊤ : MeasurableSpace Beta)
        inferInstance (fiberMeanAt Y f) := measurable_from_top
    exact (havg.comp (Measurable.of_comap_le le_rfl)).aestronglyMeasurable

end

end

namespace NoisyObservationModel

theorem ae_eq_pointwise_latent {A : Type*} {f g : LatentState -> A}
    (h : f =ᵐ[latentLaw] g) : f = g := by
  funext omega
  exact (ae_iff_of_countable.mp h) omega
    (ne_of_gt (StructuralWitnesses.singleton_mu_pos omega))

def hiddenSignReal (omega : LatentState) : Real :=
  if omega.truth then 1 else -1

def hiddenSignRat (omega : LatentState) : Rat :=
  if omega.truth then 1 else -1

def fiberMeanAtRat {Beta : Type*} [DecidableEq Beta]
    (Y : LatentState -> Beta) (f : LatentState -> Rat) (b : Beta) : Rat :=
  ((Finset.univ.filter fun x => Y x = b).card : Rat)⁻¹ *
    (Finset.univ.filter fun x => Y x = b).sum f

def latentEquiv : LatentState ≃ Bool × Fin 4 × Fin 16 × Bool where
  toFun omega := (omega.truth, omega.noise1, omega.noise2, omega.branch)
  invFun p :=
    { truth := p.1
      noise1 := p.2.1
      noise2 := p.2.2.1
      branch := p.2.2.2 }
  left_inv := by intro omega; cases omega; rfl
  right_inv := by intro p; rcases p with ⟨a, b, c, d⟩; rfl

set_option maxRecDepth 100000 in
theorem one_fiber_card (b : Bool) :
    (Finset.univ.filter fun x : LatentState => oneObservation x = b).card = 128 := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Fintype.sum_equiv latentEquiv
    (fun x : LatentState => if oneObservation x = b then 1 else 0)
    (fun p : Bool × Fin 4 × Fin 16 × Bool =>
      if oneObservation (latentEquiv.symm p) = b then 1 else 0)]
  · fin_cases b <;>
      norm_num [latentEquiv, oneObservation, firstSignal,
        Fintype.sum_prod_type, Fin.sum_univ_succ]
  · intro x
    rfl

set_option maxRecDepth 100000 in
theorem one_fiber_sum (b : Bool) :
    (Finset.univ.filter fun x : LatentState => oneObservation x = b).sum
      hiddenSignRat = if b then 64 else -64 := by
  rw [Finset.sum_filter]
  rw [Fintype.sum_equiv latentEquiv
    (fun x : LatentState => if oneObservation x = b then hiddenSignRat x else 0)
    (fun p : Bool × Fin 4 × Fin 16 × Bool =>
      if oneObservation (latentEquiv.symm p) = b
      then hiddenSignRat (latentEquiv.symm p) else 0)]
  · fin_cases b <;>
      norm_num [latentEquiv, oneObservation, firstSignal, hiddenSignRat,
        Fintype.sum_prod_type, Fin.sum_univ_succ]
  · intro x
    rfl

set_option maxRecDepth 100000 in
theorem fiberMeanAtRat_one_eq (b : Bool) :
    fiberMeanAtRat oneObservation hiddenSignRat b =
      if b then (1 / 2 : Rat) else -1 / 2 := by
  rw [fiberMeanAtRat, one_fiber_card, one_fiber_sum]
  fin_cases b <;> norm_num

set_option maxRecDepth 100000 in
theorem two_fiber_card (b : Bool × Bool) :
    (Finset.univ.filter fun x : LatentState => twoObservations x = b).card =
      if b.1 = b.2 then 68 else 60 := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Fintype.sum_equiv latentEquiv
    (fun x : LatentState => if twoObservations x = b then 1 else 0)
    (fun p : Bool × Fin 4 × Fin 16 × Bool =>
      if twoObservations (latentEquiv.symm p) = b then 1 else 0)]
  · simp_rw [Fintype.sum_prod_type]
    rcases b with ⟨b1, b2⟩
    fin_cases b1 <;> fin_cases b2 <;>
      norm_num [latentEquiv, twoObservations, firstSignal, secondSignal,
        Fin.sum_univ_succ]
  · intro x
    rfl

set_option maxRecDepth 100000 in
theorem two_fiber_sum (b : Bool × Bool) :
    (Finset.univ.filter fun x : LatentState => twoObservations x = b).sum
      hiddenSignRat =
        if b = (true, true) then 40 else
        if b = (true, false) then 24 else
        if b = (false, true) then -24 else -40 := by
  rw [Finset.sum_filter]
  rw [Fintype.sum_equiv latentEquiv
    (fun x : LatentState => if twoObservations x = b then hiddenSignRat x else 0)
    (fun p : Bool × Fin 4 × Fin 16 × Bool =>
      if twoObservations (latentEquiv.symm p) = b
      then hiddenSignRat (latentEquiv.symm p) else 0)]
  · simp_rw [Fintype.sum_prod_type]
    rcases b with ⟨b1, b2⟩
    fin_cases b1 <;> fin_cases b2 <;>
      norm_num [latentEquiv, twoObservations, firstSignal, secondSignal,
        hiddenSignRat, Fin.sum_univ_succ]
  · intro x
    rfl

set_option maxRecDepth 100000 in
theorem fiberMeanAtRat_two_eq (b : Bool × Bool) :
    fiberMeanAtRat twoObservations hiddenSignRat b =
      posteriorMeanTwo b.1 b.2 := by
  rw [fiberMeanAtRat, two_fiber_card, two_fiber_sum]
  rcases b with ⟨b1, b2⟩
  fin_cases b1 <;> fin_cases b2 <;>
    norm_num [posteriorMeanTwo, evidenceTwo, priorWeight, likelihood,
      sign, q, q']

set_option maxRecDepth 100000 in
theorem fiberMeanAt_one_eq (b : Bool) :
    fiberMeanAt oneObservation hiddenSignReal b =
      if b then (1 / 2 : Real) else -1 / 2 := by
  rw [fiberMeanAt, fiber, one_fiber_card]
  have hsum :
      (Finset.univ.filter fun x : LatentState => oneObservation x = b).sum
          hiddenSignReal =
        ((Finset.univ.filter fun x : LatentState => oneObservation x = b).sum
          hiddenSignRat : Rat) := by
    rw [Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro x hx
    cases htruth : x.truth <;> simp [hiddenSignReal, hiddenSignRat, htruth]
  rw [hsum, one_fiber_sum]
  fin_cases b <;> norm_num

set_option maxRecDepth 100000 in
theorem fiberMeanAt_two_eq (b : Bool × Bool) :
    fiberMeanAt twoObservations hiddenSignReal b =
      (posteriorMeanTwo b.1 b.2 : Real) := by
  rw [fiberMeanAt, fiber, two_fiber_card]
  have hsum :
      (Finset.univ.filter fun x : LatentState => twoObservations x = b).sum
          hiddenSignReal =
        ((Finset.univ.filter fun x : LatentState => twoObservations x = b).sum
          hiddenSignRat : Rat) := by
    rw [Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro x hx
    cases htruth : x.truth <;> simp [hiddenSignReal, hiddenSignRat, htruth]
  rw [hsum, two_fiber_sum]
  rcases b with ⟨b1, b2⟩
  fin_cases b1 <;> fin_cases b2 <;>
    norm_num [posteriorMeanTwo, evidenceTwo, priorWeight, likelihood,
      sign, q, q']

theorem hiddenSignReal_memLp : MemLp hiddenSignReal 2 latentLaw := by
  apply MemLp.of_bound measurable_from_top.aestronglyMeasurable 1
  filter_upwards with omega
  cases htruth : omega.truth <;> simp [hiddenSignReal, htruth]

theorem condExp_hiddenSign_one :
    latentLaw[hiddenSignReal | generatedOne] =ᵐ[latentLaw]
      fun omega => (posteriorMeanOne (oneObservation omega) : Rat) := by
  have hfiber := fiberMean_ae_eq_condExp oneObservation
    (measurable_from_top : Measurable oneObservation) hiddenSignReal
  refine hfiber.symm.trans (Eventually.of_forall fun omega => ?_)
  simp only [fiberMean]
  rw [fiberMeanAt_one_eq]
  cases hobs : oneObservation omega <;>
    norm_num [posteriorMeanOne, evidenceOne, priorWeight, likelihood,
      sign, q, hobs]

theorem condExp_hiddenSign_two :
    latentLaw[hiddenSignReal | generatedTwo] =ᵐ[latentLaw]
      fun omega => (posteriorMeanTwo (twoObservations omega).1
        (twoObservations omega).2 : Rat) := by
  have hobs : @Measurable LatentState (Bool × Bool) inferInstance
      (⊤ : MeasurableSpace (Bool × Bool)) twoObservations := by
    intro s hs
    exact MeasurableSet.of_discrete
  have hfiber := fiberMean_ae_eq_condExp twoObservations hobs hiddenSignReal
  refine hfiber.symm.trans (Eventually.of_forall fun omega => ?_)
  simp only [fiberMean]
  exact fiberMeanAt_two_eq (twoObservations omega)

theorem hiddenSignReal_sq : hiddenSignReal ^ 2 = fun _ => 1 := by
  funext omega
  simp [hiddenSignReal]

theorem scalarConditionalVariance_one :
    scalarConditionalVariance latentLaw generatedOne hiddenSignReal =ᵐ[latentLaw]
      fun omega => (posteriorVarianceOne (oneObservation omega) : Rat) := by
  have hformula := condVar_ae_eq_condExp_sq_sub_sq_condExp
    (μ := latentLaw) (X := hiddenSignReal) (m := generatedOne)
    le_top hiddenSignReal_memLp
  have hsquareCE :
      latentLaw[hiddenSignReal ^ 2 | generatedOne] =ᵐ[latentLaw]
        fun _ => (1 : Real) := by
    have hcongr : hiddenSignReal ^ 2 =ᵐ[latentLaw] fun _ => (1 : Real) :=
      Eventually.of_forall (congrFun hiddenSignReal_sq)
    exact (condExp_congr_ae hcongr).trans
      (EventuallyEq.of_eq (condExp_const le_top 1))
  filter_upwards [hformula, hsquareCE, condExp_hiddenSign_one] with
    omega hformulaOmega hsquareOmega hmeanOmega
  change scalarConditionalVariance latentLaw generatedOne hiddenSignReal omega = _
  rw [show scalarConditionalVariance latentLaw generatedOne hiddenSignReal =
      Var[hiddenSignReal; latentLaw | generatedOne] by rfl]
  rw [hformulaOmega, Pi.sub_apply, Pi.pow_apply, hsquareOmega, hmeanOmega]
  norm_num [posteriorVarianceOne]

theorem scalarConditionalVariance_two :
    scalarConditionalVariance latentLaw generatedTwo hiddenSignReal =ᵐ[latentLaw]
      fun omega => (posteriorVarianceTwo (twoObservations omega).1
        (twoObservations omega).2 : Rat) := by
  have hformula := condVar_ae_eq_condExp_sq_sub_sq_condExp
    (μ := latentLaw) (X := hiddenSignReal) (m := generatedTwo)
    le_top hiddenSignReal_memLp
  have hsquareCE :
      latentLaw[hiddenSignReal ^ 2 | generatedTwo] =ᵐ[latentLaw]
        fun _ => (1 : Real) := by
    have hcongr : hiddenSignReal ^ 2 =ᵐ[latentLaw] fun _ => (1 : Real) :=
      Eventually.of_forall (congrFun hiddenSignReal_sq)
    exact (condExp_congr_ae hcongr).trans
      (EventuallyEq.of_eq (condExp_const le_top 1))
  filter_upwards [hformula, hsquareCE, condExp_hiddenSign_two] with
    omega hformulaOmega hsquareOmega hmeanOmega
  change scalarConditionalVariance latentLaw generatedTwo hiddenSignReal omega = _
  rw [show scalarConditionalVariance latentLaw generatedTwo hiddenSignReal =
      Var[hiddenSignReal; latentLaw | generatedTwo] by rfl]
  rw [hformulaOmega, Pi.sub_apply, Pi.pow_apply, hsquareOmega, hmeanOmega]
  norm_num [posteriorVarianceTwo]

def varianceTwoRat (omega : LatentState) : Rat :=
  posteriorVarianceTwo (twoObservations omega).1 (twoObservations omega).2

def varianceTwoReal (omega : LatentState) : Real :=
  (varianceTwoRat omega : Rat)

set_option maxRecDepth 100000 in
theorem one_fiber_varianceTwoRat_sum (b : Bool) :
    (Finset.univ.filter fun x : LatentState => oneObservation x = b).sum
      varianceTwoRat = 8064 / 85 := by
  rw [Finset.sum_filter]
  rw [Fintype.sum_equiv latentEquiv
    (fun x : LatentState => if oneObservation x = b then varianceTwoRat x else 0)
    (fun p : Bool × Fin 4 × Fin 16 × Bool =>
      if oneObservation (latentEquiv.symm p) = b
      then varianceTwoRat (latentEquiv.symm p) else 0)]
  · simp_rw [Fintype.sum_prod_type]
    fin_cases b <;>
      norm_num [latentEquiv, oneObservation, twoObservations, firstSignal,
        secondSignal, varianceTwoRat, posteriorVarianceTwo, posteriorMeanTwo,
        evidenceTwo, priorWeight, likelihood, sign, q, q', Fin.sum_univ_succ]
  · intro x
    rfl

theorem fiberMeanAt_varianceTwo_eq (b : Bool) :
    fiberMeanAt oneObservation varianceTwoReal b = 63 / 85 := by
  rw [fiberMeanAt, fiber, one_fiber_card]
  have hsum :
      (Finset.univ.filter fun x : LatentState => oneObservation x = b).sum
          varianceTwoReal =
        ((Finset.univ.filter fun x : LatentState => oneObservation x = b).sum
          varianceTwoRat : Rat) := by
    rw [Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rfl
  rw [hsum, one_fiber_varianceTwoRat_sum]
  norm_num

theorem condExp_varianceTwo_one :
    latentLaw[varianceTwoReal | generatedOne] =ᵐ[latentLaw]
      fun _ => (63 / 85 : Real) := by
  have hfiber := fiberMean_ae_eq_condExp oneObservation
    (measurable_from_top : Measurable oneObservation) varianceTwoReal
  refine hfiber.symm.trans (Eventually.of_forall fun omega => ?_)
  simp only [fiberMean]
  exact fiberMeanAt_varianceTwo_eq (oneObservation omega)

theorem condExp_scalarConditionalVariance_two_one :
    latentLaw[
      scalarConditionalVariance latentLaw generatedTwo hiddenSignReal |
        generatedOne] =ᵐ[latentLaw]
      fun _ => (63 / 85 : Real) := by
  exact (condExp_congr_ae scalarConditionalVariance_two).trans
    condExp_varianceTwo_one

def branchSignReal (omega : LatentState) : Real :=
  if omega.branch then 1 else -1

def branchSignRat (omega : LatentState) : Rat :=
  if omega.branch then 1 else -1

theorem branchSignReal_memLp : MemLp branchSignReal 2 latentLaw := by
  apply MemLp.of_bound measurable_from_top.aestronglyMeasurable 1
  filter_upwards with omega
  cases hbranch : omega.branch <;> simp [branchSignReal, hbranch]

theorem branchSignReal_sq : branchSignReal ^ 2 = fun _ => 1 := by
  funext omega
  cases hbranch : omega.branch <;> simp [branchSignReal, hbranch]

set_option maxRecDepth 100000 in
theorem one_fiber_branchSignRat_sum (b : Bool) :
    (Finset.univ.filter fun x : LatentState => oneObservation x = b).sum
      branchSignRat = 0 := by
  rw [Finset.sum_filter]
  rw [Fintype.sum_equiv latentEquiv
    (fun x : LatentState => if oneObservation x = b then branchSignRat x else 0)
    (fun p : Bool × Fin 4 × Fin 16 × Bool =>
      if oneObservation (latentEquiv.symm p) = b
      then branchSignRat (latentEquiv.symm p) else 0)]
  · simp_rw [Fintype.sum_prod_type]
    fin_cases b <;>
      norm_num [latentEquiv, oneObservation, firstSignal, branchSignRat,
        Fin.sum_univ_succ]
  · intro x
    rfl

set_option maxRecDepth 100000 in
theorem two_fiber_branchSignRat_sum (b : Bool × Bool) :
    (Finset.univ.filter fun x : LatentState => twoObservations x = b).sum
      branchSignRat = 0 := by
  rw [Finset.sum_filter]
  rw [Fintype.sum_equiv latentEquiv
    (fun x : LatentState => if twoObservations x = b then branchSignRat x else 0)
    (fun p : Bool × Fin 4 × Fin 16 × Bool =>
      if twoObservations (latentEquiv.symm p) = b
      then branchSignRat (latentEquiv.symm p) else 0)]
  · simp_rw [Fintype.sum_prod_type]
    rcases b with ⟨b1, b2⟩
    fin_cases b1 <;> fin_cases b2 <;>
      norm_num [latentEquiv, twoObservations, firstSignal, secondSignal,
        branchSignRat, Fin.sum_univ_succ]
  · intro x
    rfl

theorem fiberMeanAt_branchSign_one_eq (b : Bool) :
    fiberMeanAt oneObservation branchSignReal b = 0 := by
  rw [fiberMeanAt, fiber, one_fiber_card]
  have hsum :
      (Finset.univ.filter fun x : LatentState => oneObservation x = b).sum
          branchSignReal =
        ((Finset.univ.filter fun x : LatentState => oneObservation x = b).sum
          branchSignRat : Rat) := by
    rw [Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro x hx
    cases hbranch : x.branch <;> simp [branchSignReal, branchSignRat, hbranch]
  rw [hsum, one_fiber_branchSignRat_sum]
  norm_num

theorem fiberMeanAt_branchSign_two_eq (b : Bool × Bool) :
    fiberMeanAt twoObservations branchSignReal b = 0 := by
  rw [fiberMeanAt, fiber, two_fiber_card]
  have hsum :
      (Finset.univ.filter fun x : LatentState => twoObservations x = b).sum
          branchSignReal =
        ((Finset.univ.filter fun x : LatentState => twoObservations x = b).sum
          branchSignRat : Rat) := by
    rw [Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro x hx
    cases hbranch : x.branch <;> simp [branchSignReal, branchSignRat, hbranch]
  rw [hsum, two_fiber_branchSignRat_sum]
  split <;> norm_num

theorem condExp_branchSign_one :
    latentLaw[branchSignReal | generatedOne] =ᵐ[latentLaw] 0 := by
  have hfiber := fiberMean_ae_eq_condExp oneObservation
    (measurable_from_top : Measurable oneObservation) branchSignReal
  refine hfiber.symm.trans (Eventually.of_forall fun omega => ?_)
  simp [fiberMean, fiberMeanAt_branchSign_one_eq]

theorem condExp_branchSign_two :
    latentLaw[branchSignReal | generatedTwo] =ᵐ[latentLaw] 0 := by
  have hobs : @Measurable LatentState (Bool × Bool) inferInstance
      (⊤ : MeasurableSpace (Bool × Bool)) twoObservations := by
    intro s hs
    exact MeasurableSet.of_discrete
  have hfiber := fiberMean_ae_eq_condExp twoObservations hobs branchSignReal
  refine hfiber.symm.trans (Eventually.of_forall fun omega => ?_)
  simp [fiberMean, fiberMeanAt_branchSign_two_eq]

theorem scalarConditionalVariance_branch_one :
    scalarConditionalVariance latentLaw generatedOne branchSignReal =ᵐ[latentLaw]
      fun _ => 1 :=
  scalarConditionalVariance_rademacher latentLaw generatedOne le_top
    branchSignReal condExp_branchSign_one
    (Eventually.of_forall (congrFun branchSignReal_sq))

theorem scalarConditionalVariance_branch_two :
    scalarConditionalVariance latentLaw generatedTwo branchSignReal =ᵐ[latentLaw]
      fun _ => 1 :=
  scalarConditionalVariance_rademacher latentLaw generatedTwo le_top
    branchSignReal condExp_branchSign_two
    (Eventually.of_forall (congrFun branchSignReal_sq))

theorem integral_hiddenSignReal : ∫ omega, hiddenSignReal omega ∂latentLaw = 0 := by
  rw [latentLaw, integral_uniformOn_univ]
  have hsum : Finset.univ.sum hiddenSignReal =
      (Finset.univ.sum hiddenSignRat : Rat) := by
    rw [Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro x hx
    cases htruth : x.truth <;> simp [hiddenSignReal, hiddenSignRat, htruth]
  rw [hsum]
  have hrat : Finset.univ.sum hiddenSignRat = 0 := by
    rw [Fintype.sum_equiv latentEquiv hiddenSignRat
      (fun p : Bool × Fin 4 × Fin 16 × Bool => hiddenSignRat (latentEquiv.symm p))]
    · simp_rw [Fintype.sum_prod_type]
      norm_num [latentEquiv, hiddenSignRat, Fin.sum_univ_succ]
    · intro x
      rfl
  rw [hrat]
  norm_num

theorem integral_branchSignReal : ∫ omega, branchSignReal omega ∂latentLaw = 0 := by
  rw [latentLaw, integral_uniformOn_univ]
  have hsum : Finset.univ.sum branchSignReal =
      (Finset.univ.sum branchSignRat : Rat) := by
    rw [Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro x hx
    cases hbranch : x.branch <;> simp [branchSignReal, branchSignRat, hbranch]
  rw [hsum]
  have hrat : Finset.univ.sum branchSignRat = 0 := by
    rw [Fintype.sum_equiv latentEquiv branchSignRat
      (fun p : Bool × Fin 4 × Fin 16 × Bool => branchSignRat (latentEquiv.symm p))]
    · simp_rw [Fintype.sum_prod_type]
      norm_num [latentEquiv, branchSignRat, Fin.sum_univ_succ]
    · intro x
      rfl
  rw [hrat]
  norm_num

theorem condExp_hiddenSign_zero :
    latentLaw[hiddenSignReal | generatedZero] =ᵐ[latentLaw] 0 := by
  rw [generatedZero, condExp_bot, integral_hiddenSignReal]
  exact Eventually.of_forall fun _ => rfl

theorem condExp_branchSign_zero :
    latentLaw[branchSignReal | generatedZero] =ᵐ[latentLaw] 0 := by
  rw [generatedZero, condExp_bot, integral_branchSignReal]
  exact Eventually.of_forall fun _ => rfl

theorem scalarConditionalVariance_hidden_zero :
    scalarConditionalVariance latentLaw generatedZero hiddenSignReal =ᵐ[latentLaw]
      fun _ => 1 :=
  scalarConditionalVariance_rademacher latentLaw generatedZero le_top
    hiddenSignReal condExp_hiddenSign_zero
    (Eventually.of_forall (congrFun hiddenSignReal_sq))

theorem scalarConditionalVariance_branch_zero :
    scalarConditionalVariance latentLaw generatedZero branchSignReal =ᵐ[latentLaw]
      fun _ => 1 :=
  scalarConditionalVariance_rademacher latentLaw generatedZero le_top
    branchSignReal condExp_branchSign_zero
    (Eventually.of_forall (congrFun branchSignReal_sq))

end NoisyObservationModel

namespace SameEstimandImpossibility

open NoisyObservationModel

noncomputable section

abbrev HilbertTarget := EuclideanSpace Real (Fin 2)

instance : MeasurableSpace HilbertTarget := borel HilbertTarget
instance : BorelSpace HilbertTarget := ⟨rfl⟩

def eZ : HilbertTarget := EuclideanSpace.single 0 1
def eW : HilbertTarget := EuclideanSpace.single 1 1

theorem norm_eZ : ‖eZ‖ = 1 := by simp [eZ]
theorem norm_eW : ‖eW‖ = 1 := by simp [eW]
theorem inner_eZ_eW : inner Real eZ eW = 0 := by
  simp [eZ, eW, EuclideanSpace.inner_single_left]

theorem gamma_pi_div_two : rotationGamma (Real.pi / 2) = 0 := by
  simp [rotationGamma]

theorem gamma_pi_div_four : rotationGamma (Real.pi / 4) = 1 / 2 := by
  rw [rotationGamma, Real.cos_pi_div_four]
  have hsqrt : Real.sqrt 2 ^ 2 = 2 := by norm_num
  nlinarith

def oldRotation : LatentState -> HilbertTarget :=
  rotationEstimand (Real.pi / 2) branchSignReal hiddenSignReal eZ eW

def newRotation : LatentState -> HilbertTarget :=
  rotationEstimand (Real.pi / 4) branchSignReal hiddenSignReal eZ eW

def terminalRotation : LatentState -> HilbertTarget :=
  rotationLimit branchSignReal eZ

/-- The canonical Hilbert-valued regular conditional law obtained from
Mathlib's conditional-expectation kernel. -/
def hilbertLaw (m : MeasurableSpace LatentState)
    (X : LatentState -> HilbertTarget) :
    Kernel[m, (inferInstance : MeasurableSpace HilbertTarget)]
      LatentState HilbertTarget :=
  (condExpKernel
    (mΩ := instMeasurableSpaceLatentState) latentLaw m).map X

theorem hilbertLaw_mean_eq_posteriorMean
    (m : MeasurableSpace LatentState)
    (X : LatentState -> HilbertTarget) :
    (fun omega => hilbertMeasureMean (hilbertLaw m X omega)) =
      posteriorMean latentLaw m X := by
  have hmean := condExp_ae_eq_integral_condExpKernel
    (mΩ := instMeasurableSpaceLatentState) (μ := latentLaw)
    (m := m) le_top (Integrable.of_finite : Integrable X latentLaw)
  have hpoint := ae_eq_pointwise_latent hmean
  funext omega
  rw [hilbertLaw, Kernel.map_apply _ measurable_from_top]
  rw [hilbertMeasureMean]
  have hmap :
      (∫ x : HilbertTarget, x ∂@Measure.map LatentState HilbertTarget
          instMeasurableSpaceLatentState
          (inferInstance : MeasurableSpace HilbertTarget) X
          (condExpKernel
            (mΩ := instMeasurableSpaceLatentState) latentLaw m omega)) =
        ∫ x, X x ∂condExpKernel
          (mΩ := instMeasurableSpaceLatentState) latentLaw m omega :=
    integral_map measurable_from_top.aemeasurable
      measurable_id.aestronglyMeasurable
  rw [hmap]
  exact (congrFun hpoint omega).symm

theorem hilbertLaw_variance_eq_one_sub_norm_sq
    (m : MeasurableSpace LatentState)
    (X : LatentState -> HilbertTarget)
    (hunit : ∀ omega, ‖X omega‖ = 1) :
    posteriorFrechetVarianceReal m (hilbertLaw m X) =
      fun omega => 1 - ‖posteriorMean latentLaw m X omega‖ ^ 2 := by
  funext omega
  rw [posteriorFrechetVarianceReal]
  have hXmeas : @Measurable LatentState HilbertTarget
      instMeasurableSpaceLatentState
      (inferInstance : MeasurableSpace HilbertTarget) X := measurable_from_top
  letI : IsMarkovKernel (hilbertLaw m X) := by
    rw [hilbertLaw]
    exact Kernel.IsMarkovKernel.map _ hXmeas
  letI : IsProbabilityMeasure (hilbertLaw m X omega) :=
    IsMarkovKernel.isProbabilityMeasure omega
  have hbaseLp : MemLp X 2
      (condExpKernel
        (mΩ := instMeasurableSpaceLatentState) latentLaw m omega) := by
    apply MemLp.of_bound hXmeas.aestronglyMeasurable 1
    exact Eventually.of_forall fun x => by simp [hunit x]
  have hmapLp : MemLp (id : HilbertTarget -> HilbertTarget) 2
      (hilbertLaw m X omega) := by
    rw [hilbertLaw, Kernel.map_apply _ hXmeas]
    apply (memLp_map_measure_iff
      measurable_id.aestronglyMeasurable
      hXmeas.aemeasurable).2
    simpa [Function.comp_def] using hbaseLp
  rw [frechetVariance_toReal_eq_hilbertMeasureVarianceReal _ hmapLp]
  have hunitMap : ∀ᵐ y ∂hilbertLaw m X omega, ‖y‖ = 1 := by
    rw [hilbertLaw, Kernel.map_apply _ hXmeas]
    rw [ae_map_iff hXmeas.aemeasurable (by measurability)]
    exact Eventually.of_forall hunit
  rw [hilbertMeasureVarianceReal_eq_one_sub_norm_sq _ hmapLp hunitMap]
  rw [congrFun (hilbertLaw_mean_eq_posteriorMean m X) omega]

theorem oldRotation_norm (omega : LatentState) : ‖oldRotation omega‖ = 1 := by
  exact rotationEstimand_norm (Real.pi / 2) branchSignReal hiddenSignReal
    eZ eW norm_eZ norm_eW inner_eZ_eW
    (congrFun branchSignReal_sq) (congrFun hiddenSignReal_sq) omega

theorem newRotation_norm (omega : LatentState) : ‖newRotation omega‖ = 1 := by
  exact rotationEstimand_norm (Real.pi / 4) branchSignReal hiddenSignReal
    eZ eW norm_eZ norm_eW inner_eZ_eW
    (congrFun branchSignReal_sq) (congrFun hiddenSignReal_sq) omega

theorem oldVariance_one :
    posteriorVariance latentLaw generatedOne oldRotation =ᵐ[latentLaw]
      fun _ => (3 / 4 : Real) := by
  have h := rotation_posteriorVariance_formula latentLaw generatedOne le_top
    (Real.pi / 2) branchSignReal hiddenSignReal eZ eW norm_eZ norm_eW
    inner_eZ_eW branchSignReal_memLp hiddenSignReal_memLp
    condExp_branchSign_one
    (Eventually.of_forall (congrFun branchSignReal_sq))
  filter_upwards [h, scalarConditionalVariance_one] with omega hrot hvar
  rw [oldRotation, hrot, hvar, gamma_pi_div_two]
  rw [posteriorVarianceOne_eq]
  norm_num [rotationVariance]

theorem oldVariance_two :
    posteriorVariance latentLaw generatedTwo oldRotation =ᵐ[latentLaw]
      varianceTwoReal := by
  have h := rotation_posteriorVariance_formula latentLaw generatedTwo le_top
    (Real.pi / 2) branchSignReal hiddenSignReal eZ eW norm_eZ norm_eW
    inner_eZ_eW branchSignReal_memLp hiddenSignReal_memLp
    condExp_branchSign_two
    (Eventually.of_forall (congrFun branchSignReal_sq))
  filter_upwards [h, scalarConditionalVariance_two] with omega hrot hvar
  rw [oldRotation, hrot, hvar, gamma_pi_div_two]
  simp [rotationVariance, varianceTwoReal, varianceTwoRat]

theorem newVariance_two :
    posteriorVariance latentLaw generatedTwo newRotation =ᵐ[latentLaw]
      fun omega => rotationVariance (1 / 2) (varianceTwoReal omega) := by
  have h := rotation_posteriorVariance_formula latentLaw generatedTwo le_top
    (Real.pi / 4) branchSignReal hiddenSignReal eZ eW norm_eZ norm_eW
    inner_eZ_eW branchSignReal_memLp hiddenSignReal_memLp
    condExp_branchSign_two
    (Eventually.of_forall (congrFun branchSignReal_sq))
  filter_upwards [h, scalarConditionalVariance_two] with omega hrot hvar
  rw [newRotation, hrot, hvar, gamma_pi_div_four]
  rfl

theorem expectedNewVariance_two_given_one :
    latentLaw[posteriorVariance latentLaw generatedTwo newRotation |
      generatedOne] =ᵐ[latentLaw] fun _ => (74 / 85 : Real) := by
  have hcongr := condExp_congr_ae (m := generatedOne) newVariance_two
  have hvint : Integrable varianceTwoReal latentLaw := Integrable.of_finite
  have haffine := condExp_rotationVariance latentLaw generatedOne le_top
    (1 / 2) varianceTwoReal hvint
  filter_upwards [hcongr, haffine, condExp_varianceTwo_one] with
    omega hcongrOmega haffineOmega hvarOmega
  rw [hcongrOmega, haffineOmega, hvarOmega]
  norm_num [rotationVariance]

theorem expectedOldVariance_two_given_one :
    latentLaw[posteriorVariance latentLaw generatedTwo oldRotation |
      generatedOne] =ᵐ[latentLaw] fun _ => (63 / 85 : Real) := by
  exact (condExp_congr_ae (m := generatedOne) oldVariance_two).trans
    condExp_varianceTwo_one

/-- The finite noisy channel gives the manuscript's strict conditional
expected-increase verdict for the moving rotation target. -/
theorem noisy_rotation_verdict :
    ((fun omega =>
      latentLaw[posteriorVariance latentLaw generatedTwo newRotation |
          generatedOne] omega -
        posteriorVariance latentLaw generatedOne oldRotation omega) =ᵐ[latentLaw]
        fun _ => (41 / 340 : Real)) ∧
    (hilbertInformationTerm latentLaw generatedOne generatedTwo oldRotation =ᵐ[latentLaw]
      fun _ => (3 / 340 : Real)) := by
  constructor
  · filter_upwards [expectedNewVariance_two_given_one, oldVariance_one] with
      omega hnew hold
    rw [hnew, hold]
    norm_num
  · filter_upwards [oldVariance_one, expectedOldVariance_two_given_one] with
      omega hold hresolved
    simp only [hilbertInformationTerm, informationGain]
    rw [hold, hresolved]
    norm_num

theorem noisy_rotation_strict :
    (0 : Real) < 3 / 340 ∧ (3 / 340 : Real) < 44 / 340 ∧
      (0 : Real) < 41 / 340 := by norm_num

theorem oldVariance_zero :
    posteriorVariance latentLaw generatedZero oldRotation =ᵐ[latentLaw]
      fun _ => (1 : Real) := by
  have h := rotation_posteriorVariance_formula latentLaw generatedZero le_top
    (Real.pi / 2) branchSignReal hiddenSignReal eZ eW norm_eZ norm_eW
    inner_eZ_eW branchSignReal_memLp hiddenSignReal_memLp
    condExp_branchSign_zero
    (Eventually.of_forall (congrFun branchSignReal_sq))
  filter_upwards [h, scalarConditionalVariance_hidden_zero] with omega hrot hvar
  rw [oldRotation, hrot, hvar]
  simp [rotationVariance]

theorem newVariance_zero :
    posteriorVariance latentLaw generatedZero newRotation =ᵐ[latentLaw]
      fun _ => (1 : Real) := by
  have h := rotation_posteriorVariance_formula latentLaw generatedZero le_top
    (Real.pi / 4) branchSignReal hiddenSignReal eZ eW norm_eZ norm_eW
    inner_eZ_eW branchSignReal_memLp hiddenSignReal_memLp
    condExp_branchSign_zero
    (Eventually.of_forall (congrFun branchSignReal_sq))
  filter_upwards [h, scalarConditionalVariance_hidden_zero] with omega hrot hvar
  rw [newRotation, hrot, hvar]
  simp [rotationVariance]

theorem oldFrechetVariance_one :
    posteriorFrechetVarianceReal generatedOne
      (hilbertLaw generatedOne oldRotation) = fun _ => (3 / 4 : Real) := by
  rw [hilbertLaw_variance_eq_one_sub_norm_sq generatedOne oldRotation
    oldRotation_norm]
  have hrot := ae_eq_pointwise_latent
    (posteriorMean_rotationEstimand latentLaw generatedOne
      (Real.pi / 2) branchSignReal hiddenSignReal eZ eW
      branchSignReal_memLp hiddenSignReal_memLp)
  have hz := ae_eq_pointwise_latent condExp_branchSign_one
  have hw := ae_eq_pointwise_latent condExp_hiddenSign_one
  funext omega
  rw [show posteriorMean latentLaw generatedOne oldRotation omega =
      ((Real.cos (Real.pi / 2) *
          latentLaw[branchSignReal | generatedOne] omega) • eZ +
        (Real.sin (Real.pi / 2) *
          latentLaw[hiddenSignReal | generatedOne] omega) • eW) by
      simpa only [oldRotation] using congrFun hrot omega]
  rw [congrFun hz omega, congrFun hw omega]
  cases hobs : oneObservation omega <;>
    norm_num [posteriorMeanOne, evidenceOne, priorWeight, likelihood,
      sign, q, hobs, norm_smul, norm_eW]

theorem oldFrechetVariance_two :
    posteriorFrechetVarianceReal generatedTwo
      (hilbertLaw generatedTwo oldRotation) = varianceTwoReal := by
  rw [hilbertLaw_variance_eq_one_sub_norm_sq generatedTwo oldRotation
    oldRotation_norm]
  have hrot := ae_eq_pointwise_latent
    (posteriorMean_rotationEstimand latentLaw generatedTwo
      (Real.pi / 2) branchSignReal hiddenSignReal eZ eW
      branchSignReal_memLp hiddenSignReal_memLp)
  have hz := ae_eq_pointwise_latent condExp_branchSign_two
  have hw := ae_eq_pointwise_latent condExp_hiddenSign_two
  funext omega
  rw [show posteriorMean latentLaw generatedTwo oldRotation omega =
      ((Real.cos (Real.pi / 2) *
          latentLaw[branchSignReal | generatedTwo] omega) • eZ +
        (Real.sin (Real.pi / 2) *
          latentLaw[hiddenSignReal | generatedTwo] omega) • eW) by
      simpa only [oldRotation] using congrFun hrot omega]
  rw [congrFun hz omega, congrFun hw omega]
  rcases hobs : twoObservations omega with ⟨b1, b2⟩
  fin_cases b1 <;> fin_cases b2 <;>
    norm_num [varianceTwoReal, varianceTwoRat, posteriorVarianceTwo,
      posteriorMeanTwo, evidenceTwo, priorWeight, likelihood, sign, q, q',
      hobs, norm_smul, norm_eW]

theorem newFrechetVariance_two :
    posteriorFrechetVarianceReal generatedTwo
      (hilbertLaw generatedTwo newRotation) =
        fun omega => rotationVariance (1 / 2) (varianceTwoReal omega) := by
  rw [hilbertLaw_variance_eq_one_sub_norm_sq generatedTwo newRotation
    newRotation_norm]
  have hrot := ae_eq_pointwise_latent
    (posteriorMean_rotationEstimand latentLaw generatedTwo
      (Real.pi / 4) branchSignReal hiddenSignReal eZ eW
      branchSignReal_memLp hiddenSignReal_memLp)
  have hz := ae_eq_pointwise_latent condExp_branchSign_two
  have hw := ae_eq_pointwise_latent condExp_hiddenSign_two
  funext omega
  rw [show posteriorMean latentLaw generatedTwo newRotation omega =
      ((Real.cos (Real.pi / 4) *
          latentLaw[branchSignReal | generatedTwo] omega) • eZ +
        (Real.sin (Real.pi / 4) *
          latentLaw[hiddenSignReal | generatedTwo] omega) • eW) by
      simpa only [newRotation] using congrFun hrot omega]
  rw [congrFun hz omega, congrFun hw omega]
  rcases hobs : twoObservations omega with ⟨b1, b2⟩
  fin_cases b1 <;> fin_cases b2 <;>
    norm_num [varianceTwoReal, varianceTwoRat, rotationVariance,
      posteriorVarianceTwo, posteriorMeanTwo, evidenceTwo, priorWeight,
      likelihood, sign, q, q', hobs, norm_smul, norm_eW,
      abs_of_nonneg (Real.sqrt_nonneg 2)] <;>
    nlinarith [Real.sq_sqrt (show (0 : Real) ≤ 2 by norm_num)]

theorem oldFrechetVariance_zero :
    posteriorFrechetVarianceReal generatedZero
      (hilbertLaw generatedZero oldRotation) = fun _ => (1 : Real) := by
  rw [hilbertLaw_variance_eq_one_sub_norm_sq generatedZero oldRotation
    oldRotation_norm]
  have hrot := ae_eq_pointwise_latent
    (posteriorMean_rotationEstimand latentLaw generatedZero
      (Real.pi / 2) branchSignReal hiddenSignReal eZ eW
      branchSignReal_memLp hiddenSignReal_memLp)
  have hz := ae_eq_pointwise_latent condExp_branchSign_zero
  have hw := ae_eq_pointwise_latent condExp_hiddenSign_zero
  funext omega
  rw [show posteriorMean latentLaw generatedZero oldRotation omega =
      ((Real.cos (Real.pi / 2) *
          latentLaw[branchSignReal | generatedZero] omega) • eZ +
        (Real.sin (Real.pi / 2) *
          latentLaw[hiddenSignReal | generatedZero] omega) • eW) by
      simpa only [oldRotation] using congrFun hrot omega]
  rw [congrFun hz omega, congrFun hw omega]
  norm_num

theorem newFrechetVariance_zero :
    posteriorFrechetVarianceReal generatedZero
      (hilbertLaw generatedZero newRotation) = fun _ => (1 : Real) := by
  rw [hilbertLaw_variance_eq_one_sub_norm_sq generatedZero newRotation
    newRotation_norm]
  have hrot := ae_eq_pointwise_latent
    (posteriorMean_rotationEstimand latentLaw generatedZero
      (Real.pi / 4) branchSignReal hiddenSignReal eZ eW
      branchSignReal_memLp hiddenSignReal_memLp)
  have hz := ae_eq_pointwise_latent condExp_branchSign_zero
  have hw := ae_eq_pointwise_latent condExp_hiddenSign_zero
  funext omega
  rw [show posteriorMean latentLaw generatedZero newRotation omega =
      ((Real.cos (Real.pi / 4) *
          latentLaw[branchSignReal | generatedZero] omega) • eZ +
        (Real.sin (Real.pi / 4) *
          latentLaw[hiddenSignReal | generatedZero] omega) • eW) by
      simpa only [newRotation] using congrFun hrot omega]
  rw [congrFun hz omega, congrFun hw omega]
  norm_num

theorem terminalRotation_norm (omega : LatentState) :
    ‖terminalRotation omega‖ = 1 := by
  rw [terminalRotation, rotationLimit, alongDirection, norm_smul, norm_eZ]
  cases hbranch : omega.branch <;>
    simp [branchSignReal, hbranch]

theorem terminalFrechetVariance_zero :
    posteriorFrechetVarianceReal generatedZero
      (hilbertLaw generatedZero terminalRotation) = fun _ => (1 : Real) := by
  rw [hilbertLaw_variance_eq_one_sub_norm_sq generatedZero terminalRotation
    terminalRotation_norm]
  have hmean := ae_eq_pointwise_latent
    (condExp_alongDirection (H := HilbertTarget) latentLaw generatedZero
      branchSignReal eZ
      (branchSignReal_memLp.integrable (by norm_num : (1 : ENNReal) ≤ 2)))
  have hz := ae_eq_pointwise_latent condExp_branchSign_zero
  funext omega
  rw [show posteriorMean latentLaw generatedZero terminalRotation omega =
      latentLaw[branchSignReal | generatedZero] omega • eZ by
      simpa only [posteriorMean, terminalRotation, rotationLimit] using
        congrFun hmean omega]
  rw [congrFun hz omega]
  norm_num

/-- With no information at either side of the same rotation step, posterior
variance remains one and the old-target information gain is zero. -/
theorem uninformative_rotation_verdict :
    ((fun omega =>
      latentLaw[posteriorVariance latentLaw generatedZero newRotation |
          generatedZero] omega -
        posteriorVariance latentLaw generatedZero oldRotation omega) =ᵐ[latentLaw]
        fun _ => (0 : Real)) ∧
    (hilbertInformationTerm latentLaw generatedZero generatedZero oldRotation =ᵐ[latentLaw]
      fun _ => (0 : Real)) := by
  have hcondNew :
      latentLaw[posteriorVariance latentLaw generatedZero newRotation |
        generatedZero] =ᵐ[latentLaw] fun _ => (1 : Real) := by
    exact (condExp_congr_ae (m := generatedZero) newVariance_zero).trans
      (EventuallyEq.of_eq (condExp_const le_top 1))
  have hcondOld :
      latentLaw[posteriorVariance latentLaw generatedZero oldRotation |
        generatedZero] =ᵐ[latentLaw] fun _ => (1 : Real) := by
    exact (condExp_congr_ae (m := generatedZero) oldVariance_zero).trans
      (EventuallyEq.of_eq (condExp_const le_top 1))
  constructor
  · filter_upwards [hcondNew, oldVariance_zero] with omega hnew hold
    rw [hnew, hold]
    norm_num
  · filter_upwards [oldVariance_zero, hcondOld] with omega hold hresolved
    simp only [hilbertInformationTerm, informationGain]
    rw [hold, hresolved]
    norm_num

open HypotheticalSequentialEstimand
open HypotheticalSequentialEstimand.StructuralPresentation

abbrev Omega := LatentState
abbrev Target := FlagSpace HilbertTarget
abbrev Prefix := Unit

def mu : Measure Omega := latentLaw

instance : IsProbabilityMeasure mu := by
  dsimp [mu]
  infer_instance

def limitValue (omega : Omega) : Target :=
  ⟨terminalRotation omega, true⟩

def isNonmonotone : EstimandClass -> Bool
  | .absorbingNonmonotone | .mixedNonmonotone |
      .nonabsorbingNonmonotone | .terminalNonmonotone => true
  | _ => false

/-- The common rotation path.  The only nonmonotone change is the initial
`pi/4 -> pi/2` step; every non-fixed row uses `pi/2 -> pi/4` at stages 1--2. -/
def coreRow (c : EstimandClass) (omega : Omega) : Nat -> HilbertTarget
  | 0 => if isNonmonotone c then newRotation omega else oldRotation omega
  | 1 => oldRotation omega
  | 2 => newRotation omega
  | 3 => newRotation omega
  | _ => terminalRotation omega

def rowFlag (c : EstimandClass) (omega : Omega) : Nat -> Bool
  | 5 =>
      match c with
      | .mixedMonotone | .mixedNonmonotone => !omega.branch
      | .nonabsorbingMonotone | .nonabsorbingNonmonotone |
          .terminalMonotone | .terminalNonmonotone => false
      | _ => true
  | 4 =>
      match c with
      | .terminalMonotone | .terminalNonmonotone => false
      | _ => true
  | _ => true

def rowValue (c : EstimandClass) (omega : Omega) (n : Nat) : Target :=
  if c = .fixed then limitValue omega
  else ⟨coreRow c omega n, rowFlag c omega n⟩

def estimand (c : EstimandClass) :
    HypotheticalSequentialEstimand Omega Target Prefix where
  horizon := fun _ => 6
  Order := fun _ => Unit
  orderNonempty := fun _ => inferInstance
  revealedPrefix := fun _ _ _ => ()
  value := fun omega _ n => rowValue c omega n
  limit := limitValue
  valuePrefixCompatible := by intros; rfl
  terminal := by
    intro omega xi
    cases c <;> rfl

def presentation (c : EstimandClass) : (estimand c).StructuralPresentation :=
  (estimand c).canonicalStructuralPresentation

theorem oldRotation_ne_terminal (omega : Omega) :
    oldRotation omega ≠ terminalRotation omega := by
  intro h
  have hcoord := congrArg (fun x : HilbertTarget => x (1 : Fin 2)) h
  cases htruth : omega.truth <;> cases hbranch : omega.branch <;>
    norm_num [oldRotation, terminalRotation, rotationEstimand, rotationLimit,
      alongDirection, eZ, eW, EuclideanSpace.single_apply,
      hiddenSignReal, branchSignReal, htruth, hbranch] at hcoord

theorem newRotation_ne_terminal (omega : Omega) :
    newRotation omega ≠ terminalRotation omega := by
  intro h
  have hcoord := congrArg (fun x : HilbertTarget => x (1 : Fin 2)) h
  cases htruth : omega.truth <;> cases hbranch : omega.branch <;>
    norm_num [newRotation, terminalRotation, rotationEstimand, rotationLimit,
      alongDirection, eZ, eW, EuclideanSpace.single_apply,
      hiddenSignReal, branchSignReal, htruth, hbranch,
      Real.sin_pi_div_four] at hcoord

theorem pi_div_four_mem : Real.pi / 4 ∈ Set.Icc (0 : Real) (Real.pi / 2) := by
  constructor <;> nlinarith [Real.pi_pos]

theorem pi_div_two_mem : Real.pi / 2 ∈ Set.Icc (0 : Real) (Real.pi / 2) := by
  constructor <;> nlinarith [Real.pi_pos]

theorem dist_terminal_rotation (alpha : Real)
    (halpha : alpha ∈ Set.Icc (0 : Real) (Real.pi / 2)) (omega : Omega) :
    dist (terminalRotation omega)
      (rotationEstimand alpha branchSignReal hiddenSignReal eZ eW omega) =
        rotationDiscrepancy alpha := by
  have h := rotationEstimand_sub_limit_norm alpha halpha
    branchSignReal hiddenSignReal eZ eW norm_eZ norm_eW inner_eZ_eW
    (congrFun branchSignReal_sq) (congrFun hiddenSignReal_sq) omega
  simpa [terminalRotation, dist_eq_norm, norm_sub_rev] using h

theorem discrepancy_new_lt_old :
    rotationDiscrepancy (Real.pi / 4) <
      rotationDiscrepancy (Real.pi / 2) := by
  exact rotationDiscrepancy_strictMonoOn pi_div_four_mem pi_div_two_mem
    (by nlinarith [Real.pi_pos])

theorem discrepancy_new_nonneg :
    0 ≤ rotationDiscrepancy (Real.pi / 4) :=
  (rotationDiscrepancy_mapsTo pi_div_four_mem).1

theorem singleton_mu_pos (omega : Omega) : 0 < mu ({omega} : Set Omega) := by
  exact StructuralWitnesses.singleton_mu_pos omega

theorem measure_pos_of_mem {E : Set Omega} {omega : Omega} (homega : omega ∈ E) :
    0 < mu E := by
  exact (singleton_mu_pos omega).trans_le
    (measure_mono (Set.singleton_subset_iff.mpr homega))

def baseState (branch : Bool) : Omega := StructuralWitnesses.baseState branch

@[simp] theorem dist_limit_old (omega : Omega) (b : Bool) :
    dist (limitValue omega) ⟨oldRotation omega, b⟩ =
      rotationDiscrepancy (Real.pi / 2) := by
  simp only [limitValue, FlagSpace.dist_eq]
  exact dist_terminal_rotation (Real.pi / 2) pi_div_two_mem omega

@[simp] theorem dist_limit_new (omega : Omega) (b : Bool) :
    dist (limitValue omega) ⟨newRotation omega, b⟩ =
      rotationDiscrepancy (Real.pi / 4) := by
  simp only [limitValue, FlagSpace.dist_eq]
  exact dist_terminal_rotation (Real.pi / 4) pi_div_four_mem omega

@[simp] theorem dist_limit_terminal (omega : Omega) (b : Bool) :
    dist (limitValue omega) ⟨terminalRotation omega, b⟩ = 0 := by
  simp [limitValue, FlagSpace.dist_eq]

@[simp] theorem dist_limit_value_old (omega : Omega) :
    dist (limitValue omega).value (oldRotation omega) =
      rotationDiscrepancy (Real.pi / 2) := by
  exact dist_terminal_rotation (Real.pi / 2) pi_div_two_mem omega

@[simp] theorem dist_limit_value_new (omega : Omega) :
    dist (limitValue omega).value (newRotation omega) =
      rotationDiscrepancy (Real.pi / 4) := by
  exact dist_terminal_rotation (Real.pi / 4) pi_div_four_mem omega

@[simp] theorem dist_limit_value_terminal (omega : Omega) :
    dist (limitValue omega).value (terminalRotation omega) = 0 := by
  simp [limitValue]

theorem not_fixed_nonfixed (c : EstimandClass) (hc : c ≠ .fixed) :
    ¬(estimand c).IsFixed := by
  intro hfixed
  have h1 := hfixed (baseState false) () 1 (by norm_num [estimand])
  cases c <;>
    simp [estimand, rowValue, coreRow, rowFlag, isNonmonotone,
      limitValue, oldRotation_ne_terminal] at hc h1

theorem fixed_isFixed : (estimand .fixed).IsFixed := by
  intro omega xi n hn
  rfl

theorem monotone_isMonotone
    (c : EstimandClass)
    (hc : c = .absorbingMonotone ∨ c = .mixedMonotone ∨
      c = .nonabsorbingMonotone ∨ c = .terminalMonotone) :
    (estimand c).IsMonotone := by
  intro omega xi n hn
  change dist (limitValue omega) (rowValue c omega (n + 1)) ≤
    dist (limitValue omega) (rowValue c omega n)
  change n < 6 at hn
  rcases hc with rfl | rfl | rfl | rfl <;>
    cases hbranch : omega.branch <;> interval_cases n <;>
      simp [rowValue, coreRow, rowFlag, isNonmonotone, hbranch,
        discrepancy_new_lt_old.le, discrepancy_new_nonneg]

theorem nonmonotone_not_isMonotone
    (c : EstimandClass)
    (hc : c = .absorbingNonmonotone ∨ c = .mixedNonmonotone ∨
      c = .nonabsorbingNonmonotone ∨ c = .terminalNonmonotone) :
    ¬(estimand c).IsMonotone := by
  intro hmonotone
  have h0 := hmonotone (baseState false) () 0 (by norm_num [estimand])
  change dist (limitValue (baseState false)) (rowValue c (baseState false) 1) ≤
    dist (limitValue (baseState false)) (rowValue c (baseState false) 0) at h0
  rcases hc with rfl | rfl | rfl | rfl <;>
    simp [rowValue, coreRow, rowFlag, isNonmonotone, baseState] at h0 <;>
    exact (not_le_of_gt discrepancy_new_lt_old) h0

theorem absorbing_tail
    (c : EstimandClass)
    (hc : c = .absorbingMonotone ∨ c = .absorbingNonmonotone) :
    ∀ omega (xi : (estimand c).Order omega) n,
      4 ≤ n → n < (estimand c).horizon omega →
        (estimand c).value omega xi (n + 1) = (estimand c).limit omega := by
  rintro omega xi n h4 hn
  change n < 6 at hn
  rcases hc with rfl | rfl <;> interval_cases n <;>
    simp [estimand, rowValue, coreRow, rowFlag, limitValue,
      rotationEstimand_zero, terminalRotation, oldRotation, newRotation]

theorem absorbing_preterminal_eq_stage4
    (c : EstimandClass)
    (hc : c = .absorbingMonotone ∨ c = .absorbingNonmonotone)
    {omega : Omega} {xi : (estimand c).Order omega} {n : Nat}
    (hn : n < (estimand c).horizon omega)
    (heq : (estimand c).value omega xi n = (estimand c).limit omega) :
    4 ≤ n := by
  change n < 6 at hn
  rcases hc with rfl | rfl <;> interval_cases n <;>
    simp [estimand, rowValue, coreRow, rowFlag, isNonmonotone, limitValue,
      oldRotation_ne_terminal, newRotation_ne_terminal] at heq ⊢

theorem absorbing_coverage
    (c : EstimandClass)
    (hc : c = .absorbingMonotone ∨ c = .absorbingNonmonotone) :
    AbsorbingCoverage (estimand c) (presentation c) mu := by
  filter_upwards [] with omega
  intro xi n hn heq
  rcases hn.lt_or_eq with hnlt | hterminal
  · exact StructuralWitnesses.persistence_of_stageTail
      (estimand c) (presentation c) 4 (absorbing_tail c hc)
      (absorbing_preterminal_eq_stage4 c hc hnlt heq) hn heq
  · subst n
    exact terminal_persistence (estimand c) (presentation c) xi

theorem absorbing_persistence_mem
    (c : EstimandClass)
    (hc : c = .absorbingMonotone ∨ c = .absorbingNonmonotone)
    (omega : Omega) :
    omega ∈ PersistenceAchievableSet (estimand c) (presentation c) := by
  refine ⟨(), 4, by norm_num [estimand], ?_⟩
  apply StructuralWitnesses.persistence_of_stageTail
    (estimand c) (presentation c) 4 (absorbing_tail c hc)
    (by norm_num) (by norm_num [estimand])
  rcases hc with rfl | rfl <;> rfl

theorem mixed_tail_false
    (c : EstimandClass)
    (hc : c = .mixedMonotone ∨ c = .mixedNonmonotone) :
    ∀ omega (xi : (estimand c).Order omega) n,
      omega.branch = false → 4 ≤ n → n < (estimand c).horizon omega →
        (estimand c).value omega xi (n + 1) = (estimand c).limit omega := by
  rintro omega xi n hbranch h4 hn
  change n < 6 at hn
  rcases hc with rfl | rfl <;> interval_cases n <;>
    simp [estimand, rowValue, coreRow, rowFlag, limitValue, hbranch]

theorem mixed_persistence_mem_false
    (c : EstimandClass)
    (hc : c = .mixedMonotone ∨ c = .mixedNonmonotone) :
    baseState false ∈ PersistenceAchievableSet (estimand c) (presentation c) := by
  refine ⟨(), 4, by norm_num [estimand], ?_⟩
  apply StructuralWitnesses.persistence_of_eventTail
    (estimand c) (presentation c) (fun omega => omega.branch = false) 4
    (mixed_tail_false c hc) rfl (by norm_num) (by norm_num [estimand])
  rcases hc with rfl | rfl <;> rfl

theorem mixed_not_persistence_true_stage4
    (c : EstimandClass)
    (hc : c = .mixedMonotone ∨ c = .mixedNonmonotone) :
    ¬PersistenceAt (estimand c) (presentation c) (baseState true) () 4 := by
  apply StructuralWitnesses.not_persistence_of_next_ne
    (estimand c) (presentation c) (by norm_num [estimand])
  rcases hc with rfl | rfl <;>
    simp [estimand, rowValue, coreRow, rowFlag, baseState,
      StructuralWitnesses.baseState, limitValue]

theorem mixed_accidental_mem_true
    (c : EstimandClass)
    (hc : c = .mixedMonotone ∨ c = .mixedNonmonotone) :
    baseState true ∈ AccidentalEqualitySet (estimand c) (presentation c) := by
  refine ⟨(), 4, by norm_num [estimand], ?_,
    mixed_not_persistence_true_stage4 c hc⟩
  rcases hc with rfl | rfl <;> rfl

theorem nonabsorbing_not_persistence_stage4
    (c : EstimandClass)
    (hc : c = .nonabsorbingMonotone ∨ c = .nonabsorbingNonmonotone)
    (omega : Omega) :
    ¬PersistenceAt (estimand c) (presentation c) omega () 4 := by
  apply StructuralWitnesses.not_persistence_of_next_ne
    (estimand c) (presentation c) (by norm_num [estimand])
  rcases hc with rfl | rfl <;>
    simp [estimand, rowValue, coreRow, rowFlag, limitValue]

theorem nonabsorbing_preterminal_eq_iff_stage4
    (c : EstimandClass)
    (hc : c = .nonabsorbingMonotone ∨ c = .nonabsorbingNonmonotone)
    {omega : Omega} {xi : (estimand c).Order omega} {n : Nat}
    (hn : n < (estimand c).horizon omega) :
    (estimand c).value omega xi n = (estimand c).limit omega ↔ n = 4 := by
  change n < 6 at hn
  rcases hc with rfl | rfl <;> interval_cases n <;>
    simp [estimand, rowValue, coreRow, rowFlag, isNonmonotone, limitValue,
      oldRotation_ne_terminal, newRotation_ne_terminal]

theorem nonabsorbing_persistenceSet_empty
    (c : EstimandClass)
    (hc : c = .nonabsorbingMonotone ∨ c = .nonabsorbingNonmonotone) :
    PersistenceAchievableSet (estimand c) (presentation c) = ∅ := by
  apply Set.Subset.antisymm
  · rintro omega ⟨xi, n, hn, hpersistence⟩
    have hn4 := (nonabsorbing_preterminal_eq_iff_stage4 c hc hn).mp
      hpersistence.1.2
    subst n
    cases xi
    exact (nonabsorbing_not_persistence_stage4 c hc omega hpersistence).elim
  · exact Set.empty_subset _

theorem nonabsorbing_equality_mem
    (c : EstimandClass)
    (hc : c = .nonabsorbingMonotone ∨ c = .nonabsorbingNonmonotone)
    (omega : Omega) :
    omega ∈ EqualityAchievableSet (estimand c) := by
  refine ⟨(), 4, by norm_num [estimand], ?_⟩
  rcases hc with rfl | rfl <;> rfl

theorem terminal_equalitySet_empty
    (c : EstimandClass)
    (hc : c = .terminalMonotone ∨ c = .terminalNonmonotone) :
    EqualityAchievableSet (estimand c) = ∅ := by
  apply Set.Subset.antisymm
  · rintro omega ⟨xi, n, hn, heq⟩
    change n < 6 at hn
    rcases hc with rfl | rfl <;> interval_cases n <;>
      simp [estimand, rowValue, coreRow, rowFlag, isNonmonotone, limitValue,
        oldRotation_ne_terminal, newRotation_ne_terminal] at heq
  · exact Set.empty_subset _

theorem fixed_hasClass :
    HasClass (estimand .fixed) (presentation .fixed) mu .fixed :=
  fixed_isFixed

theorem absorbingMonotone_hasClass :
    HasClass (estimand .absorbingMonotone) (presentation .absorbingMonotone)
      mu .absorbingMonotone := by
  refine ⟨monotone_isMonotone _ (Or.inl rfl),
    not_fixed_nonfixed _ (by decide), ?_,
    absorbing_coverage _ (Or.inl rfl)⟩
  exact measure_pos_of_mem
    (absorbing_persistence_mem _ (Or.inl rfl) (baseState false))

theorem absorbingNonmonotone_hasClass :
    HasClass (estimand .absorbingNonmonotone)
      (presentation .absorbingNonmonotone) mu .absorbingNonmonotone := by
  refine ⟨nonmonotone_not_isMonotone _ (Or.inl rfl),
    not_fixed_nonfixed _ (by decide), ?_,
    absorbing_coverage _ (Or.inr rfl)⟩
  exact measure_pos_of_mem
    (absorbing_persistence_mem _ (Or.inr rfl) (baseState false))

theorem mixedMonotone_hasClass :
    HasClass (estimand .mixedMonotone) (presentation .mixedMonotone)
      mu .mixedMonotone := by
  exact ⟨monotone_isMonotone _ (Or.inr (Or.inl rfl)),
    not_fixed_nonfixed _ (by decide),
    measure_pos_of_mem (mixed_persistence_mem_false _ (Or.inl rfl)),
    measure_pos_of_mem (mixed_accidental_mem_true _ (Or.inl rfl))⟩

theorem mixedNonmonotone_hasClass :
    HasClass (estimand .mixedNonmonotone) (presentation .mixedNonmonotone)
      mu .mixedNonmonotone := by
  exact ⟨nonmonotone_not_isMonotone _ (Or.inr (Or.inl rfl)),
    not_fixed_nonfixed _ (by decide),
    measure_pos_of_mem (mixed_persistence_mem_false _ (Or.inr rfl)),
    measure_pos_of_mem (mixed_accidental_mem_true _ (Or.inr rfl))⟩

theorem nonabsorbingMonotone_hasClass :
    HasClass (estimand .nonabsorbingMonotone)
      (presentation .nonabsorbingMonotone) mu .nonabsorbingMonotone := by
  refine ⟨monotone_isMonotone _ (Or.inr (Or.inr (Or.inl rfl))),
    not_fixed_nonfixed _ (by decide),
    measure_pos_of_mem
      (nonabsorbing_equality_mem _ (Or.inl rfl) (baseState false)), ?_⟩
  rw [PersistenceAchievable,
    nonabsorbing_persistenceSet_empty _ (Or.inl rfl)]
  simp

theorem nonabsorbingNonmonotone_hasClass :
    HasClass (estimand .nonabsorbingNonmonotone)
      (presentation .nonabsorbingNonmonotone) mu .nonabsorbingNonmonotone := by
  refine ⟨nonmonotone_not_isMonotone _
      (Or.inr (Or.inr (Or.inl rfl))),
    not_fixed_nonfixed _ (by decide),
    measure_pos_of_mem
      (nonabsorbing_equality_mem _ (Or.inr rfl) (baseState false)), ?_⟩
  rw [PersistenceAchievable,
    nonabsorbing_persistenceSet_empty _ (Or.inr rfl)]
  simp

theorem terminalMonotone_hasClass :
    HasClass (estimand .terminalMonotone) (presentation .terminalMonotone)
      mu .terminalMonotone := by
  refine ⟨monotone_isMonotone _ (Or.inr (Or.inr (Or.inr rfl))),
    not_fixed_nonfixed _ (by decide), ?_⟩
  rw [EqualityAchievable, terminal_equalitySet_empty _ (Or.inl rfl)]
  simp

theorem terminalNonmonotone_hasClass :
    HasClass (estimand .terminalNonmonotone)
      (presentation .terminalNonmonotone) mu .terminalNonmonotone := by
  refine ⟨nonmonotone_not_isMonotone _
      (Or.inr (Or.inr (Or.inr rfl))),
    not_fixed_nonfixed _ (by decide), ?_⟩
  rw [EqualityAchievable, terminal_equalitySet_empty _ (Or.inr rfl)]
  simp

/-- Every class is realised by a flag lift of the same rotation family; the
eight non-fixed rows share the exact stage-1 and stage-2 rotation variables. -/
theorem witnesses (c : EstimandClass) :
    HasClass (estimand c) (presentation c) mu c := by
  cases c with
  | fixed => exact fixed_hasClass
  | absorbingMonotone => exact absorbingMonotone_hasClass
  | absorbingNonmonotone => exact absorbingNonmonotone_hasClass
  | mixedMonotone => exact mixedMonotone_hasClass
  | mixedNonmonotone => exact mixedNonmonotone_hasClass
  | nonabsorbingMonotone => exact nonabsorbingMonotone_hasClass
  | nonabsorbingNonmonotone => exact nonabsorbingNonmonotone_hasClass
  | terminalMonotone => exact terminalMonotone_hasClass
  | terminalNonmonotone => exact terminalNonmonotone_hasClass

theorem classEventsMeasurable (c : EstimandClass) :
    ClassEventsMeasurable (estimand c) (presentation c) := by
  constructor <;> simp

theorem stage_one_value (c : EstimandClass) (hc : c ≠ .fixed) :
    (fun omega => ((estimand c).value omega () 1).value) = oldRotation := by
  funext omega
  cases c <;>
    simp [rowValue, estimand, coreRow] at hc ⊢

theorem stage_two_value (c : EstimandClass) (hc : c ≠ .fixed) :
    (fun omega => ((estimand c).value omega () 2).value) = newRotation := by
  funext omega
  cases c <;>
    simp [rowValue, estimand, coreRow] at hc ⊢

theorem measurable_flags (c : EstimandClass) :
    ∀ n, Measurable fun omega => ((estimand c).value omega () n).flag := by
  intro n
  exact measurable_from_top

def stageValue (c : EstimandClass) (n : Nat) : Omega -> Target :=
  fun omega => (estimand c).value omega () n

def stageHilbertValue (c : EstimandClass) (n : Nat) : Omega -> HilbertTarget :=
  fun omega => (stageValue c n omega).value

/-- The actual flag-valued RCD of one stage of the class witness. -/
def stageLaw (c : EstimandClass) (n : Nat)
    (m : MeasurableSpace Omega) : Kernel[m] Omega Target :=
  canonicalConditionalLaw (mOmega := instMeasurableSpaceLatentState)
    latentLaw m (stageValue c n)

theorem stageLaw_isRCD (c : EstimandClass) (n : Nat)
    (m : MeasurableSpace Omega) (hm : m ≤ ⊤) :
    IsRegularConditionalLaw latentLaw m hm (stageValue c n)
      (stageLaw c n m) := by
  have hStage : @Measurable Omega Target
      instMeasurableSpaceLatentState
      (inferInstance : MeasurableSpace Target) (stageValue c n) :=
    measurable_from_top
  exact canonicalConditionalLaw_isRCD
    (mOmega := instMeasurableSpaceLatentState)
    (sbOmega := inferInstance) (mS := inferInstance)
    latentLaw m hm (stageValue c n) hStage

theorem stageLaw_project (c : EstimandClass) (n : Nat)
    (m : MeasurableSpace Omega) :
    (stageLaw c n m).map FlagSpace.value =
      hilbertLaw m (stageHilbertValue c n) := by
  have hStage : @Measurable Omega Target
      instMeasurableSpaceLatentState
      (inferInstance : MeasurableSpace Target) (stageValue c n) :=
    measurable_from_top
  let k : @Kernel Omega Omega m instMeasurableSpaceLatentState :=
    @condExpKernel Omega instMeasurableSpaceLatentState inferInstance
      latentLaw inferInstance m
  change (k.map (stageValue c n)).map FlagSpace.value =
    k.map (stageHilbertValue c n)
  have hcomp : FlagSpace.value ∘ stageValue c n =
      stageHilbertValue c n := by rfl
  rw [← hcomp]
  exact (Kernel.map_comp_right k hStage FlagSpace.measurable_value).symm

theorem stageFrechetVariance_eq_hilbert (c : EstimandClass) (n : Nat)
    (m : MeasurableSpace Omega) :
    posteriorFrechetVarianceReal m (stageLaw c n m) =
      posteriorFrechetVarianceReal m
        (hilbertLaw m (stageHilbertValue c n)) := by
  funext omega
  simp only [posteriorFrechetVarianceReal]
  rw [FlagSpace.frechetVariance_eq_project]
  have hproject := congrArg (fun k => k omega) (stageLaw_project c n m)
  rw [Kernel.map_apply _ FlagSpace.measurable_value] at hproject
  rw [hproject]

theorem stageHilbertValue_one (c : EstimandClass) (hc : c ≠ .fixed) :
    stageHilbertValue c 1 = oldRotation :=
  stage_one_value c hc

theorem stageHilbertValue_two (c : EstimandClass) (hc : c ≠ .fixed) :
    stageHilbertValue c 2 = newRotation :=
  stage_two_value c hc

theorem stageHilbertValue_eq_coreRow
    (c : EstimandClass) (hc : c ≠ .fixed) (n : Nat) :
    stageHilbertValue c n = fun omega => coreRow c omega n := by
  funext omega
  cases c <;>
    simp [stageHilbertValue, stageValue, estimand, rowValue] at hc ⊢

theorem flaggedFrechetVariance_old_one
    (c : EstimandClass) (hc : c ≠ .fixed) :
    posteriorFrechetVarianceReal generatedOne (stageLaw c 1 generatedOne) =
      fun _ => (3 / 4 : Real) := by
  rw [stageFrechetVariance_eq_hilbert,
    stageHilbertValue_one c hc, oldFrechetVariance_one]

theorem flaggedFrechetVariance_old_two
    (c : EstimandClass) (hc : c ≠ .fixed) :
    posteriorFrechetVarianceReal generatedTwo (stageLaw c 1 generatedTwo) =
      varianceTwoReal := by
  rw [stageFrechetVariance_eq_hilbert,
    stageHilbertValue_one c hc, oldFrechetVariance_two]

theorem flaggedFrechetVariance_old_zero
    (c : EstimandClass) (hc : c ≠ .fixed) :
    posteriorFrechetVarianceReal generatedZero (stageLaw c 1 generatedZero) =
      fun _ => (1 : Real) := by
  rw [stageFrechetVariance_eq_hilbert,
    stageHilbertValue_one c hc, oldFrechetVariance_zero]

theorem flaggedFrechetVariance_new_two
    (c : EstimandClass) (hc : c ≠ .fixed) :
    posteriorFrechetVarianceReal generatedTwo (stageLaw c 2 generatedTwo) =
      fun omega => rotationVariance (1 / 2) (varianceTwoReal omega) := by
  rw [stageFrechetVariance_eq_hilbert,
    stageHilbertValue_two c hc, newFrechetVariance_two]

theorem flaggedFrechetVariance_new_zero
    (c : EstimandClass) (hc : c ≠ .fixed) :
    posteriorFrechetVarianceReal generatedZero (stageLaw c 2 generatedZero) =
      fun _ => (1 : Real) := by
  rw [stageFrechetVariance_eq_hilbert,
    stageHilbertValue_two c hc, newFrechetVariance_zero]

/-- The uninformative observation model satisfies the learning inequality
with equality at every stage of each non-fixed class witness. -/
theorem flagged_uninformative_all_stages
    (c : EstimandClass) (hc : c ≠ .fixed) (n : Nat) :
    posteriorFrechetVarianceReal generatedZero (stageLaw c n generatedZero) =
      fun _ => (1 : Real) := by
  rw [stageFrechetVariance_eq_hilbert,
    stageHilbertValue_eq_coreRow c hc n]
  cases n with
  | zero =>
      cases hnonmono : isNonmonotone c <;>
        simp [coreRow, hnonmono, oldFrechetVariance_zero,
          newFrechetVariance_zero]
  | succ n =>
      cases n with
      | zero => simpa [coreRow] using oldFrechetVariance_zero
      | succ n =>
          cases n with
          | zero => simpa [coreRow] using newFrechetVariance_zero
          | succ n =>
              cases n with
              | zero => simpa [coreRow] using newFrechetVariance_zero
              | succ n =>
                  simpa [coreRow] using terminalFrechetVariance_zero

/-- Under the uninformative observation model, the learning inequality holds
with equality at every transition of the same flag-valued estimand. -/
theorem flagged_uninformative_all_transitions
    (c : EstimandClass) (hc : c ≠ .fixed) (n : Nat) :
    (fun omega =>
      latentLaw[posteriorFrechetVarianceReal generatedZero
          (stageLaw c (n + 1) generatedZero) | generatedZero] omega -
        posteriorFrechetVarianceReal generatedZero
          (stageLaw c n generatedZero) omega) =ᵐ[latentLaw]
      fun _ => (0 : Real) := by
  have hnext := flagged_uninformative_all_stages c hc (n + 1)
  have hcurrent := flagged_uninformative_all_stages c hc n
  have hcond :
      latentLaw[posteriorFrechetVarianceReal generatedZero
        (stageLaw c (n + 1) generatedZero) | generatedZero] =ᵐ[latentLaw]
        fun _ => (1 : Real) := by
    exact (condExp_congr_ae (m := generatedZero)
      (EventuallyEq.of_eq hnext)).trans
        (EventuallyEq.of_eq (condExp_const le_top 1))
  filter_upwards [hcond] with omega hcondOmega
  rw [hcondOmega, congrFun hcurrent omega]
  norm_num

theorem expectedFlaggedFrechetVariance_two_given_one
    (c : EstimandClass) (hc : c ≠ .fixed) :
    latentLaw[posteriorFrechetVarianceReal generatedTwo
      (stageLaw c 2 generatedTwo) | generatedOne] =ᵐ[latentLaw]
        fun _ => (74 / 85 : Real) := by
  have hcongr := condExp_congr_ae (μ := latentLaw) (m := generatedOne)
    (EventuallyEq.of_eq (flaggedFrechetVariance_new_two c hc))
  have hvint : Integrable varianceTwoReal latentLaw := Integrable.of_finite
  have haffine := condExp_rotationVariance latentLaw generatedOne le_top
    (1 / 2) varianceTwoReal hvint
  filter_upwards [hcongr, haffine, condExp_varianceTwo_one] with
    omega hcongrOmega haffineOmega hvarOmega
  rw [hcongrOmega, haffineOmega, hvarOmega]
  norm_num [rotationVariance]

theorem expectedFlaggedOldFrechetVariance_two_given_one
    (c : EstimandClass) (hc : c ≠ .fixed) :
    latentLaw[posteriorFrechetVarianceReal generatedTwo
      (stageLaw c 1 generatedTwo) | generatedOne] =ᵐ[latentLaw]
        fun _ => (63 / 85 : Real) := by
  exact (condExp_congr_ae (μ := latentLaw) (m := generatedOne)
    (EventuallyEq.of_eq (flaggedFrechetVariance_old_two c hc))).trans
      condExp_varianceTwo_one

/-- The actual Fréchet information term of the flag-valued old target. -/
theorem flagged_information_term
    (c : EstimandClass) (hc : c ≠ .fixed) :
    frechetInformationGain latentLaw generatedOne generatedTwo
      (stageLaw c 1 generatedOne) (stageLaw c 1 generatedTwo) =ᵐ[latentLaw]
        fun _ => (3 / 340 : Real) := by
  filter_upwards [expectedFlaggedOldFrechetVariance_two_given_one c hc] with
    omega holdFine
  simp only [frechetInformationGain, currentPosteriorFrechetVariance,
    refinedOldPosteriorFrechetVariance, informationGain]
  rw [congrFun (flaggedFrechetVariance_old_one c hc) omega, holdFine]
  norm_num

theorem flagged_information_term_zero
    (c : EstimandClass) (hc : c ≠ .fixed) :
    frechetInformationGain latentLaw generatedZero generatedZero
      (stageLaw c 1 generatedZero) (stageLaw c 1 generatedZero) =ᵐ[latentLaw]
        fun _ => (0 : Real) := by
  have hvar := flaggedFrechetVariance_old_zero c hc
  have hcond :
      latentLaw[posteriorFrechetVarianceReal generatedZero
        (stageLaw c 1 generatedZero) | generatedZero] =ᵐ[latentLaw]
        fun _ => (1 : Real) := by
    exact (condExp_congr_ae (μ := latentLaw) (m := generatedZero)
      (EventuallyEq.of_eq hvar)).trans
        (EventuallyEq.of_eq (condExp_const le_top 1))
  filter_upwards [hcond] with omega hcondOmega
  simp only [frechetInformationGain, currentPosteriorFrechetVariance,
    refinedOldPosteriorFrechetVariance, informationGain]
  rw [congrFun hvar omega, hcondOmega]
  norm_num

/-- The actual Fréchet movement term of the same flag-valued rotation step. -/
theorem flagged_movement_term
    (c : EstimandClass) (hc : c ≠ .fixed) :
    frechetEstimandMovement latentLaw generatedOne generatedTwo
      (stageLaw c 1 generatedTwo) (stageLaw c 2 generatedTwo) =ᵐ[latentLaw]
        fun _ => (44 / 340 : Real) := by
  have hdiff :
      (fun omega =>
        posteriorFrechetVarianceReal generatedTwo
            (stageLaw c 2 generatedTwo) omega -
          posteriorFrechetVarianceReal generatedTwo
            (stageLaw c 1 generatedTwo) omega) =
        fun omega => rotationVariance (1 / 2) (varianceTwoReal omega) -
          varianceTwoReal omega := by
    funext omega
    rw [congrFun (flaggedFrechetVariance_new_two c hc) omega,
      congrFun (flaggedFrechetVariance_old_two c hc) omega]
  have hcongr := condExp_congr_ae (μ := latentLaw) (m := generatedOne)
    (EventuallyEq.of_eq hdiff)
  have hvint : Integrable varianceTwoReal latentLaw := Integrable.of_finite
  have hrotint : Integrable
      (fun omega => rotationVariance (1 / 2) (varianceTwoReal omega))
      latentLaw := by
    exact (integrable_const (1 / 2 : Real)).add
      (hvint.const_mul (1 - 1 / 2))
  have haffine := condExp_rotationVariance latentLaw generatedOne le_top
    (1 / 2) varianceTwoReal hvint
  have hsub := condExp_sub
    hrotint hvint generatedOne
  have hsub' :
      latentLaw[(fun omega =>
        rotationVariance (1 / 2) (varianceTwoReal omega) -
          varianceTwoReal omega) | generatedOne] =ᵐ[latentLaw]
        latentLaw[(fun omega => rotationVariance (1 / 2)
          (varianceTwoReal omega)) | generatedOne] -
          latentLaw[varianceTwoReal | generatedOne] := by
    have hfun :
        (fun omega => rotationVariance (1 / 2) (varianceTwoReal omega) -
          varianceTwoReal omega) =
        (fun omega => rotationVariance (1 / 2) (varianceTwoReal omega)) -
          varianceTwoReal := by rfl
    rw [hfun]
    exact hsub
  filter_upwards [hcongr, hsub', haffine, condExp_varianceTwo_one] with
    omega hcongrOmega hsubOmega haffineOmega hvarOmega
  simp only [frechetEstimandMovement, refinedNewPosteriorFrechetVariance,
    refinedOldPosteriorFrechetVariance]
  simp only [Pi.sub_apply] at hsubOmega
  rw [hcongrOmega, hsubOmega, haffineOmega, hvarOmega]
  norm_num [rotationVariance]

/-- Exact noisy-channel Fréchet-variance increase for the same flag-valued
estimand which carries the structural class witness. -/
theorem flagged_noisy_verdict (c : EstimandClass) (hc : c ≠ .fixed) :
    (fun omega =>
      latentLaw[posteriorFrechetVarianceReal generatedTwo
          (stageLaw c 2 generatedTwo) | generatedOne] omega -
        posteriorFrechetVarianceReal generatedOne
          (stageLaw c 1 generatedOne) omega) =ᵐ[latentLaw]
      fun _ => (41 / 340 : Real) := by
  filter_upwards [expectedFlaggedFrechetVariance_two_given_one c hc] with
    omega hnew
  rw [hnew, congrFun (flaggedFrechetVariance_old_one c hc) omega]
  norm_num

/-- Under the uninformative filtration, the same flag-valued rotation step
has zero conditional expected Fréchet-variance change. -/
theorem flagged_uninformative_verdict
    (c : EstimandClass) (hc : c ≠ .fixed) :
    (fun omega =>
      latentLaw[posteriorFrechetVarianceReal generatedZero
          (stageLaw c 2 generatedZero) | generatedZero] omega -
        posteriorFrechetVarianceReal generatedZero
          (stageLaw c 1 generatedZero) omega) =ᵐ[latentLaw]
      fun _ => (0 : Real) := by
  simpa using flagged_uninformative_all_transitions c hc 1

/-- Genuine repair of the manuscript's two-verdict assertion.  For every
non-fixed structural class, one and the same flag-lifted estimand has the
uninformative verdict and the strict noisy-channel verdict. -/
theorem bothverdicts (c : EstimandClass) (hc : c ≠ .fixed) :
    HasClass (estimand c) (presentation c) mu c ∧
      ClassEventsMeasurable (estimand c) (presentation c) ∧
      (∀ n, IsRegularConditionalLaw latentLaw generatedZero le_top
          (stageValue c n) (stageLaw c n generatedZero) ∧
        posteriorFrechetVarianceReal generatedZero
          (stageLaw c n generatedZero) = fun _ => (1 : Real)) ∧
      IsRegularConditionalLaw latentLaw generatedOne le_top
        (stageValue c 1) (stageLaw c 1 generatedOne) ∧
      IsRegularConditionalLaw latentLaw generatedTwo le_top
        (stageValue c 2) (stageLaw c 2 generatedTwo) ∧
      stageHilbertValue c 1 = oldRotation ∧
      stageHilbertValue c 2 = newRotation ∧
      (∀ n, (fun omega =>
        latentLaw[posteriorFrechetVarianceReal generatedZero
            (stageLaw c (n + 1) generatedZero) | generatedZero] omega -
          posteriorFrechetVarianceReal generatedZero
            (stageLaw c n generatedZero) omega) =ᵐ[latentLaw]
          fun _ => (0 : Real)) ∧
      (frechetInformationGain latentLaw generatedZero generatedZero
        (stageLaw c 1 generatedZero) (stageLaw c 1 generatedZero) =ᵐ[latentLaw]
        fun _ => (0 : Real)) ∧
      ((fun omega =>
        latentLaw[posteriorFrechetVarianceReal generatedTwo
            (stageLaw c 2 generatedTwo) | generatedOne] omega -
          posteriorFrechetVarianceReal generatedOne
            (stageLaw c 1 generatedOne) omega) =ᵐ[latentLaw]
          fun _ => (41 / 340 : Real)) ∧
      (frechetInformationGain latentLaw generatedOne generatedTwo
        (stageLaw c 1 generatedOne) (stageLaw c 1 generatedTwo) =ᵐ[latentLaw]
        fun _ => (3 / 340 : Real)) ∧
      (frechetEstimandMovement latentLaw generatedOne generatedTwo
        (stageLaw c 1 generatedTwo) (stageLaw c 2 generatedTwo) =ᵐ[latentLaw]
        fun _ => (44 / 340 : Real)) ∧
      (0 : Real) < 3 / 340 ∧ (3 / 340 : Real) < 44 / 340 ∧
        (0 : Real) < 41 / 340 := by
  exact ⟨witnesses c, classEventsMeasurable c,
    fun n => ⟨stageLaw_isRCD c n generatedZero le_top,
      flagged_uninformative_all_stages c hc n⟩,
    stageLaw_isRCD c 1 generatedOne le_top,
    stageLaw_isRCD c 2 generatedTwo le_top,
    stageHilbertValue_one c hc, stageHilbertValue_two c hc,
    flagged_uninformative_all_transitions c hc,
    flagged_information_term_zero c hc,
    flagged_noisy_verdict c hc,
    flagged_information_term c hc, flagged_movement_term c hc,
    by norm_num, by norm_num, by norm_num⟩

/-- Fixed estimands retain the universal learning guarantee; all eight
non-fixed classes have the same-estimand counterexample. -/
theorem impossibility :
    (∀ c : EstimandClass, c ≠ .fixed →
      HasClass (estimand c) (presentation c) mu c ∧
      ClassEventsMeasurable (estimand c) (presentation c) ∧
      (∀ n, posteriorFrechetVarianceReal generatedZero
        (stageLaw c n generatedZero) = fun _ => (1 : Real)) ∧
      (∀ n, (fun omega =>
        latentLaw[posteriorFrechetVarianceReal generatedZero
            (stageLaw c (n + 1) generatedZero) | generatedZero] omega -
          posteriorFrechetVarianceReal generatedZero
            (stageLaw c n generatedZero) omega) =ᵐ[latentLaw]
          fun _ => (0 : Real)) ∧
      ((fun omega =>
        latentLaw[posteriorFrechetVarianceReal generatedTwo
            (stageLaw c 2 generatedTwo) | generatedOne] omega -
          posteriorFrechetVarianceReal generatedOne
            (stageLaw c 1 generatedOne) omega) =ᵐ[latentLaw]
          fun _ => (41 / 340 : Real))) := by
  intro c hc
  exact ⟨witnesses c, classEventsMeasurable c,
    flagged_uninformative_all_stages c hc,
    flagged_uninformative_all_transitions c hc, flagged_noisy_verdict c hc⟩

end

end SameEstimandImpossibility

end SequentialLearning
