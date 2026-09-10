import SequentialLearning.AbsorbingMSEFromClasses
import Mathlib.Probability.Martingale.Basic

/-!
# Realised observed processes

This module connects the pathwise taxonomy to a single observed sequence.  A
realised order is fixed at each latent state, stage `n` uses
`min n (K.horizon omega)`, and the sequence is therefore extended constantly
after its state-dependent terminal stage.  The bundle records the filtration,
adaptedness, moment assumptions, and measurability of both the taxonomy events
and the realised persistence events.
-/

namespace SequentialLearning

open Filter MeasureTheory Set
open scoped ENNReal MeasureTheory ProbabilityTheory

noncomputable section

universe uOmega uS uPrefix

namespace HypotheticalSequentialEstimand
namespace StructuralPresentation

variable {Omega : Type uOmega} {S : Type uS} {Prefix : Type uPrefix}
  {mOmega : MeasurableSpace Omega}
  (K : HypotheticalSequentialEstimand Omega S Prefix)
  (A : K.StructuralPresentation)

/-- The classes whose definition entails pointwise monotonicity. -/
def EstimandClass.IsMonotone : EstimandClass → Prop
  | .fixed | .absorbingMonotone | .mixedMonotone |
      .nonabsorbingMonotone | .terminalMonotone => True
  | _ => False

/-- Class membership, rather than a repeated analytic hypothesis, supplies
pointwise monotonicity for every monotone class. -/
theorem hasClass_isMonotone [PseudoMetricSpace S]
    (mu : Measure Omega) (c : EstimandClass)
    (hClass : HasClass K A mu c) (hMonotoneClass : c.IsMonotone) :
    K.IsMonotone := by
  cases c with
  | fixed => exact K.fixed_isMonotone hClass
  | absorbingMonotone => exact hClass.1
  | mixedMonotone => exact hClass.1
  | nonabsorbingMonotone => exact hClass.1
  | terminalMonotone => exact hClass.1
  | absorbingNonmonotone | mixedNonmonotone |
      nonabsorbingNonmonotone | terminalNonmonotone =>
      simp [EstimandClass.IsMonotone] at hMonotoneClass

/-- Class membership in `.fixed` supplies pointwise fixedness. -/
theorem hasClass_isFixed [PseudoMetricSpace S]
    (mu : Measure Omega) (hClass : HasClass K A mu .fixed) :
    K.IsFixed := hClass

/-- The five taxonomy rows whose class membership entails monotonicity.  This
index prevents a class-facing theorem from needing a separate monotonicity
premise. -/
inductive MonotoneEstimandClass
  | fixed
  | absorbing
  | mixed
  | nonabsorbing
  | terminal
  deriving DecidableEq

/-- Forget the evidence-carrying monotone-class index. -/
def MonotoneEstimandClass.toEstimandClass : MonotoneEstimandClass → EstimandClass
  | .fixed => .fixed
  | .absorbing => .absorbingMonotone
  | .mixed => .mixedMonotone
  | .nonabsorbing => .nonabsorbingMonotone
  | .terminal => .terminalMonotone

/-- Membership in a monotone-class row supplies pointwise monotonicity with
no repeated analytic premise. -/
theorem MonotoneEstimandClass.hasClass_isMonotone
    [PseudoMetricSpace S] (mu : Measure Omega) (c : MonotoneEstimandClass)
    (hClass : HasClass K A mu c.toEstimandClass) : K.IsMonotone := by
  cases c with
  | fixed => exact K.fixed_isMonotone hClass
  | absorbing | mixed | nonabsorbing | terminal => exact hClass.1

/-- The three taxonomy rows whose class membership entails absorbing
coverage. -/
inductive AbsorbingEstimandClass
  | fixed
  | monotone
  | nonmonotone
  deriving DecidableEq

/-- Forget the evidence-carrying absorbing-class index. -/
def AbsorbingEstimandClass.toEstimandClass :
    AbsorbingEstimandClass → EstimandClass
  | .fixed => .fixed
  | .monotone => .absorbingMonotone
  | .nonmonotone => .absorbingNonmonotone

/-- Membership in an absorbing-class row supplies coverage with no repeated
coverage premise. -/
theorem AbsorbingEstimandClass.hasClass_absorbingCoverage
    [PseudoMetricSpace S] (mu : Measure Omega) (c : AbsorbingEstimandClass)
    (hClass : HasClass K A mu c.toEstimandClass) :
    AbsorbingCoverage K A mu := by
  cases c with
  | fixed => exact fixed_absorbingCoverage K A mu hClass
  | monotone | nonmonotone => exact hClass.2.2.2

/-- Monotonicity iterated between any two applicable stages of one
hypothetical order. -/
theorem IsMonotone.dist_antitone
    [PseudoMetricSpace S] (hMonotone : K.IsMonotone)
    (omega : Omega) (xi : K.Order omega) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ K.horizon omega) :
    dist (K.limit omega) (K.value omega xi j) ≤
      dist (K.limit omega) (K.value omega xi i) := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | @succ j hij ih =>
      exact (hMonotone omega xi j (Nat.lt_of_succ_le hj)).trans
        (ih (Nat.le_of_succ_le hj))

/-- A realised observation process.  The sequence itself is derived from the
single realised order and the capped stage index; callers cannot choose an
incompatible value process independently of the taxonomy object. -/
structure RealizedObservedProcess [PseudoMetricSpace S] [ENorm S]
    (mu : Measure[mOmega] Omega) where
  order : (omega : Omega) → K.Order omega
  filtration : Filtration ℕ mOmega
  classEventsMeasurable : ClassEventsMeasurable K A
  valueAdapted : ∀ n,
    StronglyMeasurable[filtration n]
      (fun omega => K.value omega (order omega) (min n (K.horizon omega)))
  persistenceEventMeasurable : ∀ n, MeasurableSet
    {omega | PersistenceAt K A omega (order omega) (min n (K.horizon omega))}
  limitStronglyMeasurable : StronglyMeasurable K.limit
  limitMemLp : MemLp K.limit 2 mu
  valueMemLp : ∀ n,
    MemLp (fun omega =>
      K.value omega (order omega) (min n (K.horizon omega))) 2 mu

variable [PseudoMetricSpace S] [ENorm S] {mu : Measure[mOmega] Omega}

namespace RealizedObservedProcess

variable (R : RealizedObservedProcess K A mu)

/-- The applicable stage index at observation time `n`. -/
def stageIndex (n : ℕ) (omega : Omega) : ℕ :=
  min n (K.horizon omega)

/-- The realised estimand sequence, extended constantly after termination. -/
def value (n : ℕ) (omega : Omega) : S :=
  K.value omega (R.order omega) (stageIndex K n omega)

/-- The realised revealed-prefix sequence. -/
def realizedPrefix (n : ℕ) (omega : Omega) : Prefix :=
  K.revealedPrefix omega (R.order omega) (stageIndex K n omega)

/-- The realised persistence event at observation time `n`. -/
def persistenceEvent (n : ℕ) : Set Omega :=
  {omega | PersistenceAt K A omega (R.order omega) (stageIndex K n omega)}

/-- The current-to-limit discrepancy along the realised process. -/
def discrepancy (n : ℕ) (omega : Omega) : ℝ :=
  dist (K.limit omega) (R.value K A n omega)

omit [PseudoMetricSpace S] [ENorm S] in
/-- The realised stage is always applicable. -/
theorem stageIndex_le_horizon (n : ℕ) (omega : Omega) :
    stageIndex K n omega ≤ K.horizon omega := by
  exact min_le_right _ _

omit [PseudoMetricSpace S] [ENorm S] in
/-- Observation indices are monotone before and after capping. -/
theorem stageIndex_mono {n k : ℕ} (hnk : n ≤ k) (omega : Omega) :
    stageIndex K n omega ≤ stageIndex K k omega := by
  exact min_le_min hnk le_rfl

/-- A process stage as the one-stage object used by the absorbing-MSE core. -/
def stage (n : ℕ) : RealizedStage K where
  order := R.order
  index := stageIndex K n
  applicable := stageIndex_le_horizon K n

@[simp]
theorem stage_value (n : ℕ) :
    (R.stage K A n).value K = R.value K A n := rfl

@[simp]
theorem stage_persistenceEvent (n : ℕ) :
    (R.stage K A n).persistenceEvent K A = R.persistenceEvent K A n := rfl

/-- At and after the state-dependent final count, the process equals its
terminal estimand. -/
theorem value_eq_limit_of_horizon_le (n : ℕ) (omega : Omega)
    (hTerminal : K.horizon omega ≤ n) :
    R.value K A n omega = K.limit omega := by
  simp only [value, stageIndex, min_eq_right hTerminal]
  exact K.terminal omega (R.order omega)

/-- In particular, the value at the final count is terminal. -/
theorem value_at_horizon (omega : Omega) :
    R.value K A (K.horizon omega) omega = K.limit omega := by
  exact R.value_eq_limit_of_horizon_le K A _ _ le_rfl

/-- The sequence is constant after the state-dependent final count. -/
theorem value_eq_value_of_horizon_le {n k : ℕ} (omega : Omega)
    (hn : K.horizon omega ≤ n) (hk : K.horizon omega ≤ k) :
    R.value K A n omega = R.value K A k omega := by
  rw [R.value_eq_limit_of_horizon_le K A n omega hn,
    R.value_eq_limit_of_horizon_le K A k omega hk]

/-- The bundled field gives exactly the adaptedness of the derived value. -/
theorem value_adapted (n : ℕ) :
    StronglyMeasurable[R.filtration n] (R.value K A n) := by
  change StronglyMeasurable[R.filtration n]
    (fun omega => K.value omega (R.order omega) (min n (K.horizon omega)))
  exact R.valueAdapted n

/-- Adaptedness implies ambient strong measurability. -/
theorem value_stronglyMeasurable (n : ℕ) :
    StronglyMeasurable[mOmega] (R.value K A n) :=
  (R.value_adapted K A n).mono (R.filtration.le n)

/-- The bundled moment assumption for a derived stage. -/
theorem value_memLp (n : ℕ) : MemLp (R.value K A n) 2 mu := by
  change MemLp
    (fun omega => K.value omega (R.order omega) (min n (K.horizon omega))) 2 mu
  exact R.valueMemLp n

/-- Realised persistence is an event at every stage. -/
theorem measurableSet_persistenceEvent (n : ℕ) :
    MeasurableSet (R.persistenceEvent K A n) := by
  simpa only [persistenceEvent, stageIndex] using
    R.persistenceEventMeasurable n

/-- The realised discrepancy is strongly measurable. -/
theorem discrepancy_stronglyMeasurable (n : ℕ) :
    StronglyMeasurable (R.discrepancy K A n) := by
  exact R.limitStronglyMeasurable.dist (R.value_stronglyMeasurable K A n)

/-- The realised discrepancy is measurable in the ambient sigma-algebra. -/
theorem discrepancy_measurable (n : ℕ) :
    Measurable[mOmega] (R.discrepancy K A n) :=
  (R.discrepancy_stronglyMeasurable K A n).measurable

/-- Realised discrepancies are nonnegative. -/
theorem discrepancy_nonnegative (n : ℕ) (omega : Omega) :
    0 ≤ R.discrepancy K A n omega := dist_nonneg

/-- Pointwise monotonicity of the hypothetical family restricts to pairwise
antitonicity of the realised discrepancy sequence. -/
theorem discrepancy_antitone
    (hMonotone : K.IsMonotone) {n k : ℕ} (hnk : n ≤ k)
    (omega : Omega) :
    R.discrepancy K A k omega ≤ R.discrepancy K A n omega := by
  exact IsMonotone.dist_antitone K hMonotone omega (R.order omega)
    (stageIndex_mono K hnk omega) (stageIndex_le_horizon K k omega)

/-- The adjacent almost-sure premise used by the analytic tail results is a
consequence of structural monotonicity. -/
theorem discrepancy_succ_le
    (hMonotone : K.IsMonotone) (n : ℕ) :
    R.discrepancy K A (n + 1) ≤ᵐ[mu] R.discrepancy K A n := by
  exact ae_of_all mu (R.discrepancy_antitone K A hMonotone (Nat.le_succ n))

/-- Fixedness of the hypothetical family restricts to every stage of the
realised process. -/
theorem value_eq_limit_of_fixed (hFixed : K.IsFixed) (n : ℕ) :
    R.value K A n = K.limit := by
  funext omega
  exact hFixed omega (R.order omega) (stageIndex K n omega)
    (stageIndex_le_horizon K n omega)

/-- Absorbing-class coverage gives a single full-measure set on which the
realised persistence/equality equivalence holds at every stage. -/
theorem persistenceEvent_iff_value_eq_of_absorbingCoverage
    (hCoverage : AbsorbingCoverage K A mu) :
    ∀ᵐ omega ∂mu, ∀ n,
      omega ∈ R.persistenceEvent K A n ↔
        R.value K A n omega = K.limit omega := by
  filter_upwards [hCoverage] with omega hCoverageOmega
  intro n
  constructor
  · exact realizedPersistence_implies_equality K A (R.stage K A n) omega
  · intro hEquality
    exact hCoverageOmega (R.order omega) (stageIndex K n omega)
      (stageIndex_le_horizon K n omega) hEquality

end RealizedObservedProcess

end StructuralPresentation
end HypotheticalSequentialEstimand

end

end SequentialLearning
