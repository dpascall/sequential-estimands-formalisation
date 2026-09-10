import SequentialLearning.AbsorbingMSE
import SequentialLearning.StructuralEstimandClasses

/-!
# Absorbing-class membership supplies the MSE hypotheses

This module connects the hypothetical-path taxonomy to the realised-path
corollary in `AbsorbingMSE.lean`.  A realised stage selects one admissible
order and one applicable index at each latent state.  Structural persistence
gives the pointwise equality direction, while absorbing-class coverage gives
the reverse direction on a single full-measure set.
-/

namespace SequentialLearning

open Filter MeasureTheory Set
open scoped ENNReal MeasureTheory ProbabilityTheory

noncomputable section

universe uOmega uH uPrefix

namespace HypotheticalSequentialEstimand
namespace StructuralPresentation

variable {Omega : Type uOmega} {H : Type uH} {Prefix : Type uPrefix}
  (K : HypotheticalSequentialEstimand Omega H Prefix)
  (A : K.StructuralPresentation)

/-- An observed restriction of the hypothetical family at one (possibly
state-dependent) applicable stage.  `order` represents the realised
revelation order. -/
structure RealizedStage where
  order : (omega : Omega) → K.Order omega
  index : Omega → ℕ
  applicable : ∀ omega, index omega ≤ K.horizon omega

variable (R : RealizedStage K)

/-- The stage estimand on the realised path. -/
def RealizedStage.value (omega : Omega) : H :=
  K.value omega (R.order omega) (R.index omega)

/-- The observed persistence event obtained by restricting the hypothetical
persistence event to the realised order and stage. -/
def RealizedStage.persistenceEvent : Set Omega :=
  {omega | PersistenceAt K A omega (R.order omega) (R.index omega)}

theorem realizedPersistence_implies_equality
    (omega : Omega) (hPersistence : omega ∈ R.persistenceEvent K A) :
    R.value K omega = K.limit omega := by
  exact hPersistence.1.2

variable [mOmega : MeasurableSpace Omega]

section PseudometricBridge

variable [PseudoMetricSpace H]

omit [PseudoMetricSpace H] in
/-- Absorbing coverage over all hypothetical paths restricts to the observed
path, even when its order and stage depend on the latent state. -/
theorem absorbingCoverage_realized
    (mu : Measure Omega) (hCoverage : AbsorbingCoverage K A mu) :
    ∀ᵐ omega ∂mu,
      R.value K omega = K.limit omega → omega ∈ R.persistenceEvent K A := by
  filter_upwards [hCoverage] with omega hCoverageOmega
  intro hEquality
  exact hCoverageOmega (R.order omega) (R.index omega)
    (R.applicable omega) hEquality

omit mOmega [PseudoMetricSpace H] in
/-- Fixedness makes the singleton exact-equality constraint valid without any
separation assumption on the pseudometric. -/
theorem singleton_equalityConstraint_valid_of_fixed (hFixed : K.IsFixed) :
    K.ValidConstraintFamily ({equalityConstraint K} : Set K.StructuralConstraint) := by
  constructor
  · intro c hc omega xi n hn _ _
    rw [Set.mem_singleton_iff] at hc
    subst c
    exact hFixed omega xi (n + 1) (Nat.succ_le_iff.2 hn)
  · intro c hc omega xi n hn _ _ _
    rw [Set.mem_singleton_iff] at hc
    subst c
    refine ⟨equalityConstraint K, Set.mem_singleton _, ?_⟩
    exact hFixed omega xi (n + 1) (Nat.succ_le_iff.2 hn)

omit [PseudoMetricSpace H] in
/-- The fixed class is a degenerate absorbing class: exact equality is
structurally certified at every applicable stage. -/
theorem fixed_absorbingCoverage (mu : Measure Omega) (hFixed : K.IsFixed) :
    AbsorbingCoverage K A mu := by
  have hConstraint : equalityConstraint K ∈ A.constraints :=
    A.greatest.2 _ (singleton_equalityConstraint_valid_of_fixed K hFixed)
      (Set.mem_singleton _)
  filter_upwards [] with omega xi n hn hEquality
  exact ⟨⟨hn, hEquality⟩, equalityConstraint K, hConstraint, hEquality⟩

namespace EstimandClass

/-- The absorbing classes, including fixed estimands as the degenerate case. -/
def IsAbsorbing : EstimandClass → Prop
  | .fixed | .absorbingMonotone | .absorbingNonmonotone => True
  | _ => False

end EstimandClass

/-- Membership in either absorbing class supplies absorbing coverage. -/
theorem hasClass_absorbingCoverage (mu : Measure Omega) (c : EstimandClass)
    (hClass : HasClass K A mu c) (hAbsorbing : c.IsAbsorbing) :
    AbsorbingCoverage K A mu := by
  cases c with
  | fixed => exact fixed_absorbingCoverage K A mu hClass
  | absorbingMonotone => exact hClass.2.2.2
  | absorbingNonmonotone => exact hClass.2.2.2
  | mixedMonotone | mixedNonmonotone | nonabsorbingMonotone |
      nonabsorbingNonmonotone | terminalMonotone | terminalNonmonotone =>
      simp [EstimandClass.IsAbsorbing] at hAbsorbing

/-- The two realised-path hypotheses of `absorbing_classes_mse_bound` follow
directly from membership in either absorbing estimand class. -/
theorem absorbingClass_realized_hypotheses
    (mu : Measure Omega) (c : EstimandClass)
    (hClass : HasClass K A mu c) (hAbsorbing : c.IsAbsorbing) :
    (∀ omega, omega ∈ R.persistenceEvent K A →
      R.value K omega = K.limit omega) ∧
    (∀ᵐ omega ∂mu,
      R.value K omega = K.limit omega →
        omega ∈ R.persistenceEvent K A) := by
  exact ⟨realizedPersistence_implies_equality K A R,
    absorbingCoverage_realized K A R mu
      (hasClass_absorbingCoverage K A mu c hClass hAbsorbing)⟩

end PseudometricBridge

/-- Closed absorbing-class MSE bound.  The caller supplies only class
membership and the analytic measurability/moment hypotheses; the structural
persistence and absorbing-coverage assumptions have been discharged. -/
theorem absorbingClass_realized_mse_bound
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (c : EstimandClass)
    (hClass : HasClass K A mu c) (hAbsorbing : c.IsAbsorbing)
    (m : MeasurableSpace Omega) (hm : m ≤ mOmega)
    (hLimitMeasurable : StronglyMeasurable[mOmega] K.limit)
    (hCurrentMeasurable : StronglyMeasurable[mOmega] (R.value K))
    (hLimit : MemLp K.limit 2 mu) (hCurrent : MemLp (R.value K) 2 mu) :
    ∀ᵐ omega ∂mu,
      posteriorMSE mu m K.limit (R.value K) omega ≤
        posteriorVariance mu m K.limit omega +
          (mu⟦(R.persistenceEvent K A)ᶜ | m⟧) omega *
            conditionalSquaredDiscrepancy mu m K.limit (R.value K) omega := by
  rcases @absorbingClass_realized_hypotheses
      Omega H Prefix K A R mOmega _ mu c hClass hAbsorbing with
    ⟨hPersistence, hCoverage⟩
  exact absorbing_classes_mse_bound
    mu m hm K.limit (R.value K) (R.persistenceEvent K A)
      hLimitMeasurable hCurrentMeasurable hLimit hCurrent
      hPersistence hCoverage

end StructuralPresentation
end HypotheticalSequentialEstimand

end

end SequentialLearning
