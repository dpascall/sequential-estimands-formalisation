import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.Topology.MetricSpace.Defs

/-!
Scratch development for structural constraints and estimand classes.
-/

namespace SequentialLearning

open Filter MeasureTheory Set
open scoped ENNReal MeasureTheory

noncomputable section

universe uOmega uS uPrefix uOrder

/-- A pathwise family of hypothetical sequential estimands.  `Order omega`
is the type of admissible revelation orders at state `omega`; `revealedPrefix`
records exactly the information revealed by an order at a stage. -/
structure HypotheticalSequentialEstimand
    (Omega : Type uOmega) (S : Type uS) (Prefix : Type uPrefix) where
  horizon : Omega → ℕ
  Order : Omega → Type uOrder
  orderNonempty : ∀ omega, Nonempty (Order omega)
  revealedPrefix : (omega : Omega) → Order omega → ℕ → Prefix
  value : (omega : Omega) → Order omega → ℕ → S
  limit : Omega → S
  valuePrefixCompatible : ∀ omega (xi xi' : Order omega) n,
    n ≤ horizon omega →
      revealedPrefix omega xi n = revealedPrefix omega xi' n →
      value omega xi n = value omega xi' n
  terminal : ∀ omega (xi : Order omega),
    value omega xi (horizon omega) = limit omega

namespace HypotheticalSequentialEstimand

variable {Omega : Type uOmega} {S : Type uS} {Prefix : Type uPrefix}
  (K : HypotheticalSequentialEstimand Omega S Prefix)

/-- A structural constraint is a prefix-compatible predicate on state,
revelation order, and stage. -/
structure StructuralConstraint where
  fires : (omega : Omega) → K.Order omega → ℕ → Prop
  nonanticipating : ∀ omega (xi xi' : K.Order omega) n,
    n ≤ K.horizon omega →
      K.revealedPrefix omega xi n = K.revealedPrefix omega xi' n →
      (fires omega xi n ↔ fires omega xi' n)

namespace StructuralConstraint

variable {K}

@[ext]
theorem ext {c d : K.StructuralConstraint}
    (h : c.fires = d.fires) : c = d := by
  cases c
  cases d
  simp_all

end StructuralConstraint

/-- Every member of a constraint family preserves literal equality with the
limit whenever it fires. -/
def ConstraintFamilyValuePreserving
    (C : Set K.StructuralConstraint) : Prop :=
  ∀ c ∈ C, ∀ omega (xi : K.Order omega) n,
    n < K.horizon omega → c.fires omega xi n →
      K.value omega xi n = K.limit omega →
        K.value omega xi (n + 1) = K.limit omega

/-- If a firing constraint ceases to fire after equality has been reached,
another member of the same family fires at the next stage. -/
def ConstraintFamilyStructurallySupported
    (C : Set K.StructuralConstraint) : Prop :=
  ∀ c ∈ C, ∀ omega (xi : K.Order omega) n,
    n < K.horizon omega → c.fires omega xi n →
      K.value omega xi n = K.limit omega →
      ¬c.fires omega xi (n + 1) →
        ∃ c' ∈ C, c'.fires omega xi (n + 1)

/-- Collective validity of a family of structural constraints. -/
def ValidConstraintFamily (C : Set K.StructuralConstraint) : Prop :=
  K.ConstraintFamilyValuePreserving C ∧
    K.ConstraintFamilyStructurallySupported C

/-- `C` is the greatest valid family under inclusion.  This is stronger than
mere maximality and makes the family canonical whenever it exists. -/
def IsGreatestValidConstraintFamily
    (C : Set K.StructuralConstraint) : Prop :=
  K.ValidConstraintFamily C ∧
    ∀ D : Set K.StructuralConstraint, K.ValidConstraintFamily D → D ⊆ C

theorem greatestValidConstraintFamily_unique
    {C D : Set K.StructuralConstraint}
    (hC : K.IsGreatestValidConstraintFamily C)
    (hD : K.IsGreatestValidConstraintFamily D) : C = D := by
  exact Set.Subset.antisymm (hD.2 C hC.1) (hC.2 D hD.1)

/-- The canonical family consists of every constraint that belongs to at
least one collectively valid family.  Equivalently, it is the union of all
valid families. -/
def canonicalConstraintFamily : Set K.StructuralConstraint :=
  {c | ∃ C : Set K.StructuralConstraint, K.ValidConstraintFamily C ∧ c ∈ C}

/-- Arbitrary unions of valid constraint families are valid: a support
witness for a constraint can be taken from the particular valid family that
contained that constraint. -/
theorem canonicalConstraintFamily_valid :
    K.ValidConstraintFamily K.canonicalConstraintFamily := by
  constructor
  · intro c hc omega xi n hn hFire hEq
    rcases hc with ⟨C, hC, hcC⟩
    exact hC.1 c hcC omega xi n hn hFire hEq
  · intro c hc omega xi n hn hFire hEq hStops
    rcases hc with ⟨C, hC, hcC⟩
    rcases hC.2 c hcC omega xi n hn hFire hEq hStops with ⟨c', hc'C, hc'Fire⟩
    exact ⟨c', ⟨C, hC, hc'C⟩, hc'Fire⟩

theorem canonicalConstraintFamily_greatest :
    K.IsGreatestValidConstraintFamily K.canonicalConstraintFamily := by
  refine ⟨K.canonicalConstraintFamily_valid, ?_⟩
  intro C hC c hc
  exact ⟨C, hC, hc⟩

/-- A hypothetical sequential estimand together with its canonical greatest
valid family of structural constraints. -/
structure StructuralPresentation where
  constraints : Set K.StructuralConstraint
  greatest : K.IsGreatestValidConstraintFamily constraints

/-- Every hypothetical sequential estimand has a canonical structural
presentation; existence of a greatest family is therefore a theorem, not an
additional model assumption. -/
def canonicalStructuralPresentation : K.StructuralPresentation where
  constraints := K.canonicalConstraintFamily
  greatest := K.canonicalConstraintFamily_greatest

namespace StructuralPresentation

variable (A : K.StructuralPresentation)

theorem constraints_eq_canonical :
    A.constraints = K.canonicalConstraintFamily := by
  exact K.greatestValidConstraintFamily_unique A.greatest
    K.canonicalConstraintFamily_greatest

/-- Literal equality with the limit at a preterminal or terminal stage. -/
def EqualAt (omega : Omega) (xi : K.Order omega) (n : ℕ) : Prop :=
  n ≤ K.horizon omega ∧ K.value omega xi n = K.limit omega

/-- Some member of the canonical family fires at a stage. -/
def SupportedAt (omega : Omega) (xi : K.Order omega) (n : ℕ) : Prop :=
  ∃ c ∈ A.constraints, c.fires omega xi n

/-- The hypothetical persistence event: literal equality together with a
currently instantiated valid constraint. -/
def PersistenceAt (omega : Omega) (xi : K.Order omega) (n : ℕ) : Prop :=
  EqualAt K omega xi n ∧ SupportedAt K A omega xi n

theorem persistence_equalAt {omega : Omega} {xi : K.Order omega} {n : ℕ}
    (h : PersistenceAt K A omega xi n) : EqualAt K omega xi n := h.1

theorem persistence_succ {omega : Omega} {xi : K.Order omega} {n : ℕ}
    (hn : n < K.horizon omega)
    (h : PersistenceAt K A omega xi n) :
    PersistenceAt K A omega xi (n + 1) := by
  rcases h with ⟨⟨_, hEq⟩, c, hcC, hcFire⟩
  have hEqNext : K.value omega xi (n + 1) = K.limit omega :=
    A.greatest.1.1 c hcC omega xi n hn hcFire hEq
  refine ⟨⟨Nat.succ_le_iff.2 hn, hEqNext⟩, ?_⟩
  by_cases hcNext : c.fires omega xi (n + 1)
  · exact ⟨c, hcC, hcNext⟩
  · exact A.greatest.1.2 c hcC omega xi n hn hcFire hEq hcNext

theorem persistence_mono {omega : Omega} {xi : K.Order omega} {n m : ℕ}
    (hnm : n ≤ m) (hm : m ≤ K.horizon omega)
    (h : PersistenceAt K A omega xi n) :
    PersistenceAt K A omega xi m := by
  induction m, hnm using Nat.le_induction with
  | base => exact h
  | succ m hnm ih =>
      exact persistence_succ K A (Nat.lt_of_succ_le hm)
        (ih (Nat.le_of_succ_le hm))

/-- A subfamily is a complete certificate when it lies in the canonical
family and is itself closed under value preservation and structural support. -/
def IsCompleteCertificate (B : Set K.StructuralConstraint) : Prop :=
  B ⊆ A.constraints ∧ K.ValidConstraintFamily B

theorem validFamily_isCompleteCertificate
    {B : Set K.StructuralConstraint} (hB : K.ValidConstraintFamily B) :
    IsCompleteCertificate K A B := by
  exact ⟨A.greatest.2 B hB, hB⟩

theorem completeCertificate_persistence
    {B : Set K.StructuralConstraint} (hB : IsCompleteCertificate K A B)
    {omega : Omega} {xi : K.Order omega} {n : ℕ}
    (hn : n ≤ K.horizon omega)
    (hEq : K.value omega xi n = K.limit omega)
    (hFire : ∃ c ∈ B, c.fires omega xi n) :
    PersistenceAt K A omega xi n := by
  rcases hFire with ⟨c, hcB, hcFire⟩
  exact ⟨⟨hn, hEq⟩, c, hB.1 hcB, hcFire⟩

/-- To certify persistence it is enough to exhibit any valid family whose
member currently fires; identifying the remainder of the canonical family is
unnecessary. -/
theorem validSubfamily_persistence
    {B : Set K.StructuralConstraint} (hB : K.ValidConstraintFamily B)
    {omega : Omega} {xi : K.Order omega} {n : ℕ}
    (hn : n ≤ K.horizon omega)
    (hEq : K.value omega xi n = K.limit omega)
    (hFire : ∃ c ∈ B, c.fires omega xi n) :
    PersistenceAt K A omega xi n := by
  exact completeCertificate_persistence K A
    (validFamily_isCompleteCertificate K A hB) hn hEq hFire

/-- The constraint that fires exactly at the terminal stage. -/
def terminalConstraint : K.StructuralConstraint where
  fires omega _ n := n = K.horizon omega
  nonanticipating := by simp

theorem singleton_terminalConstraint_valid :
    K.ValidConstraintFamily ({terminalConstraint K} : Set K.StructuralConstraint) := by
  constructor
  · intro c hc omega xi n hn hFire
    rw [Set.mem_singleton_iff] at hc
    subst c
    change n = K.horizon omega at hFire
    subst n
    exact (Nat.lt_irrefl _ hn).elim
  · intro c hc omega xi n hn hFire
    rw [Set.mem_singleton_iff] at hc
    subst c
    change n = K.horizon omega at hFire
    subst n
    exact (Nat.lt_irrefl _ hn).elim

theorem terminalConstraint_mem_canonical :
    terminalConstraint K ∈ A.constraints := by
  exact A.greatest.2 _ (singleton_terminalConstraint_valid K) (Set.mem_singleton _)

/-- Terminal equality is always structurally persistent: the canonical
family contains the vacuously valid terminal-stage constraint. -/
theorem terminal_persistence {omega : Omega} (xi : K.Order omega) :
    PersistenceAt K A omega xi (K.horizon omega) := by
  exact ⟨⟨le_rfl, K.terminal omega xi⟩, terminalConstraint K,
    terminalConstraint_mem_canonical K A, rfl⟩

end StructuralPresentation

section Classes

variable [PseudoMetricSpace S]

/-- Pointwise monotonicity of discrepancy along every hypothetical order. -/
def IsMonotone : Prop :=
  ∀ omega (xi : K.Order omega) n, n < K.horizon omega →
    dist (K.limit omega) (K.value omega xi (n + 1)) ≤
      dist (K.limit omega) (K.value omega xi n)

/-- Pointwise fixedness along every hypothetical order.  Literal equality is
used rather than zero pseudometric distance. -/
def IsFixed : Prop :=
  ∀ omega (xi : K.Order omega) n, n ≤ K.horizon omega →
    K.value omega xi n = K.limit omega

theorem fixed_isMonotone (hFixed : K.IsFixed) : K.IsMonotone := by
  intro omega xi n hn
  rw [hFixed omega xi (n + 1) (Nat.succ_le_iff.2 hn),
    hFixed omega xi n hn.le]

namespace StructuralPresentation

variable (A : K.StructuralPresentation)

/-- States on which literal equality is reached at a preterminal stage under
at least one admissible order. -/
def EqualityAchievableSet : Set Omega :=
  {omega | ∃ xi : K.Order omega, ∃ n : ℕ,
    n < K.horizon omega ∧ K.value omega xi n = K.limit omega}

/-- States on which structural persistence is reached preterminally. -/
def PersistenceAchievableSet : Set Omega :=
  {omega | ∃ xi : K.Order omega, ∃ n : ℕ,
    n < K.horizon omega ∧ PersistenceAt K A omega xi n}

/-- States exhibiting at least one preterminal literal equality that is not
structurally certified. -/
def AccidentalEqualitySet : Set Omega :=
  {omega | ∃ xi : K.Order omega, ∃ n : ℕ,
    n < K.horizon omega ∧ K.value omega xi n = K.limit omega ∧
      ¬PersistenceAt K A omega xi n}

omit [PseudoMetricSpace S] in
theorem persistenceAchievableSet_subset_equalityAchievableSet :
    PersistenceAchievableSet K A ⊆ EqualityAchievableSet K := by
  rintro omega ⟨xi, n, hn, hPersistence⟩
  exact ⟨xi, n, hn, hPersistence.1.2⟩

omit [PseudoMetricSpace S] in
theorem accidentalEqualitySet_subset_equalityAchievableSet :
    AccidentalEqualitySet K A ⊆ EqualityAchievableSet K := by
  rintro omega ⟨xi, n, hn, hEq, _⟩
  exact ⟨xi, n, hn, hEq⟩

variable [MeasurableSpace Omega]

def EqualityAchievable (mu : Measure Omega) : Prop :=
  0 < mu (EqualityAchievableSet K)

def PersistenceAchievable (mu : Measure Omega) : Prop :=
  0 < mu (PersistenceAchievableSet K A)

def AccidentalEqualityAchievable (mu : Measure Omega) : Prop :=
  0 < mu (AccidentalEqualitySet K A)

/-- Absorbing coverage is an almost-sure statement about every order-stage
pair, including the terminal stage, exactly as in the manuscript. -/
def AbsorbingCoverage (mu : Measure Omega) : Prop :=
  ∀ᵐ omega ∂mu, ∀ (xi : K.Order omega) n,
    n ≤ K.horizon omega → K.value omega xi n = K.limit omega →
      PersistenceAt K A omega xi n

omit [PseudoMetricSpace S] in
theorem persistenceAchievable_implies_equalityAchievable
    (mu : Measure Omega) (h : PersistenceAchievable K A mu) :
    EqualityAchievable K mu := by
  exact h.trans_le (measure_mono
    (persistenceAchievableSet_subset_equalityAchievableSet K A))

omit [PseudoMetricSpace S] in
theorem accidentalEqualityAchievable_implies_equalityAchievable
    (mu : Measure Omega) (h : AccidentalEqualityAchievable K A mu) :
    EqualityAchievable K mu := by
  exact h.trans_le (measure_mono
    (accidentalEqualitySet_subset_equalityAchievableSet K A))

omit [PseudoMetricSpace S] [MeasurableSpace Omega] in
theorem not_mem_accidentalEqualitySet_iff (omega : Omega) :
    omega ∉ AccidentalEqualitySet K A ↔
      ∀ (xi : K.Order omega) n, n < K.horizon omega →
        K.value omega xi n = K.limit omega →
          PersistenceAt K A omega xi n := by
  simp only [AccidentalEqualitySet, Set.mem_ofPred_eq, not_exists, not_and]
  aesop

omit [PseudoMetricSpace S] in
theorem absorbingCoverage_iff_ae_not_mem (mu : Measure Omega) :
    AbsorbingCoverage K A mu ↔
      ∀ᵐ omega ∂mu, omega ∉ AccidentalEqualitySet K A := by
  constructor
  · intro h
    filter_upwards [h] with omega homega
    exact (not_mem_accidentalEqualitySet_iff K A omega).2
      (fun xi n hn => homega xi n hn.le)
  · intro h
    filter_upwards [h] with omega homega
    intro xi n hn hEq
    rcases hn.lt_or_eq with hnlt | rfl
    · exact (not_mem_accidentalEqualitySet_iff K A omega).1 homega xi n hnlt hEq
    · exact terminal_persistence K A xi

omit [PseudoMetricSpace S] in
theorem absorbingCoverage_iff_measure_accidental_eq_zero
    (mu : Measure Omega) :
    AbsorbingCoverage K A mu ↔ mu (AccidentalEqualitySet K A) = 0 := by
  rw [absorbingCoverage_iff_ae_not_mem K A mu, ae_iff]
  simp

theorem not_accidentalEqualityAchievable_iff_absorbingCoverage
    (mu : Measure Omega) :
    ¬AccidentalEqualityAchievable K A mu ↔ AbsorbingCoverage K A mu := by
  rw [AccidentalEqualityAchievable,
    absorbingCoverage_iff_measure_accidental_eq_zero]
  constructor
  · intro h
    exact bot_unique (le_of_not_gt h)
  · intro hzero hpos
    rw [hzero] at hpos
    exact (lt_irrefl 0) hpos

/-- The measurability assumptions needed to regard the three achievability
sets as events.  They are deliberately separate from the pathwise structural
definitions. -/
structure ClassEventsMeasurable : Prop where
  equality : MeasurableSet (EqualityAchievableSet K)
  persistence : MeasurableSet (PersistenceAchievableSet K A)
  accidental : MeasurableSet (AccidentalEqualitySet K A)

/-- The nine estimand classes from the manuscript. -/
inductive EstimandClass
  | fixed
  | absorbingMonotone
  | absorbingNonmonotone
  | mixedMonotone
  | mixedNonmonotone
  | nonabsorbingMonotone
  | nonabsorbingNonmonotone
  | terminalMonotone
  | terminalNonmonotone
  deriving DecidableEq

/-- Membership in an estimand class.  Geometry and fixedness are pointwise;
achievability and absorbing coverage are properties under the law `mu`. -/
def HasClass (mu : Measure Omega) : EstimandClass → Prop
  | .fixed => K.IsFixed
  | .absorbingMonotone =>
      K.IsMonotone ∧ ¬K.IsFixed ∧ PersistenceAchievable K A mu ∧
        AbsorbingCoverage K A mu
  | .absorbingNonmonotone =>
      ¬K.IsMonotone ∧ ¬K.IsFixed ∧ PersistenceAchievable K A mu ∧
        AbsorbingCoverage K A mu
  | .mixedMonotone =>
      K.IsMonotone ∧ ¬K.IsFixed ∧ PersistenceAchievable K A mu ∧
        AccidentalEqualityAchievable K A mu
  | .mixedNonmonotone =>
      ¬K.IsMonotone ∧ ¬K.IsFixed ∧ PersistenceAchievable K A mu ∧
        AccidentalEqualityAchievable K A mu
  | .nonabsorbingMonotone =>
      K.IsMonotone ∧ ¬K.IsFixed ∧ EqualityAchievable K mu ∧
        ¬PersistenceAchievable K A mu
  | .nonabsorbingNonmonotone =>
      ¬K.IsMonotone ∧ ¬K.IsFixed ∧ EqualityAchievable K mu ∧
        ¬PersistenceAchievable K A mu
  | .terminalMonotone =>
      K.IsMonotone ∧ ¬K.IsFixed ∧ ¬EqualityAchievable K mu
  | .terminalNonmonotone =>
      ¬K.IsMonotone ∧ ¬K.IsFixed ∧ ¬EqualityAchievable K mu

/-- A canonical classifier obtained by deciding the defining propositions.
This definition is noncomputable because those propositions need not be
decidable constructively. -/
noncomputable def classify (mu : Measure Omega) : EstimandClass :=
  by
    classical
    exact
      if K.IsFixed then .fixed
      else if K.IsMonotone then
        if EqualityAchievable K mu then
          if PersistenceAchievable K A mu then
            if AccidentalEqualityAchievable K A mu then .mixedMonotone
            else .absorbingMonotone
          else .nonabsorbingMonotone
        else .terminalMonotone
      else
        if EqualityAchievable K mu then
          if PersistenceAchievable K A mu then
            if AccidentalEqualityAchievable K A mu then .mixedNonmonotone
            else .absorbingNonmonotone
          else .nonabsorbingNonmonotone
        else .terminalNonmonotone

theorem classify_hasClass (mu : Measure Omega) :
    HasClass K A mu (classify K A mu) := by
  classical
  unfold classify
  split_ifs <;>
    simp_all [HasClass,
      not_accidentalEqualityAchievable_iff_absorbingCoverage]

theorem hasClass_unique (mu : Measure Omega) {c d : EstimandClass}
    (hc : HasClass K A mu c) (hd : HasClass K A mu d) : c = d := by
  have hPersistenceImpliesEquality :=
    persistenceAchievable_implies_equalityAchievable K A mu
  have hAccidentalImpliesEquality :=
    accidentalEqualityAchievable_implies_equalityAchievable K A mu
  have hCoverage :
      AbsorbingCoverage K A mu ↔ ¬AccidentalEqualityAchievable K A mu :=
    (not_accidentalEqualityAchievable_iff_absorbingCoverage K A mu).symm
  cases c <;> cases d <;>
    simp_all [HasClass]

theorem existsUnique_estimandClass (mu : Measure Omega) :
    ∃! c, HasClass K A mu c := by
  refine ⟨classify K A mu, classify_hasClass K A mu, ?_⟩
  intro c hc
  exact hasClass_unique K A mu hc (classify_hasClass K A mu)

/-- The exact-equality predicate is itself a nonanticipating constraint.  It
need not be valid in a pseudometric space: zero discrepancy at the next stage
does not in general imply literal equality. -/
def equalityConstraint : K.StructuralConstraint where
  fires omega xi n := K.value omega xi n = K.limit omega
  nonanticipating := by
    intro omega xi xi' n hn hPrefix
    rw [K.valuePrefixCompatible omega xi xi' n hn hPrefix]

omit [MeasurableSpace Omega] in
/-- Under a separating distance, pointwise monotonicity propagates literal
equality one step.  `hSeparates` is exactly the extra fact unavailable in a
general pseudometric space. -/
theorem monotone_literalEquality_succ
    (hSeparates : ∀ x y : S, dist x y = 0 → x = y)
    (hMonotone : K.IsMonotone) {omega : Omega} {xi : K.Order omega} {n : ℕ}
    (hn : n < K.horizon omega)
    (hEq : K.value omega xi n = K.limit omega) :
    K.value omega xi (n + 1) = K.limit omega := by
  have hUpper : dist (K.limit omega) (K.value omega xi (n + 1)) ≤ 0 := by
    simpa [hEq] using hMonotone omega xi n hn
  have hZero : dist (K.limit omega) (K.value omega xi (n + 1)) = 0 :=
    le_antisymm hUpper dist_nonneg
  exact (hSeparates _ _ hZero).symm

omit [MeasurableSpace Omega] in
/-- In a distance-separating space, the singleton exact-equality family is a
valid constraint family for every pointwise monotone estimand. -/
theorem singleton_equalityConstraint_valid
    (hSeparates : ∀ x y : S, dist x y = 0 → x = y)
    (hMonotone : K.IsMonotone) :
    K.ValidConstraintFamily ({equalityConstraint K} : Set K.StructuralConstraint) := by
  constructor
  · intro c hc omega xi n hn _ hEq
    rw [Set.mem_singleton_iff] at hc
    subst c
    exact monotone_literalEquality_succ K hSeparates hMonotone hn hEq
  · intro c hc omega xi n hn _ hEq _
    rw [Set.mem_singleton_iff] at hc
    subst c
    refine ⟨equalityConstraint K, Set.mem_singleton _, ?_⟩
    exact monotone_literalEquality_succ K hSeparates hMonotone hn hEq

omit [MeasurableSpace Omega] in
theorem equalityConstraint_mem_canonical
    (hSeparates : ∀ x y : S, dist x y = 0 → x = y)
    (hMonotone : K.IsMonotone) : equalityConstraint K ∈ A.constraints := by
  exact A.greatest.2 _ (singleton_equalityConstraint_valid K hSeparates hMonotone)
    (Set.mem_singleton _)

/-- In a distance-separating space every literal equality of a monotone
estimand is structurally persistent. -/
theorem separating_monotone_equalAt_persistence
    (hSeparates : ∀ x y : S, dist x y = 0 → x = y)
    (hMonotone : K.IsMonotone) {omega : Omega} {xi : K.Order omega} {n : ℕ}
    (hn : n ≤ K.horizon omega)
    (hEq : K.value omega xi n = K.limit omega) :
    PersistenceAt K A omega xi n := by
  exact ⟨⟨hn, hEq⟩, equalityConstraint K,
    equalityConstraint_mem_canonical K A hSeparates hMonotone, hEq⟩

theorem separating_monotone_absorbingCoverage
    (mu : Measure Omega)
    (hSeparates : ∀ x y : S, dist x y = 0 → x = y)
    (hMonotone : K.IsMonotone) : AbsorbingCoverage K A mu := by
  filter_upwards [] with omega xi n hn hEq
  exact separating_monotone_equalAt_persistence K A hSeparates hMonotone hn hEq

theorem separating_monotone_equalitySet_subset_persistenceSet
    (hSeparates : ∀ x y : S, dist x y = 0 → x = y)
    (hMonotone : K.IsMonotone) :
    EqualityAchievableSet K ⊆ PersistenceAchievableSet K A := by
  rintro omega ⟨xi, n, hn, hEq⟩
  exact ⟨xi, n, hn,
    separating_monotone_equalAt_persistence K A hSeparates hMonotone hn.le hEq⟩

theorem separating_monotone_equalityAchievable_implies_persistenceAchievable
    (mu : Measure Omega)
    (hSeparates : ∀ x y : S, dist x y = 0 → x = y)
    (hMonotone : K.IsMonotone) (hEquality : EqualityAchievable K mu) :
    PersistenceAchievable K A mu := by
  exact hEquality.trans_le (measure_mono
    (separating_monotone_equalitySet_subset_persistenceSet K A hSeparates hMonotone))

theorem separating_not_mixedMonotone
    (mu : Measure Omega)
    (hSeparates : ∀ x y : S, dist x y = 0 → x = y) :
    ¬HasClass K A mu .mixedMonotone := by
  intro hClass
  have hCoverage := separating_monotone_absorbingCoverage K A mu hSeparates hClass.1
  have hNotAccidental :=
    (not_accidentalEqualityAchievable_iff_absorbingCoverage K A mu).2 hCoverage
  exact hNotAccidental hClass.2.2.2

theorem separating_not_nonabsorbingMonotone
    (mu : Measure Omega)
    (hSeparates : ∀ x y : S, dist x y = 0 → x = y) :
    ¬HasClass K A mu .nonabsorbingMonotone := by
  intro hClass
  exact hClass.2.2.2
    (separating_monotone_equalityAchievable_implies_persistenceAchievable
      K A mu hSeparates hClass.1 hClass.2.2.1)

end StructuralPresentation

end Classes

section MetricClassCorollaries

variable [MetricSpace S] [MeasurableSpace Omega]
  (A : K.StructuralPresentation)

namespace StructuralPresentation

theorem metric_monotone_absorbingCoverage (mu : Measure Omega)
    (hMonotone : K.IsMonotone) : AbsorbingCoverage K A mu := by
  exact separating_monotone_absorbingCoverage K A mu
    (fun _ _ => eq_of_dist_eq_zero) hMonotone

theorem metric_not_mixedMonotone (mu : Measure Omega) :
    ¬HasClass K A mu .mixedMonotone := by
  exact separating_not_mixedMonotone K A mu (fun _ _ => eq_of_dist_eq_zero)

theorem metric_not_nonabsorbingMonotone (mu : Measure Omega) :
    ¬HasClass K A mu .nonabsorbingMonotone := by
  exact separating_not_nonabsorbingMonotone K A mu (fun _ _ => eq_of_dist_eq_zero)

end StructuralPresentation

end MetricClassCorollaries

end HypotheticalSequentialEstimand

end

end SequentialLearning
