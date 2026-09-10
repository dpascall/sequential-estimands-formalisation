import SequentialLearning.FlagSpace
import SequentialLearning.NoisyObservationModels
import SequentialLearning.StructuralEstimandClasses
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Canonical witnesses for all nine structural classes

The table uses the spare branch bit of the 256-state noisy-channel model.
Literal equality is visible in `FlagSpace ℝ`, while its pseudometric ignores
the flag.  This makes the two monotone accidental-equality rows possible
without changing any geometric observation verdict.
-/

namespace SequentialLearning

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal MeasureTheory ProbabilityTheory

noncomputable section

namespace StructuralWitnesses

open HypotheticalSequentialEstimand
open HypotheticalSequentialEstimand.StructuralPresentation

abbrev Omega := NoisyObservationModel.LatentState
abbrev Target := FlagSpace ℝ
abbrev Prefix := Unit

def mu : Measure Omega := NoisyObservationModel.latentLaw

instance : IsProbabilityMeasure mu := by
  dsimp [mu]
  infer_instance

def limitValue : Target := ⟨0, true⟩
def hiddenZero : Target := ⟨0, false⟩
def point (x : ℝ) : Target := ⟨x, false⟩

def nonmonotoneStart : EstimandClass → Bool
  | .absorbingNonmonotone | .mixedNonmonotone |
      .nonabsorbingNonmonotone | .terminalNonmonotone => true
  | _ => false

def genericRow (start : ℝ) (stage4 stage5 : Target) : ℕ → Target
  | 0 => point start
  | 1 => point 2
  | 2 => point 1
  | 3 => point 1
  | 4 => stage4
  | 5 => stage5
  | _ => limitValue

/-- The eight non-fixed rows share the equality stage `4`.  Accidental rows
break equality at stage `5`; all rows terminate at stage `6`. -/
def rowValue : EstimandClass → Omega → ℕ → Target
  | .fixed, _, _ => limitValue
  | .absorbingMonotone, _, n => genericRow 3 limitValue limitValue n
  | .absorbingNonmonotone, _, n => genericRow 1 limitValue limitValue n
  | .mixedMonotone, omega, n =>
      genericRow 3 limitValue
        (if omega.branch then hiddenZero else limitValue) n
  | .mixedNonmonotone, omega, n =>
      genericRow 1 limitValue
        (if omega.branch then hiddenZero else limitValue) n
  | .nonabsorbingMonotone, _, n => genericRow 3 limitValue hiddenZero n
  | .nonabsorbingNonmonotone, _, n => genericRow 1 limitValue hiddenZero n
  | .terminalMonotone, _, n => genericRow 3 hiddenZero hiddenZero n
  | .terminalNonmonotone, _, n => genericRow 1 hiddenZero hiddenZero n

def estimand (c : EstimandClass) :
    HypotheticalSequentialEstimand Omega Target Prefix where
  horizon := fun _ => 6
  Order := fun _ => Unit
  orderNonempty := fun _ => inferInstance
  revealedPrefix := fun _ _ _ => ()
  value := fun omega _ n => rowValue c omega n
  limit := fun _ => limitValue
  valuePrefixCompatible := by intros; rfl
  terminal := by intro omega xi; cases xi; cases c <;> rfl

def presentation (c : EstimandClass) : (estimand c).StructuralPresentation :=
  (estimand c).canonicalStructuralPresentation

def baseState (branch : Bool) : Omega where
  truth := false
  noise1 := 0
  noise2 := 0
  branch := branch

theorem singleton_mu_pos (omega : Omega) : 0 < mu ({omega} : Set Omega) := by
  rw [mu, NoisyObservationModel.latentLaw, uniformOn_univ]
  simp [NoisyObservationModel.card_latentState]

theorem measure_pos_of_mem {E : Set Omega} {omega : Omega} (homega : omega ∈ E) :
    0 < mu E := by
  exact (singleton_mu_pos omega).trans_le
    (measure_mono (Set.singleton_subset_iff.mpr homega))

/-- A constraint that fires from a fixed stage onwards. -/
def stageTailConstraint
    {Omega S Prefix : Type*}
    (K : HypotheticalSequentialEstimand Omega S Prefix) (start : ℕ) :
    K.StructuralConstraint where
  fires := fun _ _ n => start ≤ n
  nonanticipating := by simp

theorem singleton_stageTailConstraint_valid
    {Omega S Prefix : Type*}
    (K : HypotheticalSequentialEstimand Omega S Prefix) (start : ℕ)
    (hTail : ∀ omega (xi : K.Order omega) n,
      start ≤ n → n < K.horizon omega →
        K.value omega xi (n + 1) = K.limit omega) :
    K.ValidConstraintFamily ({stageTailConstraint K start} :
      Set K.StructuralConstraint) := by
  constructor
  · intro c hc omega xi n hn hFire _
    rw [Set.mem_singleton_iff] at hc
    subst c
    exact hTail omega xi n hFire hn
  · intro c hc omega xi n _ hFire _ hStops
    rw [Set.mem_singleton_iff] at hc
    subst c
    exfalso
    apply hStops
    exact Nat.le.step hFire

theorem persistence_of_stageTail
    {Omega S Prefix : Type*}
    (K : HypotheticalSequentialEstimand Omega S Prefix)
    (A : K.StructuralPresentation) (start : ℕ)
    (hTail : ∀ omega (xi : K.Order omega) n,
      start ≤ n → n < K.horizon omega →
        K.value omega xi (n + 1) = K.limit omega)
    {omega : Omega} {xi : K.Order omega} {n : ℕ}
    (hstart : start ≤ n) (hn : n ≤ K.horizon omega)
    (hEq : K.value omega xi n = K.limit omega) :
    PersistenceAt K A omega xi n := by
  exact validSubfamily_persistence K A
    (singleton_stageTailConstraint_valid K start hTail) hn hEq
    ⟨stageTailConstraint K start, Set.mem_singleton _, hstart⟩

/-- A tail constraint restricted to a state event. -/
def eventTailConstraint
    {Omega S Prefix : Type*}
    (K : HypotheticalSequentialEstimand Omega S Prefix)
    (P : Omega → Prop) (start : ℕ) : K.StructuralConstraint where
  fires := fun omega _ n => P omega ∧ start ≤ n
  nonanticipating := by simp

theorem singleton_eventTailConstraint_valid
    {Omega S Prefix : Type*}
    (K : HypotheticalSequentialEstimand Omega S Prefix)
    (P : Omega → Prop) (start : ℕ)
    (hTail : ∀ omega (xi : K.Order omega) n,
      P omega → start ≤ n → n < K.horizon omega →
        K.value omega xi (n + 1) = K.limit omega) :
    K.ValidConstraintFamily ({eventTailConstraint K P start} :
      Set K.StructuralConstraint) := by
  constructor
  · intro c hc omega xi n hn hFire _
    rw [Set.mem_singleton_iff] at hc
    subst c
    exact hTail omega xi n hFire.1 hFire.2 hn
  · intro c hc omega xi n _ hFire _ hStops
    rw [Set.mem_singleton_iff] at hc
    subst c
    exfalso
    apply hStops
    exact ⟨hFire.1, Nat.le.step hFire.2⟩

theorem persistence_of_eventTail
    {Omega S Prefix : Type*}
    (K : HypotheticalSequentialEstimand Omega S Prefix)
    (A : K.StructuralPresentation) (P : Omega → Prop) (start : ℕ)
    (hTail : ∀ omega (xi : K.Order omega) n,
      P omega → start ≤ n → n < K.horizon omega →
        K.value omega xi (n + 1) = K.limit omega)
    {omega : Omega} {xi : K.Order omega} {n : ℕ}
    (hP : P omega) (hstart : start ≤ n) (hn : n ≤ K.horizon omega)
    (hEq : K.value omega xi n = K.limit omega) :
    PersistenceAt K A omega xi n := by
  exact validSubfamily_persistence K A
    (singleton_eventTailConstraint_valid K P start hTail) hn hEq
    ⟨eventTailConstraint K P start, Set.mem_singleton _, ⟨hP, hstart⟩⟩

/-- If equality breaks at the next stage, no member of the canonical greatest
valid family can certify persistence now. -/
theorem not_persistence_of_next_ne
    {Omega S Prefix : Type*}
    (K : HypotheticalSequentialEstimand Omega S Prefix)
    (A : K.StructuralPresentation)
    {omega : Omega} {xi : K.Order omega} {n : ℕ}
    (hn : n < K.horizon omega)
    (hNext : K.value omega xi (n + 1) ≠ K.limit omega) :
    ¬PersistenceAt K A omega xi n := by
  rintro ⟨⟨_, hEq⟩, c, hc, hFire⟩
  exact hNext (A.greatest.1.1 c hc omega xi n hn hFire hEq)

theorem not_fixed_nonfixed (c : EstimandClass) (hc : c ≠ .fixed) :
    ¬(estimand c).IsFixed := by
  intro hFixed
  have h0 := hFixed (baseState false) () 0 (by norm_num)
  cases c <;>
    simp [estimand, rowValue, genericRow, point, limitValue] at hc h0

theorem fixed_isFixed : (estimand .fixed).IsFixed := by
  intro omega xi n hn
  rfl

theorem absorbingMonotone_isMonotone :
    (estimand .absorbingMonotone).IsMonotone := by
  intro omega xi n hn
  change dist limitValue (rowValue .absorbingMonotone omega (n + 1)) ≤
    dist limitValue (rowValue .absorbingMonotone omega n)
  change n < 6 at hn
  interval_cases n <;>
    norm_num [estimand, rowValue, genericRow, nonmonotoneStart, point, limitValue,
      hiddenZero, FlagSpace.dist_eq]

theorem mixedMonotone_isMonotone :
    (estimand .mixedMonotone).IsMonotone := by
  intro omega xi n hn
  change dist limitValue (rowValue .mixedMonotone omega (n + 1)) ≤
    dist limitValue (rowValue .mixedMonotone omega n)
  change n < 6 at hn
  cases hbranch : omega.branch <;> interval_cases n <;>
    norm_num [estimand, rowValue, genericRow, nonmonotoneStart, point, limitValue,
      hiddenZero, FlagSpace.dist_eq, hbranch]

theorem nonabsorbingMonotone_isMonotone :
    (estimand .nonabsorbingMonotone).IsMonotone := by
  intro omega xi n hn
  change dist limitValue (rowValue .nonabsorbingMonotone omega (n + 1)) ≤
    dist limitValue (rowValue .nonabsorbingMonotone omega n)
  change n < 6 at hn
  interval_cases n <;>
    norm_num [estimand, rowValue, genericRow, nonmonotoneStart, point, limitValue,
      hiddenZero, FlagSpace.dist_eq]

theorem terminalMonotone_isMonotone :
    (estimand .terminalMonotone).IsMonotone := by
  intro omega xi n hn
  change dist limitValue (rowValue .terminalMonotone omega (n + 1)) ≤
    dist limitValue (rowValue .terminalMonotone omega n)
  change n < 6 at hn
  interval_cases n <;>
    norm_num [estimand, rowValue, genericRow, nonmonotoneStart, point, limitValue,
      hiddenZero, FlagSpace.dist_eq]

theorem nonmonotone_not_isMonotone
    (c : EstimandClass)
    (hc : c = .absorbingNonmonotone ∨ c = .mixedNonmonotone ∨
      c = .nonabsorbingNonmonotone ∨ c = .terminalNonmonotone) :
    ¬(estimand c).IsMonotone := by
  intro hMonotone
  have h0 := hMonotone (baseState false) () 0 (by norm_num [estimand])
  change dist limitValue (rowValue c (baseState false) 1) ≤
    dist limitValue (rowValue c (baseState false) 0) at h0
  rcases hc with rfl | rfl | rfl | rfl <;>
    norm_num [estimand, rowValue, genericRow, nonmonotoneStart, point, limitValue,
      FlagSpace.dist_eq, abs_of_nonneg] at h0

theorem absorbing_tail
    (c : EstimandClass)
    (hc : c = .absorbingMonotone ∨ c = .absorbingNonmonotone) :
    ∀ omega (xi : (estimand c).Order omega) n,
      4 ≤ n → n < (estimand c).horizon omega →
        (estimand c).value omega xi (n + 1) = (estimand c).limit omega := by
  rintro omega xi n h4 hn
  change n < 6 at hn
  rcases hc with rfl | rfl <;> interval_cases n <;>
    simp [estimand, rowValue, genericRow, limitValue]

theorem absorbing_preterminal_eq_stage4
    (c : EstimandClass)
    (hc : c = .absorbingMonotone ∨ c = .absorbingNonmonotone)
    {omega : Omega} {xi : (estimand c).Order omega} {n : ℕ}
    (hn : n < (estimand c).horizon omega)
    (hEq : (estimand c).value omega xi n = (estimand c).limit omega) :
    4 ≤ n := by
  change n < 6 at hn
  rcases hc with rfl | rfl <;> interval_cases n <;>
    simp [estimand, rowValue, genericRow, point, limitValue] at hEq ⊢

theorem absorbing_coverage
    (c : EstimandClass)
    (hc : c = .absorbingMonotone ∨ c = .absorbingNonmonotone) :
    AbsorbingCoverage (estimand c) (presentation c) mu := by
  filter_upwards [] with omega
  intro xi n hn hEq
  rcases hn.lt_or_eq with hnlt | hterminal
  · exact persistence_of_stageTail (estimand c) (presentation c) 4
      (absorbing_tail c hc) (absorbing_preterminal_eq_stage4 c hc hnlt hEq)
      hn hEq
  · subst n
    exact terminal_persistence (estimand c) (presentation c) xi

theorem absorbing_persistence_mem
    (c : EstimandClass)
    (hc : c = .absorbingMonotone ∨ c = .absorbingNonmonotone)
    (omega : Omega) :
    omega ∈ PersistenceAchievableSet (estimand c) (presentation c) := by
  refine ⟨(), 4, by norm_num [estimand], ?_⟩
  apply persistence_of_stageTail (estimand c) (presentation c) 4
    (absorbing_tail c hc) (by norm_num) (by norm_num [estimand])
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
    simp [estimand, rowValue, genericRow, limitValue, hbranch]

theorem mixed_persistence_mem_false
    (c : EstimandClass)
    (hc : c = .mixedMonotone ∨ c = .mixedNonmonotone) :
    baseState false ∈ PersistenceAchievableSet (estimand c) (presentation c) := by
  refine ⟨(), 4, by norm_num [estimand], ?_⟩
  apply persistence_of_eventTail (estimand c) (presentation c)
    (fun omega => omega.branch = false) 4 (mixed_tail_false c hc)
    rfl (by norm_num) (by norm_num [estimand])
  rcases hc with rfl | rfl <;> rfl

theorem mixed_not_persistence_true_stage4
    (c : EstimandClass)
    (hc : c = .mixedMonotone ∨ c = .mixedNonmonotone) :
    ¬PersistenceAt (estimand c) (presentation c) (baseState true) () 4 := by
  apply not_persistence_of_next_ne (estimand c) (presentation c) (by norm_num [estimand])
  rcases hc with rfl | rfl <;>
    simp [estimand, rowValue, genericRow, baseState, hiddenZero, limitValue]

theorem mixed_accidental_mem_true
    (c : EstimandClass)
    (hc : c = .mixedMonotone ∨ c = .mixedNonmonotone) :
    baseState true ∈ AccidentalEqualitySet (estimand c) (presentation c) := by
  refine ⟨(), 4, by norm_num [estimand], ?_, mixed_not_persistence_true_stage4 c hc⟩
  rcases hc with rfl | rfl <;> rfl

theorem nonabsorbing_not_persistence_stage4
    (c : EstimandClass)
    (hc : c = .nonabsorbingMonotone ∨ c = .nonabsorbingNonmonotone)
    (omega : Omega) :
    ¬PersistenceAt (estimand c) (presentation c) omega () 4 := by
  apply not_persistence_of_next_ne (estimand c) (presentation c) (by norm_num [estimand])
  rcases hc with rfl | rfl <;>
    simp [estimand, rowValue, genericRow, hiddenZero, limitValue]

theorem nonabsorbing_preterminal_eq_iff_stage4
    (c : EstimandClass)
    (hc : c = .nonabsorbingMonotone ∨ c = .nonabsorbingNonmonotone)
    {omega : Omega} {xi : (estimand c).Order omega} {n : ℕ}
    (hn : n < (estimand c).horizon omega) :
    (estimand c).value omega xi n = (estimand c).limit omega ↔ n = 4 := by
  change n < 6 at hn
  rcases hc with rfl | rfl <;> interval_cases n <;>
    simp [estimand, rowValue, genericRow, point, hiddenZero, limitValue]

theorem nonabsorbing_persistenceSet_empty
    (c : EstimandClass)
    (hc : c = .nonabsorbingMonotone ∨ c = .nonabsorbingNonmonotone) :
    PersistenceAchievableSet (estimand c) (presentation c) = ∅ := by
  apply Set.Subset.antisymm
  · rintro omega ⟨xi, n, hn, hPersistence⟩
    have hEq := hPersistence.1.2
    have hn4 := (nonabsorbing_preterminal_eq_iff_stage4 c hc hn).mp hEq
    subst n
    cases xi
    exact (nonabsorbing_not_persistence_stage4 c hc omega hPersistence).elim
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
  · rintro omega ⟨xi, n, hn, hEq⟩
    change n < 6 at hn
    rcases hc with rfl | rfl <;> interval_cases n <;>
      simp [estimand, rowValue, genericRow, point, hiddenZero, limitValue] at hEq
  · exact Set.empty_subset _

theorem fixed_hasClass :
    HasClass (estimand .fixed) (presentation .fixed) mu .fixed :=
  fixed_isFixed

theorem absorbingMonotone_hasClass :
    HasClass (estimand .absorbingMonotone) (presentation .absorbingMonotone)
      mu .absorbingMonotone := by
  refine ⟨absorbingMonotone_isMonotone,
    not_fixed_nonfixed _ (by decide), ?_, absorbing_coverage _ (Or.inl rfl)⟩
  exact measure_pos_of_mem (absorbing_persistence_mem _ (Or.inl rfl) (baseState false))

theorem absorbingNonmonotone_hasClass :
    HasClass (estimand .absorbingNonmonotone) (presentation .absorbingNonmonotone)
      mu .absorbingNonmonotone := by
  refine ⟨nonmonotone_not_isMonotone _ (Or.inl rfl),
    not_fixed_nonfixed _ (by decide), ?_, absorbing_coverage _ (Or.inr rfl)⟩
  exact measure_pos_of_mem (absorbing_persistence_mem _ (Or.inr rfl) (baseState false))

theorem mixedMonotone_hasClass :
    HasClass (estimand .mixedMonotone) (presentation .mixedMonotone)
      mu .mixedMonotone := by
  exact ⟨mixedMonotone_isMonotone, not_fixed_nonfixed _ (by decide),
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
    HasClass (estimand .nonabsorbingMonotone) (presentation .nonabsorbingMonotone)
      mu .nonabsorbingMonotone := by
  refine ⟨nonabsorbingMonotone_isMonotone, not_fixed_nonfixed _ (by decide),
    measure_pos_of_mem (nonabsorbing_equality_mem _ (Or.inl rfl) (baseState false)), ?_⟩
  rw [PersistenceAchievable, nonabsorbing_persistenceSet_empty _ (Or.inl rfl)]
  simp

theorem nonabsorbingNonmonotone_hasClass :
    HasClass (estimand .nonabsorbingNonmonotone)
      (presentation .nonabsorbingNonmonotone) mu .nonabsorbingNonmonotone := by
  refine ⟨nonmonotone_not_isMonotone _ (Or.inr (Or.inr (Or.inl rfl))),
    not_fixed_nonfixed _ (by decide),
    measure_pos_of_mem (nonabsorbing_equality_mem _ (Or.inr rfl) (baseState false)), ?_⟩
  rw [PersistenceAchievable, nonabsorbing_persistenceSet_empty _ (Or.inr rfl)]
  simp

theorem terminalMonotone_hasClass :
    HasClass (estimand .terminalMonotone) (presentation .terminalMonotone)
      mu .terminalMonotone := by
  refine ⟨terminalMonotone_isMonotone, not_fixed_nonfixed _ (by decide), ?_⟩
  rw [EqualityAchievable, terminal_equalitySet_empty _ (Or.inl rfl)]
  simp

theorem terminalNonmonotone_hasClass :
    HasClass (estimand .terminalNonmonotone) (presentation .terminalNonmonotone)
      mu .terminalNonmonotone := by
  refine ⟨nonmonotone_not_isMonotone _ (Or.inr (Or.inr (Or.inr rfl))),
    not_fixed_nonfixed _ (by decide), ?_⟩
  rw [EqualityAchievable, terminal_equalitySet_empty _ (Or.inr rfl)]
  simp

/-- The table covers all nine rows using each model's canonical greatest
constraint family. -/
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

/-- All taxonomy events are measurable in the finite latent sigma algebra. -/
theorem classEventsMeasurable (c : EstimandClass) :
    ClassEventsMeasurable (estimand c) (presentation c) := by
  constructor <;> simp

end StructuralWitnesses

end

end SequentialLearning
