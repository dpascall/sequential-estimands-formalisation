import SequentialLearning.AbsorptionOracleResults
import SequentialLearning.Impossibility
import SequentialLearning.RotationFamilyProperties
import SequentialLearning.SameEstimandImpossibility

/-!
# Manuscript-alignment interfaces

This module supplies the small named interfaces needed by the final
label-to-declaration audit.  The same-estimand repair now identifies the
finite noisy experiment's posterior Frechet variance with that of each
class-specific flag-lifted rotation witness.
-/

namespace SequentialLearning

open HypotheticalSequentialEstimand
open HypotheticalSequentialEstimand.StructuralPresentation

noncomputable section

universe uOmega uS uPrefix uOrder

namespace HypotheticalSequentialEstimand

variable {Omega : Type uOmega} {S : Type uS} {Prefix : Type uPrefix}
  (K : HypotheticalSequentialEstimand Omega S Prefix)

/-- A Boolean flag process is nonanticipating when equal revealed prefixes
give equal current flags, and terminally compatible when its terminal flag is
the designated limit flag. -/
def AdmissibleFlagProcess
    (flag : (omega : Omega) -> K.Order omega -> Nat -> Bool)
    (limitFlag : Omega -> Bool) : Prop :=
  (forall omega (xi xi' : K.Order omega) n,
      n <= K.horizon omega ->
        K.revealedPrefix omega xi n = K.revealedPrefix omega xi' n ->
          flag omega xi n = flag omega xi' n) /\
    forall omega (xi : K.Order omega),
      flag omega xi (K.horizon omega) = limitFlag omega

end HypotheticalSequentialEstimand

namespace StructuralWitnesses

/-- The flag carried by the concrete nine-row witness table. -/
def witnessFlag (c : EstimandClass)
    (omega : Omega) (_ : (estimand c).Order omega) (n : Nat) : Bool :=
  (rowValue c omega n).flag

/-- The terminal flag of the concrete witness table. -/
def witnessLimitFlag (c : EstimandClass) (omega : Omega) : Bool :=
  ((estimand c).limit omega).flag

/-- Exact admissibility of every flag template in the witness table. -/
theorem admissibleFlagProcess (c : EstimandClass) :
    (estimand c).AdmissibleFlagProcess
      (witnessFlag c) (witnessLimitFlag c) := by
  constructor
  · intro omega xi xi' n hn hPrefix
    exact congrArg FlagSpace.flag
      ((estimand c).valuePrefixCompatible omega xi xi' n hn hPrefix)
  · intro omega xi
    exact congrArg FlagSpace.flag ((estimand c).terminal omega xi)

end StructuralWitnesses

namespace Phase5

open NoisyObservationModel

/-- The former Phase 5 endpoint, retained under an accurate coexistence name.
Every structural class
has an admissible measurable witness on the finite latent probability space,
and the noisy-sign experiment on that same space has both realised posterior-
variance directions while decreasing in expectation.  No identification of
that scalar noisy-sign variance with the witness's Fréchet variance is made. -/
theorem coexistence (c : EstimandClass) :
    HasClass (StructuralWitnesses.estimand c)
        (StructuralWitnesses.presentation c) StructuralWitnesses.mu c /\
      ClassEventsMeasurable (StructuralWitnesses.estimand c)
        (StructuralWitnesses.presentation c) /\
      (StructuralWitnesses.estimand c).AdmissibleFlagProcess
        (StructuralWitnesses.witnessFlag c)
        (StructuralWitnesses.witnessLimitFlag c) /\
      NoisyObservationModel.posteriorVarianceTwo false false <
        NoisyObservationModel.posteriorVarianceOne false /\
      NoisyObservationModel.posteriorVarianceOne false <
        NoisyObservationModel.posteriorVarianceTwo false true /\
      NoisyObservationModel.expectedVarianceTwo <
        NoisyObservationModel.expectedVarianceOne := by
  exact ⟨StructuralWitnesses.witnesses c,
    StructuralWitnesses.classEventsMeasurable c,
    StructuralWitnesses.admissibleFlagProcess c,
    Phase3.bothverdicts.1, Phase3.bothverdicts.2.1,
    Phase3.bothverdicts.2.2⟩

/-- Exact aligned `impossibility`: for every non-fixed class, the same
flag-valued estimand has constant Frechet variance under the uninformative
model and a strict conditional expected increase under the noisy model. -/
theorem impossibility :
    (∀ c : EstimandClass, c ≠ .fixed →
      HasClass (SameEstimandImpossibility.estimand c)
        (SameEstimandImpossibility.presentation c)
        SameEstimandImpossibility.mu c ∧
      ClassEventsMeasurable (SameEstimandImpossibility.estimand c)
        (SameEstimandImpossibility.presentation c) ∧
      (∀ n, posteriorFrechetVarianceReal
        generatedZero
        (SameEstimandImpossibility.stageLaw c n
          generatedZero) = fun _ => (1 : Real)) ∧
      (∀ n, (fun omega =>
        MeasureTheory.condExp generatedZero latentLaw
          (posteriorFrechetVarianceReal generatedZero
            (SameEstimandImpossibility.stageLaw c (n + 1)
              generatedZero)) omega -
          posteriorFrechetVarianceReal generatedZero
            (SameEstimandImpossibility.stageLaw c n
              generatedZero) omega) =ᵐ[latentLaw]
          fun _ => (0 : Real)) ∧
      ((fun omega =>
        MeasureTheory.condExp generatedOne latentLaw
          (posteriorFrechetVarianceReal generatedTwo
            (SameEstimandImpossibility.stageLaw c 2
              generatedTwo)) omega -
          posteriorFrechetVarianceReal generatedOne
            (SameEstimandImpossibility.stageLaw c 1
              generatedOne) omega) =ᵐ[latentLaw]
          fun _ => (41 / 340 : Real))) :=
  SameEstimandImpossibility.impossibility

end Phase5

end

end SequentialLearning
