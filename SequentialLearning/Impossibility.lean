import SequentialLearning.StructuralWitnesses

/-!
# Taxonomy-independent observation verdicts

The same 256-state noisy observation model supports every structural class.
Its spare branch bit controls only the equality-visible, zero-distance flag;
the two observed noisy signs and their posterior variances are unchanged.
Thus the structural taxonomy cannot determine the realised direction of the
second observation's posterior-variance change.
-/

namespace SequentialLearning

open MeasureTheory
open HypotheticalSequentialEstimand
open HypotheticalSequentialEstimand.StructuralPresentation

noncomputable section

namespace Phase3

/-- The finite flag process is measurable at every stage, as is its terminal
value.  This is the admissibility condition needed by the concrete observation
model. -/
theorem admissible_flag_process (c : EstimandClass) :
    (∀ n : ℕ, Measurable fun omega : StructuralWitnesses.Omega =>
      (StructuralWitnesses.rowValue c omega n).flag) ∧
    Measurable fun omega : StructuralWitnesses.Omega =>
      (StructuralWitnesses.estimand c).limit omega := by
  constructor
  · intro n
    exact measurable_from_top
  · exact measurable_from_top

/-- Master-facing `bothverdicts`: agreement and disagreement give opposite
realised variance changes, while the ex-ante variance still decreases. -/
theorem bothverdicts :
    NoisyObservationModel.posteriorVarianceTwo false false <
        NoisyObservationModel.posteriorVarianceOne false ∧
      NoisyObservationModel.posteriorVarianceOne false <
        NoisyObservationModel.posteriorVarianceTwo false true ∧
      NoisyObservationModel.expectedVarianceTwo <
        NoisyObservationModel.expectedVarianceOne :=
  NoisyObservationModel.both_verdicts

/-- Master-facing `impossibility`: every one of the nine structural classes is
realised on the same finite observation space and probability law, with
measurable taxonomy events and an admissible flag process, yet that common
model exhibits both realised observation verdicts. -/
theorem impossibility (c : EstimandClass) :
    HasClass (StructuralWitnesses.estimand c)
        (StructuralWitnesses.presentation c) StructuralWitnesses.mu c ∧
      ClassEventsMeasurable (StructuralWitnesses.estimand c)
        (StructuralWitnesses.presentation c) ∧
      (∀ n : ℕ, Measurable fun omega : StructuralWitnesses.Omega =>
        (StructuralWitnesses.rowValue c omega n).flag) ∧
      NoisyObservationModel.posteriorVarianceTwo false false <
        NoisyObservationModel.posteriorVarianceOne false ∧
      NoisyObservationModel.posteriorVarianceOne false <
        NoisyObservationModel.posteriorVarianceTwo false true := by
  refine ⟨StructuralWitnesses.witnesses c,
    StructuralWitnesses.classEventsMeasurable c,
    (admissible_flag_process c).1, ?_⟩
  exact ⟨bothverdicts.1, bothverdicts.2.1⟩

end Phase3

end

end SequentialLearning
