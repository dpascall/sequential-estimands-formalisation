import SequentialLearning.IncreasingLoss

/-!
# Three-way refinement of posterior risk

This file formalises Proposition `threeway`.  The geometric master lemma has
already supplied integrable non-negative posterior-risk functions and
non-negative refinement gains.  What remains here is the conditional-
expectation algebra that composes two successive refinements.
-/

namespace SequentialLearning

open Filter MeasureTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

noncomputable section

section ThreeWayRefinement

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- The risk reduction obtained by refining from `mCoarse` to an information
state whose posterior risk is represented by `VFine`. -/
def refinementGain (μ : Measure[m0] Ω) (mCoarse : MeasurableSpace Ω)
    (VCoarse VFine : Ω → ℝ) : Ω → ℝ :=
  fun ω => VCoarse ω - μ[VFine | mCoarse] ω

/-- A refinement gain is integrable whenever its two risk functions are
integrable. -/
theorem refinementGain_integrable
    (μ : Measure[m0] Ω) (mCoarse : MeasurableSpace Ω)
    (VCoarse VFine : Ω → ℝ)
    (hVCoarse : Integrable VCoarse μ) (_hVFine : Integrable VFine μ) :
    Integrable (refinementGain μ mCoarse VCoarse VFine) μ := by
  exact hVCoarse.sub integrable_condExp

/-- Refinement gains satisfy a conditional cocycle law along nested
information states. -/
theorem refinementGain_cocycle
    (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (mCoarse mMiddle mFine : MeasurableSpace Ω)
    (hCoarseMiddle : mCoarse ≤ mMiddle)
    (hMiddleFine : mMiddle ≤ mFine) (hFineAmbient : mFine ≤ m0)
    (VCoarse VMiddle VFine : Ω → ℝ)
    (hVMiddle : Integrable VMiddle μ) (_hVFine : Integrable VFine μ) :
    refinementGain μ mCoarse VCoarse VFine =ᵐ[μ]
      fun ω =>
        refinementGain μ mCoarse VCoarse VMiddle ω +
          μ[refinementGain μ mMiddle VMiddle VFine | mCoarse] ω := by
  have hSub :
      μ[VMiddle - μ[VFine | mMiddle] | mCoarse] =ᵐ[μ]
        μ[VMiddle | mCoarse] - μ[μ[VFine | mMiddle] | mCoarse] :=
    condExp_sub hVMiddle integrable_condExp mCoarse
  have hTower :
      μ[μ[VFine | mMiddle] | mCoarse] =ᵐ[μ]
        μ[VFine | mCoarse] :=
    condExp_condExp_of_le hCoarseMiddle (hMiddleFine.trans hFineAmbient)
  filter_upwards [hSub, hTower] with ω hSubω hTowerω
  change VCoarse ω - μ[VFine | mCoarse] ω =
    (VCoarse ω - μ[VMiddle | mCoarse] ω) +
      μ[VMiddle - μ[VFine | mMiddle] | mCoarse] ω
  rw [hSubω]
  simp only [Pi.sub_apply]
  rw [hTowerω]
  ring

/-- The three-way decomposition into the coarse-to-middle gain, the middle-to-
fine gain viewed from the coarse information state, and the residual fine risk
viewed from the coarse information state. -/
theorem three_way_refinement_identity
    (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (mCoarse mMiddle mFine : MeasurableSpace Ω)
    (hCoarseMiddle : mCoarse ≤ mMiddle)
    (hMiddleFine : mMiddle ≤ mFine) (hFineAmbient : mFine ≤ m0)
    (VCoarse VMiddle VFine : Ω → ℝ)
    (hVMiddle : Integrable VMiddle μ) (hVFine : Integrable VFine μ) :
    VCoarse =ᵐ[μ] fun ω =>
      refinementGain μ mCoarse VCoarse VMiddle ω +
        μ[refinementGain μ mMiddle VMiddle VFine | mCoarse] ω +
          μ[VFine | mCoarse] ω := by
  have hCocycle := refinementGain_cocycle
    μ mCoarse mMiddle mFine hCoarseMiddle hMiddleFine hFineAmbient
      VCoarse VMiddle VFine hVMiddle hVFine
  filter_upwards [hCocycle] with ω hCocycleω
  calc
    VCoarse ω = refinementGain μ mCoarse VCoarse VFine ω +
        μ[VFine | mCoarse] ω := by
      simp only [refinementGain]
      ring
    _ = (refinementGain μ mCoarse VCoarse VMiddle ω +
          μ[refinementGain μ mMiddle VMiddle VFine | mCoarse] ω) +
        μ[VFine | mCoarse] ω := by rw [hCocycleω]
    _ = refinementGain μ mCoarse VCoarse VMiddle ω +
          μ[refinementGain μ mMiddle VMiddle VFine | mCoarse] ω +
        μ[VFine | mCoarse] ω := rfl

/-- The complete proposition: the three-way identity and non-negativity of
each of its three summands.  Non-negativity of the two primitive gains and of
the finest posterior risk is supplied by the geometric master lemma. -/
theorem three_way_refinement
    (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
    (mCoarse mMiddle mFine : MeasurableSpace Ω)
    (hCoarseMiddle : mCoarse ≤ mMiddle)
    (hMiddleFine : mMiddle ≤ mFine) (hFineAmbient : mFine ≤ m0)
    (VCoarse VMiddle VFine : Ω → ℝ)
    (hVMiddle : Integrable VMiddle μ) (hVFine : Integrable VFine μ)
    (hGainCoarseMiddle :
      0 ≤ᵐ[μ] refinementGain μ mCoarse VCoarse VMiddle)
    (hGainMiddleFine :
      0 ≤ᵐ[μ] refinementGain μ mMiddle VMiddle VFine)
    (hVFineNonnegative : 0 ≤ᵐ[μ] VFine) :
    (VCoarse =ᵐ[μ] fun ω =>
      refinementGain μ mCoarse VCoarse VMiddle ω +
        μ[refinementGain μ mMiddle VMiddle VFine | mCoarse] ω +
          μ[VFine | mCoarse] ω) ∧
    0 ≤ᵐ[μ] refinementGain μ mCoarse VCoarse VMiddle ∧
    0 ≤ᵐ[μ] μ[refinementGain μ mMiddle VMiddle VFine | mCoarse] ∧
    0 ≤ᵐ[μ] μ[VFine | mCoarse] := by
  refine ⟨three_way_refinement_identity μ mCoarse mMiddle mFine
    hCoarseMiddle hMiddleFine hFineAmbient VCoarse VMiddle VFine
      hVMiddle hVFine, hGainCoarseMiddle, ?_, ?_⟩
  · exact condExp_nonneg hGainMiddleFine
  · exact condExp_nonneg hVFineNonnegative

end ThreeWayRefinement

end

end SequentialLearning
