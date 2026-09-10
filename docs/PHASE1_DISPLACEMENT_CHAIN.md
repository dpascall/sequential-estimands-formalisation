# Phase 1 displacement-chain record

## Outcome

Phase 1 closes `displacement`, `dispbound`, `dispenvelope`, and `breakeven` under the manuscript's
own hypotheses. The original 41 supplied files remain byte-for-byte unchanged; the closed
interfaces are additive wrappers, so the Phase 0 evidence remains verifiable.

## New formal results

| Layer | Canonical declaration | Role |
|---|---|---|
| Probability laws | `MeasureTheory.secondCountableTopology_probabilityMeasure` | Weak probability-law topology is second-countable on a Polish space. |
| Probability laws | `MeasureTheory.opensMeasurableSpace_probabilityMeasure` | Weak Borel sigma-algebra is contained in the Giry measurable structure. |
| Wasserstein | `SequentialLearning.wasserstein2_lowerSemicontinuous` | The project-defined quadratic Wasserstein distance is weakly lower semicontinuous. |
| Wasserstein | `SequentialLearning.wasserstein2LawMeasurable_of_polish` | The project-defined `W₂` is Giry measurable on Polish laws. |
| Completion | `SequentialLearning.wasserstein2LawMeasurable_pseudometricCompletion` | Discharges the temporary proposition-valued interface on the canonical completion. |
| `displacement` | `SequentialLearning.measurable_posteriorDisplacementENN_closed` | Posterior displacement is measurable without `hW`. |
| `displacement` | `SequentialLearning.posteriorDisplacement_memLp_two_closed` | Posterior displacement is in `L²` without `hW`. |
| `displacement` | `SequentialLearning.integral_posteriorDisplacement_sq_le_closed` | Unconditional squared-displacement bound without `hW`. |
| `dispbound` | `SequentialLearning.frechet_posterior_displacement_bound_closed` | Full Fréchet/RCD bound without `hW`. |
| `dispenvelope` | `SequentialLearning.frechet_predictable_displacement_envelope_closed` | Predictable envelope without `hW`. |
| `breakeven` | `SequentialLearning.frechet_break_even_criterion_closed` | Break-even criterion without `hW`. |

The probability-law separability argument approximates arbitrary laws by finite atomic laws in the
Lévy--Prokhorov metric. Lower semicontinuity of `W₂` is obtained by tightness of near-optimal
couplings, Prokhorov subsequence extraction, convergence of marginals, and Portmanteau for the
nonnegative squared-distance cost.

## Compatibility note

The Phase 0 declarations that accept `hW` are intentionally retained unchanged. The declarations
with the `_closed` suffix are the canonical Phase 1 manuscript-facing interfaces and have identical
conclusions with that premise removed. `scripts/check_displacement_interfaces.sh` checks this
boundary mechanically.

## Reproducibility

Lean and Mathlib remain pinned exactly as in Phase 0. A clean checkout is verified with:

```bash
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
scripts/fetch_mathlib_cache.sh
scripts/check_all.sh
```

The known-good Phase 1 revision is identified by the Git tag `phase1-known-good`.
