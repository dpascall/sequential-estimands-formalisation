# Phase 3 impossibility record

## Outcome

Phase 3 formalises a finite coexistence block. Four additive modules define
an equality-visible flag pseudometric, an explicit finite noisy-channel
experiment, witnesses for all nine structural classes, and a
class-independent observation theorem. The 41 supplied baseline modules
remain byte-for-byte unchanged.

Phase 5 subsequently identified an important scope distinction: the scalar
posterior variances of the noisy-sign experiment are not the Frechet
variances of the nine structural witness estimands. Accordingly this record
must not be read as a proof of the earlier manuscript's stronger
same-estimand impossibility claim. That Phase 3 limitation is superseded by
`SequentialLearning/SameEstimandImpossibility.lean`, which constructs a single
flag-lifted rotation estimand for each non-fixed class and computes its actual
Fréchet variance under both observation filtrations. See
`docs/PHASE5_FINAL_AUDIT.md`.

## Flag target

`FlagSpace S` stores a value in `S` and a Boolean flag. Its pseudometric is
induced only by the value coordinate, while its measurable structure contains
both coordinates. Thus opposite flags are literally unequal and measurably
distinguishable while remaining at distance zero.

Frechet risk and variance project exactly to the value coordinate. Phase 8 now
also proves that Wasserstein distance is exactly preserved: arbitrary
projected couplings are decorated using the two conditional Boolean flag
kernels, with unchanged cost. The earlier explicit `CouplingsLift` condition
has therefore been discharged. This strengthening is independent of the
witness table, the two-verdict theorem, and the final impossibility theorem.

## Finite observation model

The latent space has 256 equiprobable states:

- one hidden Boolean sign;
- a four-valued first-channel error selector;
- a sixteen-valued second-channel error selector; and
- one spare branch bit used only by the structural flag process.

The first channel has crossover probability `q = 1/4`, and the second has
`q' = 7/16`. The generated filtration reveals no signs, then the first sign,
then both signs. Kernel-checked rational calculations establish:

| Quantity | Value |
|---|---:|
| Prior variance | `1` |
| Posterior variance after one sign | `3/4` |
| Posterior variance after agreeing signs | `189/289` |
| Posterior variance after disagreeing signs | `21/25` |
| Expected variance after two signs | `63/85` |

Agreement lowers posterior variance while disagreement raises it; ex ante,
the second signal still lowers expected posterior variance.

## Structural witnesses

`StructuralWitnesses.witnesses` covers all nine `EstimandClass` constructors on
the same finite probability space. The eight non-fixed rows use an explicit
six-stage table. Absorbing rows certify persistence through valid tail
constraints; mixed rows use the positive-probability branch bit; nonabsorbing
and terminal rows prove the required event separation. Every proof uses the
canonical greatest constraint family supplied by the taxonomy development.

## Master-facing endpoints

- `StructuralWitnesses.witnesses`: a `HasClass` proof for every class.
- `StructuralWitnesses.classEventsMeasurable`: measurability of all taxonomy
  events in the finite latent sigma algebra.
- `Phase3.bothverdicts`: both realised variance directions plus the expected
  decrease.
- `Phase3.impossibility`: every class is realised with measurable events on
  the same finite ambient space as a noisy-sign experiment exhibiting both
  realised verdicts. It does not identify the two target variables.

`scripts/check_phase3_interfaces.sh` rejects leaked `CouplingsLift`,
`ValidConstraintFamily`, or `StructuralConstraint` premises from these closed
endpoints. The aggregate build, placeholder scan, and axiom audit include all
Phase 3 declarations.
