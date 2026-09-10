# Phase 4 absorption-oracle record

## Outcome

Phase 4 joins the generic terminal-refinement and binary-oracle developments
to the concrete absorption event

`absorptionEvent E f = ⋃ k, E k ∩ {omega | f omega = k}`.

The exact manuscript-facing declarations are `SequentialLearning.threeway`,
`SequentialLearning.oraclestrict`, and `SequentialLearning.oraclehilbert`.
They expose regular-conditional-law data and the master second-moment
assumption, but no separate branch-risk, branch-`L²`, finite-branch, or
kernel-constructor hypotheses.

The 41 supplied baseline modules remain byte-for-byte unchanged.

## RCD boundary

`RegularConditionalLawData` packages a probability kernel with the assertion
that it is a regular conditional law. `AbsorptionOracleRCDs` packages the two
branch laws `muA` and `muAc` by asserting that:

- their `pInfinity` mixture is the conditional law given `FInf`; and
- selecting the branch by the absorption status is the conditional law given
  `FInf ∨ σ(absorptionEvent E f)`.

This leaves RCD existence as the sole kernel-level boundary of the three
master wrappers. The concrete oracle measurable space and absorption-event
measurability are constructed internally from the stated event hypotheses.

## Closing branch finiteness

The original generic Fréchet theorem requested finite risk for both branch
kernels at every probability value. The closed theorem instead uses one
finite-risk fact for the coarse mixture:

- when `0 < pInfinity < 1`, positive mixture weights force both branch risks
  to be finite;
- when `pInfinity = 0` or `pInfinity = 1`, the unused branch has zero weight
  and the oracle gap vanishes algebraically.

The required mixture finiteness follows almost surely from the coarse RCD and
the master square-moment assumption. In the Hilbert case, finite branch risk
at the origin supplies the branch `MemLp id 2` fact on the interior event, so
`oraclehilbert` also needs no separate branch-`L²` premise.

## Master-facing endpoints

- `threeway` gives the current variance as reducible gain, absorption-oracle
  enlargement gain, and residual risk, with all three terms nonnegative.
- `oraclestrict` gives the exact Fréchet gap representation, measurability,
  integrability, nonnegativity, the sequence-event characterisation, the
  positive-expectation criterion, and the separated-sublevel lower bound.
- `oraclehilbert` gives
  `pInfinity * (1 - pInfinity) * ‖mA - mAc‖ ^ 2`, together with the strict
  branch-mean event, its measurability, and the positive-expectation criterion.

`scripts/check_phase4_interfaces.sh` compiles and prints these three types,
requires the concrete absorption notation, and rejects the implementation
premises removed in this phase. The aggregate build, placeholder scan, source
integrity check, and axiom audit cover the Phase 4 declarations.
