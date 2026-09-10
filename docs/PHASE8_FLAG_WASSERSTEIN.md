# Phase 8 reverse flag-space Wasserstein equality

## Outcome

The former `FlagSpace.CouplingsLift` hypothesis has been proved for every pair
of Boolean-flagged probability laws.  The exact master-facing theorem

```text
SequentialLearning.FlagSpace.wasserstein2_eq_project
```

now states

```text
wasserstein2 mu nu = wasserstein2 (projectLaw mu) (projectLaw nu)
```

without a coupling-lift or disintegration premise.

## Construction

`FlagSpace S` is measurably equivalent to `S × Bool`.  For a flagged law `mu`,
Mathlib's standard-Borel disintegration gives a Markov kernel for the
conditional Boolean flag law given the `S` coordinate.  This use of
disintegration needs only the conditioned coordinate `Bool` to be standard
Borel; it does not add a standard-Borel or countable-generation hypothesis on
`S`.

For a coupling `pi` of the projected laws:

1. take the two conditional flag kernels belonging to `mu` and `nu`;
2. conditionally independently attach those flags to the two coordinates of
   `pi`;
3. map the resulting value/flag pairs back into `FlagSpace S`.

Lean proves that the decorated law has marginals exactly `mu` and `nu`, and
that projecting both values recovers `pi` exactly.  The flag pseudometric
ignores the attached flags, so `transportL2Cost_liftCoupling` proves equality
of transport costs.  This establishes `couplingsLift`, the reverse
Wasserstein inequality, and exact equality.

## Why the direct Radon--Nikodym sketch was not used

The finite Radon--Nikodym construction is valid, but its Lean implementation
would require four weighted submeasures, almost-everywhere identities for the
two flag densities, and separate marginal calculations.  The conditional
kernel construction packages the same measure-theoretic content and makes
the marginal identities consequences of disintegration and kernel
composition.

## Consequences

The aligned flag-space lemma is now exact and unconditional.  Flag lifting
preserves posterior displacement as well as Frechet risk, variance,
information, and movement.  The original conditional theorem
`wasserstein2_eq_project_of_couplingsLift` remains available as a compatibility
lemma, but it is no longer the master-facing endpoint.
