# Phase 8 reverse flag-space Wasserstein equality

- Commit: `0a25e7a431a4238b608916e51107e70b8fd36502`
- Tag: `phase8-known-good`
- Lean: `v4.34.0-rc2`
- Mathlib: `f2916a54665af851fc9a4da901cfc242c47a8922`
- Aggregate build: 3,103 jobs, passed
- Current project modules: 57, passed
- Original 41-module source-integrity audit: passed
- Proof-placeholder scan: passed
- Master-facing axiom checks: 90, passed
- Transitive axioms: `propext`, `Classical.choice`, `Quot.sound` only
- `sorryAx`, `native_decide`, and compiler-trust calculation: absent
- Phase 1--4, Phase 6, and Phase 7 interface audits: passed
- Flag-space interface audit: passed
- Manuscript label-to-declaration audit: all 46 labels resolve, passed
- Separate clean checkout with a fresh project build directory: passed

## Closed result

For every pair of probability laws `mu` and `nu` on `FlagSpace S`, Lean now
proves

```text
wasserstein2 mu nu = wasserstein2 (projectLaw mu) (projectLaw nu)
```

without an exposed `FlagSpace.CouplingsLift` hypothesis.

The proof identifies `FlagSpace S` measurably with `S × Bool`, disintegrates
each flagged law to obtain the conditional Boolean flag law given its value,
and conditionally independently decorates any coupling of the projected laws.
The resulting joint law has exactly the original flagged marginals and
projects exactly to the supplied coupling. Because the pseudometric ignores
both flags, transport cost is preserved exactly.

The construction does not add a standard-Borel or countable-generation
hypothesis on `S`: only the conditioned coordinate `Bool` uses standard-Borel
disintegration.

The aligned manuscript and declaration index now state unconditional equality,
so flag lifting preserves posterior displacement as well as Frechet risk,
variance, information, and movement. The former conditional theorem remains
available only for compatibility.

## Archive hashes

- `SequentialLearning_Phase8_Source.zip`:
  `4c4011bf40bd5a4c5e5c9dc4e516dc4c1b40122ce51e0657fa90562328358552`
- `SequentialLearning_Phase8.bundle`:
  `1da843ce9e8ba52e165854c20b7003e19ddbe1c143b3f3ca39298c11159dada6`
