# v0.1.0-alpha.1 — Early research release

An initial source release of **SequentialLearning**, a Lean 4 formalisation of
sequential estimands and learning.

The snapshot contains 57 library modules covering the sequential-estimand
taxonomy, Fréchet information–movement criterion, Hilbert uncertainty
decompositions, Wasserstein displacement bounds, absorption-oracle results,
MSE bounds, and finite same-estimand counterexamples. It includes the working
manuscript, declaration index, pinned dependencies, and reproduction scripts.

This release preserves the supplied Phase 8 Lean source without mathematical
changes. The associated record reports a successful full build and axiom
audit. Packaging checked source identity and metadata; a fresh compiler run
was not available in the packaging environment.

**Development status:** the observed-process interface and the general
Fréchet–Hilbert identification require further formalisation, and several
manuscript statements and proofs require correction. Full correspondence
between manuscript and code is not claimed. See `docs/STATUS.md` in the source
tree for the current scope and planned revisions.

**Reproduction:** Lean `v4.34.0-rc2`, Mathlib
`f2916a54665af851fc9a4da901cfc242c47a8922`; follow the README build instructions.

**Citation:** Pascall, D. J. (2026). *SequentialLearning: Lean formalisation of
sequential estimands* (v0.1.0-alpha.1) [Computer software; early research release].
Use this release's URL when citing it. Metadata is in `CITATION.cff`.
