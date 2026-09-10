# Current scope and planned revisions

Status of the source snapshot prepared on 10 September 2026 for
`v0.1.0-alpha.1`. This document takes precedence over historical claims of exact
manuscript alignment in the phase notes and declaration index.

## Formal coverage

The release preserves the current Lean definitions and proofs, their pinned
build environment, and the working manuscript. The supplied Phase 8 record
reports successful compilation and axiom checks. Formal coverage is determined
by the actual definitions and hypotheses of each Lean theorem.

This is an abstract mathematical development. It does not yet include a
formalised Markov genealogy model or a complete construction connecting every
filtration and estimand to the manuscript's initial sampling model.

## Observed-process interface

`RealizedObservedProcess` in `SequentialLearning/ObservedProcess.lean` currently
requires the target to be strongly measurable with respect to the analyst's
filtration and caps stages at the full hypothetical horizon `z`. These are
more restrictive requirements than the intended manuscript model.

The replacement will represent actual observed prefixes, use `f <= z`, and cap
realised stages at `min(n, f)`. It will preserve target measurability with
respect to `sigma(Theta, D_n)` into the specified target sigma-algebra. The
target may remain uncertain given the analyst's information `sigma(D_n)`.

Hypothetical orders will establish geometry through explicit agreement on
observed prefixes. Unobserved suffixes will not extend the realised data or
target process. A stopping-time assumption on `f` is not needed for these
pathwise comparisons. Moments will be attached to the results that need them;
bounded tail results do not need the current bundle's target `L2` assumptions.

The generic probability results already admit broader processes. The principal
repair is the class-to-observed-process connection in `TaxonomyProcessResults`.

## Fréchet–Hilbert connection

The library contains Fréchet variance defined through posterior-law kernels
and Hilbert variance defined through conditional squared residuals. It also
contains a law-level identification and concrete finite-model connections.
The general conditional identification, and its consequences for information,
movement, and refinement quantities, still need to be added. They are
mathematically available under the manuscript's existing separable-Hilbert and
second-moment assumptions.

## Manuscript corrections

The manuscript is unchanged, despite the historical word `aligned` in its
filename. Planned corrections include:

- Carrying the rotation lemma's independence condition from part (ii) into
  part (iii).
- Replacing the incorrect assertion of unweighted branch-variance integrability
  by the weighted argument. The closed Lean oracle results already avoid extra
  branch moment assumptions.
- Directly proving measurability of the sequence-defined strict-oracle event,
  and distinguishing exact statements from almost-sure identities.
- Correcting the fixed-target universal-equality wording to a supermartingale
  inequality, the class-nesting display, and the pseudometric nondegeneracy
  example.
- Clarifying inherited moment and RCD hypotheses, observed versus hypothetical
  persistence notation, constant extension after the observed count, and the
  terminal observation sigma-algebra.
- Qualifying the discussion of nonmonotonic classes and repairing minor TeX
  and notation errors.

The missing `references.bib` must also be restored for a complete manuscript
build. It is not needed to build the Lean project.

## Interpretation of the checks

Compiler and axiom checks concern the Lean statements with their actual
hypotheses. The manuscript-index script checks labels, references, and
declaration resolution; it does not prove semantic equivalence between TeX
statements and Lean types.

The `Exact` labels in `checks/manuscript-label-index.tsv` are preserved as
historical metadata and are subject to these qualifications. The phase notes
are development records, not an independent certification of correspondence.

An appropriate description is: an early Lean formalisation of sequential-
estimand theory, with a reproducible source snapshot, a supplied successful-
build record, and ongoing work on correspondence with the working manuscript.
