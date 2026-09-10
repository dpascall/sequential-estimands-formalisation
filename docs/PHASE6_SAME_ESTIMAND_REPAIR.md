# Same-estimand impossibility repair

## Outcome

The substantive gap identified after Phase 4 is resolved. For every non-fixed
structural class, the project now constructs one flag-lifted rotation estimand,
proves that estimand's exact `HasClass` judgment, constructs its canonical RCD
under each observation sigma-algebra, and computes its actual Frechet variance
under both models.

This is not a conjunction of `StructuralWitnesses.witnesses` with an unrelated
scalar variance result. The new class proofs and the variance calculation share
the definitions `SameEstimandImpossibility.estimand`, `stageValue`, and
`stageLaw`.

## Assessment of the proposed repair

| Point | Assessment before repair | Implemented resolution |
|---|---|---|
| Rotation arithmetic | Valid | Kernel-checked calculations prove `V_1 = 3/4`, the expected old-target stage-two variance `63/85`, and the expected new-target stage-two variance `74/85`. |
| R1: abstract arithmetic | Sound and small | Instantiated through the existing rotation identities and actual posterior kernels. |
| R2: fifth independent bit | Sufficient but not necessary | The existing spare branch bit is used as the orthogonal Rademacher coordinate. Its conditional expectation is proved zero under the zero-, one-, and two-sign sigma-algebras, so independence is established at the exact place it is needed. The latent space remains 256 states. |
| R3: instantiate rotations | Plausible | Completed with angles `pi/2` at stage one and `pi/4` at stage two. |
| R4: combine with old witnesses | Invalid as originally proposed | Not done. Eight non-fixed rotation-valued structural rows are constructed and their class membership is reproved from the canonical greatest constraint family. |
| Same-estimand requirement | Previously missing | `bothverdicts` uses the same `stageValue c n` under both canonical RCDs; only the observation measurable space changes. |
| Actual Frechet variance | Previously missing | `stageFrechetVariance_eq_hilbert` projects each flag-valued posterior law and proves equality with the Hilbert variance. |

## Exact verdicts

For every non-fixed class `c`:

- Model A uses the no-sign sigma-algebra at every stage and has Frechet
  variance `1` at every stage, hence zero conditional expected change and
  zero information term.
- Model B uses the one-sign sigma-algebra at stage one and the two-sign
  sigma-algebra at stage two. The same estimand has conditional expected
  Frechet-variance increase `41/340`.
- Its actual Frechet information term is `3/340` and its estimand-movement term
  is `44/340`, so `0 < 3/340 < 44/340`.

The master declarations are:

- `SequentialLearning.SameEstimandImpossibility.bothverdicts`
- `SequentialLearning.SameEstimandImpossibility.impossibility`
- `SequentialLearning.Phase5.impossibility`

## RCD representation

`canonicalConditionalLaw` maps Mathlib's finite-state conditional-expectation
kernel by the actual stage function. `canonicalConditionalLaw_isRCD` proves
that this mapped kernel is a regular conditional law. `stageLaw_isRCD`
specialises it to the flag-valued class witness. No RCD existence axiom or
implementation-level finiteness premise appears in the master theorem.

## Verification

The aggregate build, source-integrity check, placeholder scan, complete
master-facing axiom audit, Phase 1--4 interface audits, same-estimand interface
audit, and manuscript label-to-declaration audit all pass. The new declarations
depend only on the standard Lean/Mathlib axioms `propext`, `Classical.choice`,
and `Quot.sound`; there is no `sorryAx`, `native_decide`, or compiler-trust
calculation.
