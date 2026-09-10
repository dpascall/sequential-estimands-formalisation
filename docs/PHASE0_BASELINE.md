# Phase 0 baseline record

## Scope

The baseline contains all 41 supplied Lean source files under
`SequentialLearning/`. They were copied without edits. Their SHA-256 hashes
are recorded in `checks/source-manifest.sha256` and checked before every
verification build.

The master-facing audit contains 51 existing declarations. The registry is
`checks/master-facing-theorems.tsv`; `AxiomAudit.lean` issues one
`#print axioms` command for each entry.

## Reproducibility pins

| Component | Pin |
|---|---|
| Lean | `leanprover/lean4:v4.34.0-rc2` |
| Lean commit | `6a10ac8c22beadecabdbb0919c2b50214762f91d` |
| Mathlib | `f2916a54665af851fc9a4da901cfc242c47a8922` |
| Other Lake packages | `lake-manifest.json` |

## Verification record

| Check | Result |
|---|---|
| ZIP entries copied | 41/41 |
| SHA-256 integrity | Pass, 41/41 |
| Proof-placeholder scan | Pass |
| `lake build AllResults` | Pass, 3,062 jobs |
| Full default `lake build` | Pass, 3,064 jobs |
| Master-facing declarations elaborated | Pass, 51/51 |
| `sorryAx` in axiom output | None |

The master-facing declarations use only the standard Lean/Mathlib axioms
`propext`, `Classical.choice`, and `Quot.sound`; the canonical greatest-family
theorem is axiom-free. The build emits existing linter warnings (unused section
variables and style suggestions), which are retained because Phase 0 does not
edit the supplied source files.

The first known-good revision is identified by the Git tag
`phase0-known-good`. The exact commit object is also reported with the delivered
Git bundle. A clone of that tagged revision was used for the clean-checkout
verification.
