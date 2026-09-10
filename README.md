# SequentialLearning

**Lean formalisation of sequential estimands and learning**  
David J. Pascall · MRC Biostatistics Unit, University of Cambridge

Mathematical tools for learning about targets that can change as observations
accumulate. The project formalises a geometric classification of sequential
estimands, information and target-movement identities, posterior displacement
bounds, and results about uncertainty concerning a limiting target.

**Early research release: `v0.1.0-alpha.1`.** This snapshot contains 57 library
modules and the associated working manuscript. The code and manuscript are
being revised together. The current Lean definitions and hypotheses determine
the formal coverage of this release; full correspondence with the intended
manuscript model remains work in progress. See [Current status](docs/STATUS.md).

## Mathematical contents

| Area | Starting points |
| --- | --- |
| Taxonomy and structural persistence | [StructuralEstimandClasses](SequentialLearning/StructuralEstimandClasses.lean), [StructuralWitnesses](SequentialLearning/StructuralWitnesses.lean) |
| Fréchet risk and the information–movement criterion | [FrechetRiskWellPosedness](SequentialLearning/FrechetRiskWellPosedness.lean), [ProbabilisticExactCriterion](SequentialLearning/ProbabilisticExactCriterion.lean) |
| Hilbert interpretation and remaining uncertainty | [HilbertLearningCriterion](SequentialLearning/HilbertLearningCriterion.lean), [ReducibleIrreducible](SequentialLearning/ReducibleIrreducible.lean) |
| Wasserstein displacement and stability | [ClosedDisplacementResults](SequentialLearning/ClosedDisplacementResults.lean), [FlagSpaceCouplingLift](SequentialLearning/FlagSpaceCouplingLift.lean) |
| Absorption oracle | [AbsorptionOracleResults](SequentialLearning/AbsorptionOracleResults.lean) |
| Finite same-estimand counterexample | [SameEstimandImpossibility](SequentialLearning/SameEstimandImpossibility.lean) |
| MSE bounds and dynamics | [MSEHierarchyDynamics](SequentialLearning/MSEHierarchyDynamics.lean) |

[AllResults.lean](AllResults.lean) imports the full library. The
[declaration index](checks/manuscript-label-index.tsv) maps the manuscript's 46
indexed items to Lean declarations. Its historical alignment labels must be
read with the [current correspondence notes](docs/STATUS.md).

## Build and check

The environment is pinned to Lean `leanprover/lean4:v4.34.0-rc2`, Mathlib commit
`f2916a54665af851fc9a4da901cfc242c47a8922`, and the transitive revisions in
[lake-manifest.json](lake-manifest.json).

On Linux, install Git, Bash, Perl, ripgrep, GNU coreutils, and
[Elan](https://github.com/leanprover/elan). From the repository root:

```bash
chmod +x scripts/*.sh
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
scripts/fetch_mathlib_cache.sh
scripts/check_all.sh
```

Elan selects the version in `lean-toolchain`. The cache script requests the
Mathlib imports needed by this project. `check_all.sh` builds the project, runs
the axiom and interface audits, checks the original baseline hashes, scans for
proof placeholders, and checks manuscript labels and declaration references.
The label checks do not establish semantic equivalence between TeX and Lean.

After dependencies have been fetched, `lake build` runs just the aggregate
build. The GitHub Actions workflow runs the complete check sequence on pushes
and pull requests using [lean-action](https://github.com/leanprover/lean-action).

## Verification record

The supplied [Phase 8 record](docs/history/PHASE8_VERIFICATION.md) reports a
successful 3,103-job aggregate build, 90 master-facing axiom checks, and a
separate clean-checkout build. These are recorded results for the source
snapshot, not a new build of this release package.

Packaging checked that all 66 Lean files, dependency pins, and the working
manuscript are byte-for-byte unchanged. Lean and Lake were unavailable in the
packaging environment; a fresh compiler run remains to be obtained from the
workflow or commands above. See [Source provenance](docs/SOURCE_PROVENANCE.md).

## Cite this release

Metadata is supplied in [CITATION.cff](CITATION.cff). Cite the version and append
the published release URL or exact commit:

> Pascall, D. J. (2026). *SequentialLearning: Lean formalisation of sequential
> estimands* (v0.1.0-alpha.1) [Computer software; early research release].

This supports a reference to an early formalisation under active development.
It should not be described as complete formal verification of every statement
in the working manuscript.

## Repository guide

| Path | Purpose |
| --- | --- |
| `SequentialLearning/` | 57 Lean library modules |
| `AllResults.lean`, `AxiomAudit.lean`, `*InterfaceAudit.lean` | Aggregate imports and audit entry points |
| `scripts/`, `checks/` | Reproduction commands, inventories, and source checksums |
| `manuscript/` | Original working TeX manuscript, retained for declaration checks |
| `docs/STATUS.md` | Current scope and planned corrections |
| `docs/PHASE*.md`, `docs/history/` | Historical development and verification records |
| `RELEASE_NOTES.md`, `docs/RELEASING.md` | Release description and publishing instructions |

The manuscript's `references.bib` was not included in the supplied source;
building a manuscript PDF is not part of the Lean build.

## Licensing

No project license was included in the supplied snapshot, and this packaging
does not assign one. Third-party dependencies retain their own licenses.
