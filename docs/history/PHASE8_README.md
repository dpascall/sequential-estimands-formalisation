# Sequential Learning formalisation

This project preserves the Phase 0 reproducible baseline for the 41 Lean modules supplied in
`AllCurrentLean(1).zip`, adds the three Phase 1 modules that close the manuscript's displacement
chain, and adds two Phase 2 modules that connect taxonomy membership to realised tail and MSE
processes. Four Phase 3 modules provide the flag-space construction, explicit finite observation
models, all nine structural witnesses, and the finite coexistence result. Three Phase 4 modules
specialise the generic refinement machinery to the concrete absorption oracle and close its
Fréchet and Hilbert interfaces without separate branch-moment assumptions.
Phase 5 adds the exact manuscript-alignment interfaces, a corrected manuscript,
and an exhaustive label-to-declaration audit. Phase 6 repairs the impossibility
endpoint with one flag-lifted rotation estimand per class. Phase 7 removes the
surplus global measurability assumption from the increasing-loss boundary.
Phase 8 proves the reverse flag-space Wasserstein inequality by a constructive
Boolean conditional-kernel lift, making the equality unconditional.

## Pinned environment

- Lean: `leanprover/lean4:v4.34.0-rc2`
- Mathlib: `f2916a54665af851fc9a4da901cfc242c47a8922`
- Transitive dependencies: locked in `lake-manifest.json`

`lean-toolchain` selects Lean through Elan. `lakefile.toml` pins Mathlib to the
exact Git revision above.

## Build from a clean checkout

Install Git, Elan, `ripgrep`, and GNU `sha256sum`, then run:

```bash
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
scripts/fetch_mathlib_cache.sh
scripts/check_all.sh
```

The environment variable prevents Mathlib's update hook from fetching its
entire cache. The next command fetches only the transitive Mathlib closure of
the Mathlib modules imported by this project.

## Verification checks

- `AllResults.lean` imports all 41 supplied modules and every additive phase
  module explicitly.
- `checks/source-manifest.sha256` proves the project copies are byte-for-byte
  identical to the supplied ZIP entries.
- `scripts/check_no_placeholders.sh` rejects proof placeholders in Lean source.
- `AxiomAudit.lean` runs `#print axioms` for every declaration in
  `checks/master-facing-theorems.tsv`.
- `scripts/check_axioms.sh` records the axiom report and rejects `sorryAx`.
- `scripts/check_displacement_interfaces.sh` rejects a residual
  `Wasserstein2LawMeasurable` premise in any canonical downstream displacement result.
- `scripts/check_taxonomy_process_interfaces.sh` rejects repeated monotonicity, absorbing-coverage,
  or fixedness premises in canonical class-facing results.
- `scripts/check_phase3_interfaces.sh` checks the closed witness, two-verdict, and final
  impossibility interfaces and rejects a leaked coupling-lift or constraint-family premise.
- `scripts/check_phase4_interfaces.sh` checks the exact `threeway`, `oraclestrict`, and
  `oraclehilbert` wrappers and rejects leaked branch-finiteness, branch-`L²`, finite-branch, or
  kernel-constructor premises.
- `scripts/check_phase6_interfaces.sh` checks the repaired same-estimand
  impossibility boundary.
- `scripts/check_loss_interfaces.sh` checks that the exact increasing-loss
  wrappers do not require global measurability of `g`.
- `scripts/check_flagspace_interfaces.sh` checks that exact flag-space
  Wasserstein equality does not expose `CouplingsLift`.
- `scripts/check_manuscript_alignment.sh` checks that every label in the aligned manuscript has
  exactly one index row and that every indexed Lean declaration compiles.
- `scripts/check_all.sh` runs integrity, placeholder, full-build, and axiom
  checks in one command.

See `docs/PHASE0_BASELINE.md`, `docs/PHASE1_DISPLACEMENT_CHAIN.md`,
`docs/PHASE2_OBSERVED_PROCESS.md`, `docs/PHASE3_IMPOSSIBILITY.md`,
`docs/PHASE4_ABSORPTION_ORACLE.md`, `docs/PHASE5_FINAL_AUDIT.md`,
`docs/PHASE6_SAME_ESTIMAND_REPAIR.md`, and
`docs/PHASE7_LOSS_MEASURABILITY.md`, and
`docs/PHASE8_FLAG_WASSERSTEIN.md` for the recorded phase boundaries and final
manuscript differences.
