# Source provenance

Prepared: 10 September 2026. Package version: `0.1.0-alpha.1`.

## Supplied snapshot

- Commit: `0a25e7a431a4238b608916e51107e70b8fd36502`.
- Tag: `phase8-known-good`.
- Source archive: `SequentialLearning_Phase8_Source.zip`.
- Source archive SHA-256:
  `4c4011bf40bd5a4c5e5c9dc4e516dc4c1b40122ce51e0657fa90562328358552`.
- Supplied Git bundle SHA-256:
  `1da843ce9e8ba52e165854c20b7003e19ddbe1c143b3f3ca39298c11159dada6`.

This commit identifies the supplied development snapshot. A packaging commit
in a new repository will have its own identifier. Original Git history and
dependency source are not included in the portable release tree.

## Preservation

All 66 Lean files (57 library modules and nine top-level entry points), all
original verification scripts, `lean-toolchain`, `lakefile.toml`,
`lake-manifest.json`, and the manuscript are retained byte-for-byte. Shell
scripts are marked executable. The original README is preserved in
[history/PHASE8_README.md](history/PHASE8_README.md).

`checks/early-release-source.sha256` records all Lean files, the dependency
configuration, and manuscript. From the repository root:

```bash
sha256sum --check checks/early-release-source.sha256
```

This is an archival snapshot manifest. Future mathematical revisions should
record their own manifest and version. The original 41-module baseline
manifest remains in `checks/source-manifest.sha256`.

The Lake package's existing version `0.1.0` is preserved with its configuration.
`VERSION`, `CITATION.cff`, and the proposed tag identify this packaged
pre-release as `0.1.0-alpha.1`.

## Verification boundary

The [supplied record](history/PHASE8_VERIFICATION.md) reports a successful full
build, 90 axiom checks, and a clean-checkout reproduction. Packaging checked
source identity, baseline hashes, proof placeholders, shell syntax, metadata,
documentation links, and archive contents. Lean and Lake were unavailable;
the compiler and new GitHub workflow were not executed here.

[Current status](STATUS.md) records the known correspondence gaps and
supersedes stronger alignment claims in historical records.
