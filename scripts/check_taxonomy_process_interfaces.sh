#!/usr/bin/env bash
set -euo pipefail

project_root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$project_root"

output="$(lake env lean TaxonomyProcessInterfaceAudit.lean 2>&1)"
printf '%s\n' "$output"

for required in RealizedObservedProcess HasClass; do
  if ! printf '%s\n' "$output" | rg --fixed-strings "$required" >/dev/null; then
    echo "Canonical taxonomy/process interfaces do not expose $required." >&2
    exit 1
  fi
done

for forbidden in 'K.IsMonotone' AbsorbingCoverage 'c.IsAbsorbing' hStep hFixed; do
  if printf '%s\n' "$output" | rg --fixed-strings "$forbidden" >/dev/null; then
    echo "A canonical taxonomy/process result repeats derived premise: $forbidden" >&2
    exit 1
  fi
done

echo "Canonical taxonomy/process interfaces derive class properties internally."
