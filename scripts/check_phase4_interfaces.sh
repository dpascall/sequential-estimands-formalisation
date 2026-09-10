#!/usr/bin/env bash
set -euo pipefail

project_root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$project_root"

output="$(lake env lean Phase4InterfaceAudit.lean 2>&1)"
printf '%s\n' "$output"

for required in threeway oraclestrict oraclehilbert AbsorptionOracleRCDs \
    absorptionEvent pInfinity; do
  if ! printf '%s\n' "$output" | rg --fixed-strings "$required" >/dev/null; then
    echo "Phase 4 interface audit did not expose $required." >&2
    exit 1
  fi
done

for forbidden in hFiniteRisk hBranchL2 MemLp binaryOracleKernel \
    binaryEventMixtureKernel Fintype Finite; do
  if printf '%s\n' "$output" | rg --fixed-strings "$forbidden" >/dev/null; then
    echo "A Phase 4 endpoint leaks an implementation premise: $forbidden" >&2
    exit 1
  fi
done

echo "Absorption-oracle interfaces expose only the stated RCD boundary."
