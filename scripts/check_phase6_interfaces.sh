#!/usr/bin/env bash
set -euo pipefail

project_root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$project_root"

output="$(lake env lean Phase6InterfaceAudit.lean 2>&1)"
printf '%s\n' "$output"

for required in HasClass IsRegularConditionalLaw posteriorFrechetVarianceReal \
    frechetInformationGain frechetEstimandMovement bothverdicts impossibility; do
  if ! printf '%s\n' "$output" | rg --fixed-strings "$required" >/dev/null; then
    echo "Same-estimand interface audit did not expose $required." >&2
    exit 1
  fi
done

for forbidden in CouplingsLift ValidConstraintFamily StructuralConstraint \
    branchFinite branchL2 sorryAx; do
  if printf '%s\n' "$output" | rg --fixed-strings "$forbidden" >/dev/null; then
    echo "The same-estimand endpoint leaks implementation premise: $forbidden" >&2
    exit 1
  fi
done

echo "Same-estimand impossibility interfaces are closed."
