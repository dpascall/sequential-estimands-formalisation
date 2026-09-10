#!/usr/bin/env bash
set -euo pipefail

project_root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$project_root"

output="$(lake env lean Phase3InterfaceAudit.lean 2>&1)"
printf '%s\n' "$output"

for required in card_latentState both_verdicts witnesses classEventsMeasurable \
    admissible_flag_process bothverdicts impossibility HasClass; do
  if ! printf '%s\n' "$output" | rg --fixed-strings "$required" >/dev/null; then
    echo "Phase 3 interface audit did not expose $required." >&2
    exit 1
  fi
done

for forbidden in CouplingsLift ValidConstraintFamily StructuralConstraint sorryAx; do
  if printf '%s\n' "$output" | rg --fixed-strings "$forbidden" >/dev/null; then
    echo "A Phase 3 endpoint leaks implementation premise: $forbidden" >&2
    exit 1
  fi
done

echo "Phase 3 witness and impossibility interfaces are closed."
