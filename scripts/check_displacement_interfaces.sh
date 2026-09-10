#!/usr/bin/env bash
set -euo pipefail

project_root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$project_root"

output="$(lake env lean DisplacementInterfaceAudit.lean 2>&1)"
printf '%s\n' "$output"

if printf '%s\n' "$output" | rg --fixed-strings 'Wasserstein2LawMeasurable'; then
  echo "A canonical displacement result still exposes a Wasserstein measurability premise." >&2
  exit 1
fi

echo "Canonical displacement interfaces contain no auxiliary Wasserstein measurability premise."
