#!/usr/bin/env bash
set -euo pipefail

project_root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$project_root"

output="$(lake env lean FlagSpaceInterfaceAudit.lean 2>&1)"
printf '%s\n' "$output"

for required in liftCoupling_map_values transportL2Cost_liftCoupling \
    wasserstein2_eq_project TransportCoupling; do
  if ! printf '%s\n' "$output" | rg --fixed-strings "$required" >/dev/null; then
    echo "Flag-space interface audit did not expose $required." >&2
    exit 1
  fi
done

if printf '%s\n' "$output" | rg --fixed-strings 'CouplingsLift' >/dev/null; then
  echo "The exact flag-space Wasserstein equality again exposes CouplingsLift." >&2
  exit 1
fi

echo "Boolean flag-space Wasserstein equality is unconditional."
