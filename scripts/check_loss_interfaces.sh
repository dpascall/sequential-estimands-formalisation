#!/usr/bin/env bash
set -euo pipefail

project_root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$project_root"

output="$(lake env lean LossInterfaceAudit.lean 2>&1)"
printf '%s\n' "$output"

for required in MonotoneOn Integrable Supermartingale \
    conditional_increasing_loss_order_nonnegative \
    conditional_increasing_loss_supermartingale_nonnegative \
    monotoneClass_conditional_increasing_loss_supermartingale; do
  if ! printf '%s\n' "$output" | rg --fixed-strings "$required" >/dev/null; then
    echo "Increasing-loss interface audit did not expose $required." >&2
    exit 1
  fi
done

if printf '%s\n' "$output" | rg --fixed-strings 'hgMeas' >/dev/null; then
  echo "The increasing-loss boundary again requires global measurability of g." >&2
  exit 1
fi

echo "Increasing-loss interfaces require no global measurability premise on g."
