#!/usr/bin/env bash
set -euo pipefail

project_root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$project_root"

work_dir="$(mktemp -d)"
trap 'rm -r "$work_dir"' EXIT

tail -n +2 checks/master-facing-theorems.tsv | cut -f2 | sort -u \
  > "$work_dir/master-facing.txt"
sed -n 's/^#print axioms //p' AxiomAudit.lean | sort -u \
  > "$work_dir/axiom-audit.txt"

if ! diff -u "$work_dir/master-facing.txt" "$work_dir/axiom-audit.txt"; then
  echo "AxiomAudit.lean and the master-facing declaration inventory differ." >&2
  exit 1
fi

lake env lean AxiomAudit.lean 2>&1 | tee checks/axioms.log

if rg --line-number 'sorryAx' checks/axioms.log; then
  echo "Unsound proof axiom detected." >&2
  exit 1
fi

echo "Axiom audit covered every master-facing declaration without an unsound proof axiom."
