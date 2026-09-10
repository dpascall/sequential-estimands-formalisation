#!/usr/bin/env bash
set -euo pipefail

project_root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$project_root"

mapfile -t roots < checks/mathlib-cache-roots.txt
lake exe cache get "${roots[@]}"
