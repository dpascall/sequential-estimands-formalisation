#!/usr/bin/env bash
set -euo pipefail

project_root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$project_root"

if rg --line-number --glob '*.lean' '(^|[^[:alnum:]_])(sorry|admit)([^[:alnum:]_]|$)' \
    SequentialLearning ./*.lean; then
  echo "Proof placeholder detected." >&2
  exit 1
fi

echo "No proof placeholders detected."
