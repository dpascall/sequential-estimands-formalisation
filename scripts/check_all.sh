#!/usr/bin/env bash
set -euo pipefail

project_root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$project_root"

scripts/check_source_integrity.sh
scripts/check_no_placeholders.sh
lake build
scripts/check_axioms.sh
scripts/check_displacement_interfaces.sh
scripts/check_taxonomy_process_interfaces.sh
scripts/check_phase3_interfaces.sh
scripts/check_phase4_interfaces.sh
scripts/check_phase6_interfaces.sh
scripts/check_loss_interfaces.sh
scripts/check_flagspace_interfaces.sh
scripts/check_manuscript_alignment.sh
