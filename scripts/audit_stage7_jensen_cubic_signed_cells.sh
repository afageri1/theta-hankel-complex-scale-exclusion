#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-cubic-signed-cells-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenCubicSignedCellBounds
lake env lean HodgeProofHP/Stage7ThetaJensenCubicSignedCellBounds.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaJensen_signedProduct_bounds \
  --expect HodgeProofHP.hpThetaJensenCubic_signedCellIntegral_bounds
