#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-bernstein-bounds-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenBernsteinBounds
lake env lean HodgeProofHP/Stage7ThetaJensenBernsteinBounds.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaBernstein_coefficient_bounds \
  --expect HodgeProofHP.hpThetaBernsteinValue_bounds \
  --expect HodgeProofHP.hpThetaJensenCubicWeight_bounds_of_bernstein
