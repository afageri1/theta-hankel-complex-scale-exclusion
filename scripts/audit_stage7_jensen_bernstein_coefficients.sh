#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-bernstein-coefficients-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenBernsteinCoefficients
lake env lean HodgeProofHP/Stage7ThetaJensenBernsteinCoefficients.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaJensenCubicWeight_bernstein_expansion \
  --expect HodgeProofHP.hpThetaJensenCubicWeight_bernstein_cell \
  --expect HodgeProofHP.hpThetaJensenCubicWeight_bounds_of_coefficients
