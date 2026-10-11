#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-cubic-algebra-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenCubicAlgebra
lake env lean HodgeProofHP/Stage7ThetaJensenCubicAlgebra.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaJensenGamma_three \
  --expect HodgeProofHP.hpThetaJensenPolynomial_three \
  --expect HodgeProofHP.hpThetaJensenCubic_toPoly \
  --expect HodgeProofHP.hpThetaJensenCubic_eval \
  --expect HodgeProofHP.hpThetaJensenCubic_eval_moments \
  --expect HodgeProofHP.hpThetaJensenCubic_discr_moments
