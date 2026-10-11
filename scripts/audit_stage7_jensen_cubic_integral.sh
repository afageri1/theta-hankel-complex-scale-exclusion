#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-cubic-integral-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenCubicIntegral
lake env lean HodgeProofHP/Stage7ThetaJensenCubicIntegral.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaJensenCubicWeight_mul_kernel \
  --expect HodgeProofHP.hpThetaJensenCubicWeight_integrableOn \
  --expect HodgeProofHP.hpThetaJensenCubic_eval_eq_integral \
  --expect HodgeProofHP.hpThetaJensenCubic_eval_eq_finite_add_tail
