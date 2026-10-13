#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-cnv-kernel-second-zero-lower-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenCNVKernelSecondZeroLower
lake env lean HodgeProofHP/Stage7ThetaJensenCNVKernelSecondZeroLower.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaCNV_exp_neg_pi_upper \
  --expect HodgeProofHP.hpThetaCNV_secondDerivativeFactor_nonneg \
  --expect HodgeProofHP.hpThetaCNV_secondDerivative_firstTerm_ge_neg35 \
  --expect HodgeProofHP.hpThetaCNV_secondDerivative_tailTerm_nonneg \
  --expect HodgeProofHP.hpThetaPhi_secondDeriv_zero_ge_neg35
echo "PASS: actual second kernel derivative at zero bounded below by -35; weighted tail upper certificate and full endpoint positivity remain unproved"
