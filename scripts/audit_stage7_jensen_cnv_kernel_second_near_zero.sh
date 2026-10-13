#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-cnv-kernel-second-near-zero-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenCNVKernelSecondNearZero
lake env lean HodgeProofHP/Stage7ThetaJensenCNVKernelSecondNearZero.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaCNV_exp_twoMicro_upper \
  --expect HodgeProofHP.hpThetaCNV_exp_halfMicro_upper \
  --expect HodgeProofHP.hpThetaCNV_firstParameter_nearZero_bounds \
  --expect HodgeProofHP.hpThetaCNV_secondDerivative_firstTerm_nearZero_ge_neg35 \
  --expect HodgeProofHP.hpThetaCNV_secondDerivative_tailTerm_nonneg_nonnegative \
  --expect HodgeProofHP.hpThetaPhi_secondDeriv_ge_neg35_nearZero
echo "PASS: actual second kernel derivative at least -35 on [0, 0.000001]; explicit CNV positivity radius remains unproved"
