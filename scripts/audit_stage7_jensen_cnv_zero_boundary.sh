#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-cnv-zero-boundary-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenCNVZeroBoundary
lake env lean HodgeProofHP/Stage7ThetaJensenCNVZeroBoundary.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaCNV_logProfile_first_reflection \
  --expect HodgeProofHP.hpThetaCNV_logProfile_second_reflection \
  --expect HodgeProofHP.hpThetaPhi_reflection \
  --expect HodgeProofHP.hpThetaPhi_deriv_zero \
  --expect HodgeProofHP.hpThetaPhiCNVTailExpression_zero
echo "PASS: kernel reflection, kernel derivative at zero and CNV zero boundary; CNV positivity remains unproved"
