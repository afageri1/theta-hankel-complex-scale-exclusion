#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-square-variable-tail-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenSquareVariableTail
lake env lean HodgeProofHP/Stage7ThetaJensenSquareVariableTail.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaPhiSquareTail_pos \
  --expect HodgeProofHP.hpThetaPhiSquareTail_hasDerivAt \
  --expect HodgeProofHP.hpThetaPhiSquareTail_deriv \
  --expect HodgeProofHP.hpThetaPhiSquareTail_log_hasDerivAt \
  --expect HodgeProofHP.hpThetaPhiSquareTail_log_deriv
echo "PASS: positive square-variable tail and first derivatives; CNV concavity remains unproved"
