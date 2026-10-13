#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-weighted-tail-positive-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenWeightedTailPositive
lake env lean HodgeProofHP/Stage7ThetaJensenWeightedTailPositive.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaPhiWeightedTail_pos \
  --expect HodgeProofHP.hpThetaPhiWeightedTail_ne_zero \
  --expect HodgeProofHP.hpThetaPhiWeightedTail_log_hasDerivAt \
  --expect HodgeProofHP.hpThetaPhiWeightedTail_log_deriv
echo "PASS: positive weighted tail and logarithmic derivative; CNV concavity remains unproved"
