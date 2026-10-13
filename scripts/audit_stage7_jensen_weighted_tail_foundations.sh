#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-weighted-tail-foundations-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenWeightedTailFoundations
lake env lean HodgeProofHP/Stage7ThetaJensenWeightedTailFoundations.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaPhi_weightedIntegrand_continuous \
  --expect HodgeProofHP.hpThetaPhi_weighted_integrableOn_positive \
  --expect HodgeProofHP.hpThetaPhi_weightedTail_integrableOn \
  --expect HodgeProofHP.hpThetaPhiWeightedTail_nonneg
echo "PASS: weighted tail foundations; CNV positivity remains unproved"
