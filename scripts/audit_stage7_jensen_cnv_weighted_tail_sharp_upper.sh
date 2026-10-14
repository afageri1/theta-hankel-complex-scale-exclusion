#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-cnv-weighted-tail-sharp-upper-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenCNVWeightedTailSharpUpper
lake env lean HodgeProofHP/Stage7ThetaJensenCNVWeightedTailSharpUpper.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaCNV_weightedTailRectangle_upper_sharp \
  --expect HodgeProofHP.hpThetaCNV_weightedTailFiniteIntegral_upper_sharp \
  --expect HodgeProofHP.hpThetaPhiWeightedTail_zero_le_eightySeven_thousandths \
  --expect HodgeProofHP.hpThetaPhiWeightedTail_le_at_zero \
  --expect HodgeProofHP.hpThetaPhiWeightedTail_le_eightySeven_thousandths \
  --expect HodgeProofHP.hpThetaPhiWeightedTail_bounds_eightySeven_thousandths
echo "PASS: actual weighted tail between 0 and 0.087 at every nonnegative argument"
echo "Uniform kernel bounds and CNV positivity on [0, 1/50] remain unproved"
