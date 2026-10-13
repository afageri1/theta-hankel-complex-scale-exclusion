#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
lake build HodgeProofHP.Stage7ThetaJensenCNVWeightedTailCertifiedBounds
LOG=stage7-jensen-cnv-weighted-tail-rectangles-axioms.log
lake env lean HodgeProofHP/Stage7ThetaJensenCNVWeightedTailRectangles.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaJensen_weighted_tailRectangleBatch_bounds \
  --expect HodgeProofHP.hpThetaJensen_weighted_tailRectangle_lower_numeric \
  --expect HodgeProofHP.hpThetaJensen_weighted_tailRectangle_upper_numeric
LOG=stage7-jensen-cnv-weighted-tail-certified-axioms.log
lake env lean HodgeProofHP/Stage7ThetaJensenCNVWeightedTailCertifiedBounds.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaJensen_weighted_tailBatchIntegral_of_kernelBounds \
  --expect HodgeProofHP.hpThetaJensen_weighted_tailBatchIntegral_bounds \
  --expect HodgeProofHP.hpThetaJensen_weighted_tailFiniteIntegral_bounds \
  --expect HodgeProofHP.hpThetaCNV_weightedTail_at_one_le_twoEminusEight \
  --expect HodgeProofHP.hpThetaCNV_weightedTail_zero_split \
  --expect HodgeProofHP.hpThetaPhiWeightedTail_zero_le_nine_hundredths \
  --expect HodgeProofHP.hpThetaPhiCNVTailFirstDerivative_zero_gt_certified \
  --expect HodgeProofHP.hpThetaPhiCNVTailFirstDerivative_zero_pos
echo "PASS: weighted tail at zero at most 0.09 and CNV right derivative at zero greater than 0.0184; global CNV positivity remains unproved"
