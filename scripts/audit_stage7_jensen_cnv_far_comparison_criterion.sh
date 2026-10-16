#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

LOG=stage7-jensen-cnv-far-comparison-criterion-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenCNVFarComparisonCriterion
lake env lean HodgeProofHP/Stage7ThetaJensenCNVFarComparisonCriterion.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaCNV_far_firstTerm_eq \
  --expect HodgeProofHP.hpThetaCNV_far_abs_deriv_le_envelope \
  --expect HodgeProofHP.hpThetaCNV_farComparisonMargin_lower \
  --expect HodgeProofHP.hpThetaCNV_farComparisonNumerator_eq \
  --expect HodgeProofHP.hpThetaCNV_farComparisonMargin_pos_iff \
  --expect HodgeProofHP.hpThetaPhiCNVTailExpression_pos_of_far_margin \
  --expect HodgeProofHP.hpThetaCNV_far_weightedTail_comparison_of_numerator \
  --expect HodgeProofHP.hpThetaPhiCNVTailPositive_of_far_numerator
echo "PASS: actual CNV expression bounded below by an explicit scalar far-field margin"
echo "PASS: positive denominator cleared and near/far conditional gluing established"
echo "Positivity of the scalar numerator on the far half-line remains unproved"
