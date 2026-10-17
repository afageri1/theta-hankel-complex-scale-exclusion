#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

LOG=stage7-jensen-cnv-gamma-normalization-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenCNVGammaNormalization
lake env lean HodgeProofHP/Stage7ThetaJensenCNVGammaNormalization.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaCNV_halfGamma_factorial_balance \
  --expect HodgeProofHP.hpThetaCNV_halfGamma_factorial_ratio \
  --expect HodgeProofHP.hpThetaCNVHalfMoment_eq_evenMoment \
  --expect HodgeProofHP.hpThetaCNVHalfMoment_pos \
  --expect HodgeProofHP.hpThetaCNVNormalizedHalfMoment_pos \
  --expect HodgeProofHP.hpThetaJensenGamma_succ_eq_normalizedHalfMoment \
  --expect HodgeProofHP.hpThetaJensen_shiftedTuranGap_eq_normalizedHalfMomentGap \
  --expect HodgeProofHP.hpThetaJensen_shiftedStrictTuran_iff_normalizedHalfMoments
echo "PASS: positive actual half moments and their exact Gamma normalization"
echo "PASS: shifted Turan gap equals a positive geometric factor times the normalized moment gap"
echo "Normalized moment log concavity, general Turan inequalities and unbounded good degrees remain unproved"
